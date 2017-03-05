{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
import Data.Maybe
import Control.Monad.State
import Data.List

{- Nondeterministic matching -}

class Eq s => Nondeterministic s a | s -> a where
	-- s is state, a is symbol
  stepN :: s -> a -> [s]
  epsN :: s -> [s]
  acceptN :: s -> Bool

matchN :: Nondeterministic s a => s -> [a] -> Bool
matchN st s = any acceptN $ foldl (epsStep . step) [st] s where
	-- step along symbol from each state of sts
  step sts c = [next | st <- sts, next <- stepN st c]
  -- transitive closure along eps edges
  epsStep sts = let stepped = nub $ sts ++ [next | st <- sts, next <- epsN st]
    in if sts == stepped then sts else epsStep stepped


{- Deterministic matching -}

class Deterministic s a | s -> a where
	-- s is state, a is symbol
  stepD :: s -> a -> s
  acceptD :: s -> Bool

matchD :: Deterministic s a => s -> [a] -> Bool
matchD st s = acceptD $ foldl stepD st s

{- NFA -}

data NFA s a = NFA s {-current-} [s] {-final-} [((s, a), s)] {-transitions-} [(s, s)] {-epsilon transitions-}
  deriving (Show, Eq)

instance (Eq a, Eq s) => Nondeterministic (NFA s a) a where
	epsN (NFA st final trans eps) = [NFA next final trans eps | next <- lookupAll st eps]
	stepN (NFA st final trans eps) c = [NFA next final trans eps | next <- lookupAll (st, c) trans]
	acceptN (NFA st final _ _) = st `elem` final

{- DFA -}

data DFA s a = DFA s {-current-} [s] {-final-} [((s, a), s)] {-transitions-}
  deriving (Show, Eq)

instance (Eq a, Eq s) => Deterministic (DFA s a) a where
	stepD (DFA st final trans) c = case lookup (st, c) trans of
		Just next -> DFA next final trans
		Nothing {-dead state-} -> DFA st [] [] {-no more transitions or acceptance-}
	acceptD (DFA st final _) = st `elem` final

asNFA :: (DFA s a) -> (NFA s a)
asNFA (DFA st final trans) = NFA st final trans []

{- complementDFA -}
complementDFA :: DFA s a -> DFA s' a
complementDFA = undefined

{- deteminize -}
deteminize :: Nondeterministic s a => s -> DFA s a
deteminize = undefined

{- Pattern -}
data Pattern a = PEmpty | PSym a | PSeq (Pattern a) (Pattern a) | PAlt (Pattern a) (Pattern a) | PStar (Pattern a)

anySymbolPattern = foldr PAlt PEmpty . map PSym
literalPattern = sequencePattern . map PSym
sequencePattern = foldr PSeq PEmpty

class SafeSymbol a where
	escape :: a -> String
	escapeClass :: a -> String

instance SafeSymbol Char where
	escape c | c `elem` "[()*" = '\\':[c]
	escape c = [c]
	escapeClass c | c == ']' = '\\':[c]
	escapeClass c = [c]

instance SafeSymbol a => Show (Pattern a) where
	show PEmpty = ""
	show (PSym c) = escape c
	show (PSeq a b) = (show a) ++ (show b)
	show (PStar s@(PSym _)) = (show s) ++ "*"
	show (PStar a) = "(" ++ (show a) ++ ")*"
	show p@(PAlt _ _) = case classifySyms [] [] $ flatten p of
		  ([], []) -> ""
		  (syms, []) -> formatClass syms
		  ([], exprs) -> "(" ++ (formatExprs exprs) ++ ")"
		  (syms, exprs) -> "(" ++ (formatClass syms) ++ "|" ++ (formatExprs exprs) ++ ")"
		where
			flatten (PAlt a b) = (flatten a) ++ (flatten b)
			flatten a = [a]
			classifySyms syms exprs (s@(PSym _):rest) = classifySyms (syms++[s]) exprs rest
			classifySyms syms exprs (e:rest) = classifySyms syms (exprs++[e]) rest
			classifySyms syms exprs [] = (syms, exprs)
			formatClass syms = "[" ++ concat [escapeClass s | PSym s <- syms] ++ "]"
			formatExprs exprs = concat $ intersperse "|" (map show exprs)

{- Pattern conversions -}

patternToNFA :: Pattern a -> NFA Int a
patternToNFA a = NFA 0 [end] (filterSym trans) (filterEps trans) where
	((end, trans), _) = runState (convert 0 a) 0
	filterEps trs = [(l, r) | (l, label, r) <- trs, isNothing label]
	filterSym trs = [((l, sym), r) | (l, label, r) <- trs, isJust label, let sym = fromJust label]
	{- https://en.wikipedia.org/wiki/Thompson's_construction -}
	convert :: Int -> Pattern a -> State Int (Int, [(Int, Maybe a, Int)])
	convert left PEmpty = do
		right <- newState
		return (right, [(left, Nothing, right)])
	convert left (PSym a) = do
		right <- newState
		return (right, [(left, Just a, right)])
	convert left (PSeq a b) = do
		(middle, ltrans) <- convert left a
		(right, rtrans) <- convert middle b
		return (right, ltrans ++ rtrans)
	convert left (PAlt a b) = do
		[up, down, right] <- sequence [newState, newState, newState]
		(top, ttrans) <- convert up a
		(bottom, btrans) <- convert down b
		return (right, ttrans ++ btrans ++ [
			(left, Nothing, up), (left, Nothing, down), 
			(top, Nothing, right), (bottom, Nothing, right)])
	convert left (PStar a) = do
		[internal, right] <- sequence [newState, newState]
		(exit, trans) <- convert internal a
		return (right, trans ++ [
			(left, Nothing, internal), (left, Nothing, right), 
			(exit, Nothing, internal), (exit, Nothing, right)])
	newState = modify (+1) >> get

buildPattern :: (NFA s a) -> Pattern a
buildPattern = undefined

{- utilities -}
lookupAll :: Eq a => a -> [(a, b)] -> [b]
lookupAll a = (map snd) . filter ((==a) . fst)




--let p= literalPattern "abcd" `PSeq` (literalPattern "de" `PAlt` PStar (literalPattern "xy")); n = patternToNFA p in matchN n "abcdd"