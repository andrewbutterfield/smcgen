\section{Utilities}\label{sec:lhs:utils}

\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at smcgen root
\end{verbatim}
\begin{code}
module Utilities where
-- import Data.List
-- import Data.Maybe
\end{code}


\subsection{Association Lists}

Association list lookup:
\begin{code}
alookup :: (Eq a, Monad m) => [(a,b)] -> a -> m b
alookup [] _ = fail "not found"
alookup ((x,y):xys) z
 | z == x  =  return y
 | otherwise  = alookup xys z
\end{code}

When we are really sure the key \emph{is} in the assoc-list:
\begin{code}
aget :: (Eq a, Show a) => [(a,b)] -> a -> b
aget [] z = error ("aget: "++show z++" not found")
aget ((x,y):xys) z
 | z == x     =  y
 | otherwise  =  aget xys z
\end{code}

\subsection{List Products}

List Product --- all the ways to construct a list
by taking one element from each of the argument lists
\begin{code}
-- lprod :: [[a]] -> [[a]]
lprod [] = []
lprod [as] = map sngl as where sngl a = [a]
lprod (as:bss)  =  concat $ map (lprod' (lprod bss)) as

-- lprod' :: [[a]] -> a -> [[a]]
lprod' pss a  =  map (a:) pss
\end{code}
