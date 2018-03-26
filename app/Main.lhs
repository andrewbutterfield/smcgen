\section{Main Program}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at smcgen root
\end{verbatim}
\begin{code}
module Main where
import Hack
import Abs1

main :: IO ()
main = abs1 -- sequence_ $ map hack [2..8]
\end{code}
