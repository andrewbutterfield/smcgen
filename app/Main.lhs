\section{Main Program}\label{sec:lhs:Main}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at smcgen root
\end{verbatim}
\begin{code}
module Main where
import Hack
import Abs1

main :: IO ()
main = abs1 prism1 [("b",3)]
\end{code}
