\section{Main Program}\label{sec:lhs:Main}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at smcgen root
\end{verbatim}
\begin{code}
module Main where
import Hack
import Abs1
import FlashA1

main :: IO ()
main = sequence_ $ map (abs1 "FlashA1" flashA1) [2..8]
\end{code}
