\section{Main Program}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at smcgen root
\end{verbatim}
\begin{code}
module Main where
import Hack

main :: IO ()
main = sequence_ $ map hack [2..8]
\end{code}
