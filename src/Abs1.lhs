\section{Abstraction, Level One}\label{sec:lhs:Abs1}

\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at smcgen root
\end{verbatim}
\begin{code}
module Abs1 ( abs1 ) where
import Data.List
import Data.Maybe

import DSL1

import Debug.Trace
dbg msg x = trace (msg ++ show x) x
\end{code}

We now take a fresh look at the initial \texttt{Flash.prism} example,
but focus instead on structure,
including declarations, control-flow, and formul\ae.

Here we will present excerpts out-of-order, as we focus on specific aspects.
For now, definitions of abstract syntax, useful (Haskell) constants,
and the encoding of the Flash model are all interleaved.

Eventually these will all be factored out into their own sections.

\subsection{Top Level}

\begin{code}
abs1 mName fModel b
  = do let code1 = prism1code fModel fixedpars
       putStrLn code1
       let cflash = x2sPrism fixedpars fModel
       let ccode = prism1code cflash fixedpars
       putStrLn ccode
       let fName = "models/gen/"++mName++showpars++".prism"
       writeFile fName ccode
       putStrLn ("Prism written to "++fName)
  where
    fixedpars = [("b",b)]
    showpars = concat $ map showpar fixedpars
    showpar (s,i) = '_':s ++ '_':show i
\end{code}
