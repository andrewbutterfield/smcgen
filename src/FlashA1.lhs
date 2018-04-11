\section{Flash Model, Level One}\label{sec:lhs:FlashA1}

\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at smcgen root
\end{verbatim}
\begin{code}
module FlashA1 ( flashA1 ) where
import Data.List
import Data.Maybe

import DSL1
\end{code}

\def\Flash{\texttt{Flash.prism}}

\subsection{Declarations from \Flash}

\paragraph{Constants} from \Flash:
\begin{prism}
const int b;
const int p;
const int c;
const int w;
const int MAXDIFF;
const int INIT = 1;
const int WRITE = 2;
const int SELECT = 3;
const int FINISH = 4;
\end{prism}
\begin{code}
cdecl
  = [ Parameter "b" IntT
    , Parameter "p" IntT
    , Parameter "c" IntT
    , Parameter "w" IntT
    , Parameter "MAXDIFF" IntT
    , Constant "INIT" IntT _1
    , Constant "WRITE" IntT _2
    , Constant "SELECT" IntT _3
    , Constant "FINISH" IntT _4
    ]
 -- as (atomic) expressions
b = N "b"
p = N "p"
c = N "c"
w = N "w"
_MAXDIFF = N "MAXDIFF"
_INIT    = N "INIT"
_WRITE   = N "WRITE"
_SELECT  = N "SELECT"
_FINISH  = N "FINISH"
\end{code}

\newpage
\paragraph{Variables} from \Flash, using array declarations
\begin{prism}
fm_clean: array [1..b] of [0..p];
fm_erase: array [1..b] of [0..w];
pc: [INIT..FINISH] init INIT;
i: [0..c] init 0;
\end{prism}
\begin{code}
_0 = I 0
one2b = (_1,b) -- rngT _1 b
vdecl
  = [ Var "fm_clean" $ arrT _1 b $ rngT _0 p
    , Var "fm_erase" $ arrT _1 b $ rngT _0 w
    , VInit "pc" (rngT _INIT _FINISH) _INIT
    , VInit "i" (rngT _0 c) _0
    ]
 -- as most commonly used expressions
fm_clean[x] = AI (N "fm_clean") x ; fm_clean'[x] e = UA "fm_clean" x e
fm_erase[x] = AI (N "fm_erase") x ; fm_erase'[x] e = UA "fm_erase" x e
pc       = N "pc"       ; pc' e     = U "pc" e
i        = N "i"        ; i'  e     = U "i"  e
\end{code}

\newpage
\subsection{Formul\ae\ from \Flash}


Rewritten ``our style'':
\begin{prism}
formula writeable = for x:[1..b] apply + over (fm_clean[x]!=0 ? 1 : 0);
\end{prism}
\begin{code}
x = N "x" ; y = N "y"
_writeable
  = Formula "writeable"
            $ AF [("x",(_1,b))]
                 "+"
                 true
                 (fm_clean[x] .!= _0 .? _1 .: _0)
writeable = N "writeable"
\end{code}

\begin{prism}
formula dirty(x:[1..b]) = p-fm_clean[x];
\end{prism}
\begin{code}
_dirty = PFormula "dirty" [("x",one2b)] true (p .- fm_clean[x])
dirty e = F "dirty" [e]
\end{code}

\begin{prism}
formula cand(x,y:[1..b]) = x!=y -> dirty(x)>0 & fm_clean[y] >= dirty(x);
\end{prism}
\begin{code}
_cand
  = PFormula "cand" [("x",one2b),("y",one2b)]
             (x .!= y)
             ( dirty(x) .> _0 .& fm_clean[y] .>= dirty(x) )
cand (e, f) = F "cand" [e,f]
\end{code}

\begin{prism}
formula candidates = for x,y:[1..b] apply + over x!=y -> cand(x,y)?1:0);
\end{prism}
\begin{code}
_candidates
  = Formula "candidates"
            $ AF [("x",one2b),("y",one2b)]
                 "+"
                 ( x .!= y )
                 ( cand (x, y) .? _1 .: _0 )
candidates = N "candidates"
\end{code}

\begin{prism}
formula can_erase = for x:[1..b] apply & over fm_erase[x]<w ;
\end{prism}
\begin{code}
_can_erase
  = Formula "can_erase"
            $ AF [("x",one2b)]
                 "&"
                 true
                 ( fm_erase[x] .< w)
can_erase = N "can_erase"
\end{code}

\newpage
\begin{prism}
formula diff(x,y:[1..b]) = x != y -> fm_erase(x)-fm_erase(y);
\end{prism}
\begin{code}
_diff
  = PFormula "diff" [("x",one2b),("y",one2b)]
             ( x .!= y ) ( fm_erase[x] .- fm_erase[y] )
diff (e,f) = F "diff" [e,f]
\end{code}

\begin{prism}
formula toobig = for x,y:[1..b] apply | over x!=y -> diff(x,y) >= MAXDIFF)
\end{prism}
\begin{code}
_toobig
  = Formula "toobig"
            $ AF [("x",one2b),("y",one2b)]
                 "|"
                 ( x .!= y )
                 ( diff(x, y) .>= _MAXDIFF )
toobig = N "toobig"
\end{code}

All formul\ae\ together:
\begin{code}
formulae = [_writeable,_dirty,_cand,_candidates,_can_erase,_diff,_toobig]
\end{code}

\newpage
\subsection{Flow of Control from \Flash}

Rewritten ``our style'':

\begin{prism}
[] pc=INIT ->
  ( for x:[1..b] apply & over (fm_clean'[x]=p) & (fm_erase'[x]=0) )
  & (pc'=WRITE);
\end{prism}
\begin{code}
cmd1
 = Cmd [] (pc .= _INIT)
       ( ( AF [("x",one2b)]
              "&"
              true
              ( fm_clean'[x] .:= p .& fm_erase'[x] .:= _0  ) )
         .& pc' .:= _WRITE )
\end{code}

\begin{prism}
[] pc=WRITE & i<c & writeable!=0 ->
  for x:[1..b] apply + over
    (fm_clean[x]>0?1/writeable:0): (fm_clean'[x]=fm_clean[x]-1) & (i'=i+1);
\end{prism}
\begin{code}
cmd2 = Cmd [] (pc .= _WRITE .& i .< c .& writeable .!= _0)
           ( AF [("x",one2b)]
                "+"
                true
                ( P (fm_clean[x] .> _0 .? _1./writeable .: _0)
                    ( fm_clean'[x] .:= fm_clean[x] .- _1
                      .& i' .:= (i .+ _1 ) ) ) )
\end{code}

\begin{prism}
[] pc=WRITE & i<c & writeable=0 -> (pc'=FINISH);
\end{prism}
\begin{code}
cmd3 = Cmd [] (pc .= _WRITE .& i .< c .& writeable .= _0) (pc' .:= _FINISH)
\end{code}

\begin{prism}
[] pc=WRITE & i=c -> (pc'=SELECT);
\end{prism}
\begin{code}
cmd4 = Cmd [] (pc .= _WRITE .& i .= c) (pc' .:= _SELECT)
\end{code}

\begin{prism}
[] pc=SELECT & (candidates=0 | !can_erase) -> (pc'=FINISH);
\end{prism}
\begin{code}
cmd5 = Cmd [] (pc .= _SELECT .& ( candidates .= _0 .| lnot can_erase ) )
              (pc' .:= _FINISH)
\end{code}

\newpage
\begin{prism}
[] pc=SELECT & candidates!=0 & can_erase ->
  for from,to:[1..b] apply + over
    from != to ->
     cand(from,to) ? 1/candidates : 0):
     (fm_clean[to]'=fm_clean[to]-dirty(from)) &
     (fm_clean[from]'=p) & (fm_erase[from]'=fm_erase[from]+1) &
     (i'=0) & (pc'=WRITE) ;
\end{prism}
\begin{code}
from = N "from" ; to = N "to"
cmd6 = Cmd [] (pc .= _SELECT .& candidates .!= _0 .& can_erase)
           ( AF [("from",one2b),("to",one2b)]
                "+"
                (from .!= to)
                ( P (  cand(from,to) .? _1./candidates .: _0)
                    ( fm_clean'[to] .:= fm_clean[to] .- dirty(from)
                      .& fm_clean'[from] .:= p
                      .& fm_erase'[from] .:= fm_erase[from] .+ _1
                      .& i' .:= _0 .& pc' .:= _WRITE ) ) )
\end{code}

\begin{prism}
[] pc=FINISH -> true;
\end{prism}
\begin{code}
true = B True
cmd7 = Cmd [] (pc .= _FINISH) true
\end{code}

Bringing all commands together:
\begin{code}
commands = [cmd1,cmd2,cmd3,cmd4,cmd5,cmd6,cmd7]
\end{code}

\subsubsection{The Big Picture}

\begin{code}
flashA1 = (DTMC, cdecl, [("Flash",vdecl,commands)], formulae)
\end{code}
