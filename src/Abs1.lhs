\section{Abstraction, Level One}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at smcgen root
\end{verbatim}
\begin{code}
module Abs1 where
import Data.List
\end{code}

We now take a fresh look at the initial \texttt{Flash.prism} example,
but focus instead on structure,
including declarations, control-flow, and formul\ae.

Here we will present excerpts out-of-order, as we focus on specific aspects.

\newpage
\subsection{Expressions}

We need to support Prism expressions.
\begin{code}
data Expr
  = B Bool -- literal boolean
  | I Int    -- literal int
  | D Double -- literal double
  | C Ident  -- constant name
  | F String [Expr] -- generic function
  deriving (Eq,Show,Read)

isAtomic :: Expr -> Bool
isAtomic (B _)  =  True
isAtomic (I _)  =  True
isAtomic (D _)  =  True
isAtomic (C _)  =  True
isAtomic _      =  False
\end{code}

Supported infix forms of \texttt{F} from \cite{KNP11},
the most strongly binding first:
\begin{verbatim}
- (unary minus)
*, / (multiplication, division)
+, - (addition, subtraction)
<, <=, >=, > (relational operators)
=, != (equality operators)
! (negation)
& (conjunction)
| (disjunction)
<=> (if-and-only-if)
=> (implication)
? (condition evaluation: condition ? a : b means "if condition is true then a else b")
\end{verbatim}
For now, the ones in use in this example:
\begin{code}
infixl 7 ./  ;  e1 ./ e2   =  F "/"  [e1,e2]
infixl 7 .*  ;  e1 .* e2   =  F "*"  [e1,e2]
infixl 6 .+  ;  e1 .+ e2   =  F "+"  [e1,e2]
infixl 6 .-  ;  e1 .- e2   =  F "-"  [e1,e2]
infix  4 .=  ;  e1 .= e2   =  F "="  [e1,e2]
infix  4 .!= ;  e1 .!= e2  =  F "!=" [e1,e2]
infix  4 .<  ;  e1 .< e2   =  F "<"  [e1,e2]
infix  4 .>  ;  e1 .> e2   =  F ">"  [e1,e2]
infix  4 .>= ;  e1 .>= e2  =  F ">=" [e1,e2]
infix  3 .&  ;  e1 .&  e2  =  F "&"  [e1,e2]
infix  2 .|  ;  e1 .|  e2  =  F "|"  [e1,e2]
infix  1 <=> ;  e1 <=> e2  =  F "<=>"[e1,e2]
infix  0 .=> ;  e1 .=> e2  =  F "=>" [e1,e2]
-- faking e0 .? e1 .: e2 -->
infix  1 .:  ;  e1 .: e2   =         [e1,e2]
infix  0 .?  ;  e0 .? es   =  F "?:" (e0:es)
\end{code}

\newpage
\subsection{Declarations}

The following excerpt captures the range of state declarations we need to
handle:
\begin{prism}
const int b = 3
const int p
const int c
const int INIT = 1
const int FINISH = 4
fm_clean_2 : [0..p]
pc : [INIT..FINISH] init INIT
i : [0..c] init 0
\end{prism}
The first thing that we note is that the declaration of \texttt{fm\_clean\_2}
is one of several where what we want to declare is an array,
here in `pseudo-prism':
\begin{prism}
fm_clean : array [1..b] of [0..p]
\end{prism}


\subsubsection{Types}

What we have here are types whose contents depend
on the value of one or more constants (not variables).
We have the integer type, range types, and array types.
Prism also has boolean and double types, which we shall also include.
\begin{code}
type Ident = String -- identifiers
type Number = Expr -- Atomic (I, D or C only)
data Type
  = BoolT | IntT | DblT -- basic types
  | RngT Number Number -- range type, lowest to highest
  | ArrT Number Number Type -- array type
  deriving (Eq,Show,Read)
\end{code}
We note that \texttt{RngT} is a subtype of \texttt{IntT}.

\newpage
\subsubsection{Constants}

Constants can be declared with a known value,
or without.
The latter are to allow different values to be associated with the
constants as part of experimentation.
We shall refer to constants without specified values as ``parameters''.
So, in our terminology,
the following are constant declarations:
\begin{prism}
const int b = 3
const int INIT = 1
const int FINISH = 4
\end{prism}
whilst these are parameter declarations:
\begin{prism}
const int p
const int c
\end{prism}
\begin{code}
data CDecl
  = Constant Ident Type Number
  | Parameter Ident Type
  deriving (Eq,Show,Read)
\end{code}

\subsubsection{Variables}

Variables can have an optional initialisation,
but are initialised to zero or the lowest range value
if that is ommitted.
\begin{prism}
fm_clean_2 : [0..p]
pc : [INIT..FINISH] init INIT
i : [0..c] init 0
fm_clean : array [1..b] of [0..p]
\end{prism}
\begin{code}
data VDecl
  =  Var Ident Type
  | VInit Ident Type Number
  -- note, we can't init arrays with this.
  deriving (Eq,Show,Read)
\end{code}

\subsubsection{Declarations from Flash.prism}

\paragraph{Constants} from Prism:
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
    , Constant "INIT" IntT $ I 1
    , Constant "WRITE" IntT $ I 2
    , Constant "SELECT" IntT $ I 3
    , Constant "FINISH" IntT $ I 4
    ]
\end{code}

\paragraph{Variables} from Prism, using array declarations
\begin{prism}
fm_clean: array [1..b] of [0..p];
fm_erase: array [1..b] of [0..w];
pc: [INIT..FINISH] init INIT;
i: [0..c] init 0;
\end{prism}
\begin{code}
vdecl
  = [ Var "fm_clean" $ ArrT (I 0) (C "b") $ RngT (I 0) (C "p")
    , Var "fm_erase" $ ArrT (I 0) (C "b") $ RngT (I 0) (C "w")
    , VInit "pc" (RngT (C "INIT") (C "FINISH")) $ C "INIT"
    , VInit "i" (RngT (I 0) (C "c")) $ I 0
    ]
\end{code}

\newpage
\subsection{Flow of Control}

Here is an excerpt of control-flow:
\begin{prism}
[] pc=WRITE & i<c & writeable!=0 ->
  (fm_clean_1>0?1/writeable:0): (fm_clean_1'=fm_clean_1-1) & (i'=i+1) +
  (fm_clean_2>0?1/writeable:0): (fm_clean_2'=fm_clean_2-1) & (i'=i+1) +
  (fm_clean_3>0?1/writeable:0): (fm_clean_3'=fm_clean_3-1) & (i'=i+1);
[] pc=WRITE & i<c & writeable=0 -> (pc'=FINISH);
[] pc=SELECT & candidates!=0 & can_erase ->
  (cand_1_2 ? 1/candidates : 0): (fm_clean_2'=fm_clean_2-dirty_1) &
                                 (fm_clean_1'=p) & (fm_erase_1'=fm_erase_1+1) &
                                 (i'=0) & (pc'=WRITE) +
  (cand_1_3 ? 1/candidates : 0): (fm_clean_3'=fm_clean_3-dirty_1) &
                                 (fm_clean_1'=p) & (fm_erase_1'=fm_erase_1+1) &
                                 (i'=0) & (pc'=WRITE) +
  (cand_2_1 ? 1/candidates : 0): (fm_clean_1'=fm_clean_1-dirty_2) &
                                 (fm_clean_2'=p) & (fm_erase_2'=fm_erase_2+1) &
                                 (i'=0) & (pc'=WRITE) +
  (cand_2_3 ? 1/candidates : 0): (fm_clean_3'=fm_clean_3-dirty_2) &
                                 (fm_clean_2'=p) & (fm_erase_2'=fm_erase_2+1) &
                                 (i'=0) & (pc'=WRITE) +
  (cand_3_1 ? 1/candidates : 0): (fm_clean_1'=fm_clean_1-dirty_3) &
                                 (fm_clean_3'=p) & (fm_erase_3'=fm_erase_3+1) &
                                 (i'=0) & (pc'=WRITE) +
  (cand_3_2 ? 1/candidates : 0): (fm_clean_2'=fm_clean_2-dirty_3) &
                                 (fm_clean_3'=p) & (fm_erase_3'=fm_erase_3+1) &
                                 (i'=0) & (pc'=WRITE);
\end{prism}
From the Prism reference,
we see that these statements have three components:
\begin{itemize}
  \item Synchronising Events, of which this particular example has none.
  \item Boolean Guard Expression
  \item Probabilistic Choice over Updates.
\end{itemize}


Now that we have array values, we need to define some form of iterator/visitor
syntax.
We propose that the above becomes:
\begin{prism}
[] pc=WRITE & i<c & writeable!=0 ->
  for x:[1..b] apply + @
    (fm_clean[x]>0?1/writeable:0): (fm_clean'[x]=fm_clean[x]-1) & (i'=i+1);
[] pc=WRITE & i<c & writeable=0 -> (pc'=FINISH);
[] pc=SELECT & candidates!=0 & can_erase ->
  for from,to:[1..b] apply + @
  (x /= y && cand(x,y) ? 1/candidates : 0):
     (fm_clean[to]'=fm_clean[to]-dirty(from)) &
     (fm_clean[to]'=p) & (fm_erase[to]'=fm_erase[to]+1) & (i'=0) & (pc'=WRITE) ;
\end{prism}
Here we have a new \texttt{for}-construct:
\begin{prism}
for vars:ranges apply op to update
\end{prism}
Here this construct plays the role of a probabilistic choice over updates.
Note also  how the formul\ae now take parameters!


\newpage
\subsection{Formul\ae}

A selection of formul\ae:
\begin{prism}
formula writeable = (fm_clean_1!=0 ? 1 : 0) +  (fm_clean_2!=0 ? 1 : 0)
                  + (fm_clean_3!=0 ? 1 : 0);
formula dirty_1 = p-fm_clean_1;
formula dirty_2 = p-fm_clean_2;
formula dirty_3 = p-fm_clean_3;
formula cand_1_2 = dirty_1>0 & fm_clean_2 >= dirty_1;
formula cand_1_3 = dirty_1>0 & fm_clean_3 >= dirty_1;
formula cand_2_1 = dirty_2>0 & fm_clean_1 >= dirty_2;
formula cand_2_3 = dirty_2>0 & fm_clean_3 >= dirty_2;
formula cand_3_1 = dirty_3>0 & fm_clean_1 >= dirty_3;
formula cand_3_2 = dirty_3>0 & fm_clean_2 >= dirty_3;
formula candidates =
  (cand_1_2?1:0) + (cand_1_3?1:0) + (cand_2_1?1:0) +
  (cand_2_3?1:0) + (cand_3_1?1:0) + (cand_3_2?1:0);
\end{prism}
Again, we want to exploit our new array capabilities:
\begin{prism}
formula writeable = for x:[1..b] apply + to (fm_clean[x]!=0 ? 1 : 0);
formula dirty(x) = p-fm_clean[x];
formula cand(x,y) = x/=y & dirty(x)>0 & fm_clean[y] >= dirty(x);
formula candidates = for x,y:[1..b] apply + to (x/= && cand(x,y)?1:0);
\end{prism}
We see the new \texttt{for}-construct, where expressions replace updates
as well as having parameterised formul\ae.
So far the parameters are only variables.

\newpage
\subsection{The Big Picture}

\begin{code}
abs1
  = do putStrLn "Abs1 under development:"
       putStrLn "Constant Declarations:"
       putlist cdecl
       putStrLn "Variable Declarations:"
       putlist vdecl
       putStrLn "Also try ':browse Abs1' for now."
  where
    putlist xs = sequence_ $ map putthing xs
    putthing :: Show t => t -> IO ()
    putthing x = putStrLn $ ("  "++) $ show x
\end{code}

\subsubsection{Original Prism Code}

As a holding position, here is all of \texttt{Flash.prism}:
\begin{prism}
dtmc

const int b=3; // Block Count: Our problematic parameter
const int p; // Pages per Block
const int c; // Number of page writes between wear levelling
const int w; // Maximum wear tolerance (no. of erasures)
const int MAXDIFF; // Maximum desired difference in wear across blocks.
// control flow
const int INIT = 1;    // startup
const int WRITE = 2;   // page writes
const int SELECT = 3;  // wear-levelling
const int FINISH = 4;  // done: memory full or worn out

module Flash

// fm_clean_i, for i in 1..b - the number of clean pages in block i
fm_clean_1: [0..p];
fm_clean_2: [0..p];
fm_clean_3: [0..p];
// fm_erase_i, i in 1..b, the number of times block i has been erased.
fm_erase_1: [0..w];
fm_erase_2: [0..w];
fm_erase_3: [0..w];

pc: [INIT..FINISH] init INIT;
// count the number of page writes done since last wear-levelling.
i: [0..c] init 0;

// Step 1
[] pc=INIT ->
  (fm_clean_1'=p) & (fm_clean_2'=p) & (fm_clean_3'=p) &
  (fm_erase_1'=0) & (fm_erase_2'=0) & (fm_erase_3'=0) &
  (pc'=WRITE);
// Step 2
[] pc=WRITE & i<c & writeable!=0 ->
  (fm_clean_1>0?1/writeable:0): (fm_clean_1'=fm_clean_1-1) & (i'=i+1) +
  (fm_clean_2>0?1/writeable:0): (fm_clean_2'=fm_clean_2-1) & (i'=i+1) +
  (fm_clean_3>0?1/writeable:0): (fm_clean_3'=fm_clean_3-1) & (i'=i+1);
// Step 3
[] pc=WRITE & i<c & writeable=0 -> (pc'=FINISH);
// Step 4
[] pc=WRITE & i=c -> (pc'=SELECT);
// Step 5
[] pc=SELECT & (candidates=0 | !can_erase) -> (pc'=FINISH);
// Step 6
[] pc=SELECT & candidates!=0 & can_erase ->
  (cand_1_2 ? 1/candidates : 0): (fm_clean_2'=fm_clean_2-dirty_1) &
                                 (fm_clean_1'=p) & (fm_erase_1'=fm_erase_1+1) &
                                 (i'=0) & (pc'=WRITE) +
  (cand_1_3 ? 1/candidates : 0): (fm_clean_3'=fm_clean_3-dirty_1) &
                                 (fm_clean_1'=p) & (fm_erase_1'=fm_erase_1+1) &
                                 (i'=0) & (pc'=WRITE) +
  (cand_2_1 ? 1/candidates : 0): (fm_clean_1'=fm_clean_1-dirty_2) &
                                 (fm_clean_2'=p) & (fm_erase_2'=fm_erase_2+1) &
                                 (i'=0) & (pc'=WRITE) +
  (cand_2_3 ? 1/candidates : 0): (fm_clean_3'=fm_clean_3-dirty_2) &
                                 (fm_clean_2'=p) & (fm_erase_2'=fm_erase_2+1) &
                                 (i'=0) & (pc'=WRITE) +
  (cand_3_1 ? 1/candidates : 0): (fm_clean_1'=fm_clean_1-dirty_3) &
                                 (fm_clean_3'=p) & (fm_erase_3'=fm_erase_3+1) &
                                 (i'=0) & (pc'=WRITE) +
  (cand_3_2 ? 1/candidates : 0): (fm_clean_2'=fm_clean_2-dirty_3) &
                                 (fm_clean_3'=p) & (fm_erase_3'=fm_erase_3+1) &
                                 (i'=0) & (pc'=WRITE);
// Step 7
[] pc=FINISH -> true;

endmodule

// a block is writeable if it has at least one clean page
// We need to know how many of these there are.
formula writeable = (fm_clean_1!=0 ? 1 : 0) +  (fm_clean_2!=0 ? 1 : 0)
                  + (fm_clean_3!=0 ? 1 : 0);

// dirty_i, for i in 1..b - number of dirty pages in block i
formula dirty_1 = p-fm_clean_1;
formula dirty_2 = p-fm_clean_2;
formula dirty_3 = p-fm_clean_3;

// cand_i_j, for i,j in 1..b, i /= j
//  block i is dirty but there is space in block j for its pages
formula cand_1_2 = dirty_1>0 & fm_clean_2 >= dirty_1;
formula cand_1_3 = dirty_1>0 & fm_clean_3 >= dirty_1;
formula cand_2_1 = dirty_2>0 & fm_clean_1 >= dirty_2;
formula cand_2_3 = dirty_2>0 & fm_clean_3 >= dirty_2;
formula cand_3_1 = dirty_3>0 & fm_clean_1 >= dirty_3;
formula cand_3_2 = dirty_3>0 & fm_clean_2 >= dirty_3;

// the number of ways in which we can relocate dirty pages from one block
// to another so we can erase (clean) the first block.
formula candidates =
  (cand_1_2?1:0) + (cand_1_3?1:0) + (cand_2_1?1:0) +
  (cand_2_3?1:0) + (cand_3_1?1:0) + (cand_3_2?1:0);

// true when it is still possibe to erase ANY block,
// without exceeding the maximum allowable erase operations.
formula can_erase = fm_erase_1<w & fm_erase_2<w & fm_erase_3<w;

// diff_i_j, for i,j in 1..b, i /= j
// the difference in number of erasure of blocks i and j
formula diff_1_2 = fm_erase_1-fm_erase_2;
formula diff_1_3 = fm_erase_1-fm_erase_3;
formula diff_2_1 = fm_erase_2-fm_erase_1;
formula diff_2_3 = fm_erase_2-fm_erase_3;
formula diff_3_1 = fm_erase_3-fm_erase_1;
formula diff_3_2 = fm_erase_3-fm_erase_2;

// true if difference in wear equals some limit.
formula toobig =
  diff_1_2 >= MAXDIFF |
  diff_1_3 >= MAXDIFF |
  diff_2_1 >= MAXDIFF |
  diff_2_3 >= MAXDIFF |
  diff_3_1 >= MAXDIFF |
  diff_3_2 >= MAXDIFF;
\end{prism}
