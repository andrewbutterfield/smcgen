\section{Abstraction, Level One}\label{sec:lhs:Abs1}

\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at smcgen root
\end{verbatim}
\begin{code}
module Abs1 ( prism1, abs1 ) where
import Data.List
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
abs1 :: Prism1 -> [(String,Int)] -> IO ()
abs1 prsm fixedpars
  = do let code = prism1code prsm fixedpars
       putStrLn code
       let fname = "models/gen/FlashA1"++showpars++".prism"
       writeFile fname code
       putStrLn ("Prism written to "++fname)
  where
    showpars = concat $ map showpar fixedpars
    showpar (s,i) = '_':s ++ '_':show i
\end{code}



\newpage
\subsection{Expressions}

We need to support Prism expressions,
plus our extensions
\begin{code}
data Expr
  = B Bool -- literal boolean
  | I Int    -- literal int
  | D Double -- literal double
  | N Ident  -- variable/constant name
  | N' Ident -- after-value of N
  | F String -- function name /operator symbol
      [Expr] -- function/operator arguments
  | P Expr  -- probability
      Expr  -- (update) expression
  -- added stuff
  | AI Expr  -- array-valued expression
       Expr  -- array index
  | AF [VDecl]  -- array indices declaration
       String   -- operator symbol
       Expr     -- array body expression/update
  deriving (Eq,Show,Read)

isNum :: Expr -> Bool
isNum (I _)  =  True
isNum (D _)  =  True
isNum (N _)  =  True
isNum _      =  False
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
infixl 7 ./  ;  e1 ./ e2   =   F "/"   [e1,e2]
infixl 7 .*  ;  e1 .* e2   =  aF "*"   [e1,e2]
infixl 6 .+  ;  e1 .+ e2   =  aF "+"   [e1,e2]
infixl 6 .-  ;  e1 .- e2   =  aF "-"   [e1,e2]
infix  4 .=  ;  e1 .= e2   =   F "="   [e1,e2]
infix  4 .!= ;  e1 .!= e2  =   F "!="  [e1,e2]
infix  4 .<  ;  e1 .< e2   =   F "<"   [e1,e2]
infix  4 .>  ;  e1 .> e2   =   F ">"   [e1,e2]
infix  4 .>= ;  e1 .>= e2  =   F ">="  [e1,e2]
infix  4 .<= ;  e1 .<= e2  =   F "<="  [e1,e2]
infixl 3 .&  ;  e1 .&  e2  =  aF "&"   [e1,e2]
infixl 2 .|  ;  e1 .|  e2  =  aF "|"   [e1,e2]
infix  1 <=> ;  e1 <=> e2  =   F "<=>" [e1,e2]
infix  0 .=> ;  e1 .=> e2  =   F "=>"  [e1,e2]
-- faking e0 .? e1 .: e2 -->
infix  1 .:  ;  e1 .: e2   =           [e1,e2]
infix  0 .?  ;  e0 .? es   =   F "?:"  (e0:es)

isInfix [c] = c `elem` "/*+-=<>&|"
isInfix nm = nm `elem` ["!=",">=","<=","<=>","=>"]

-- infix operator precedences
prec "/"    =  7
prec "*"    =  7
prec "+"    =  6
prec "-"    =  6
prec "="    =  5
prec "!="   =  5
prec "<"    =  5
prec ">"    =  5
prec ">="   =  5
prec "<="   =  5
prec "&"    =  4
prec "|"    =  3
prec "<=>"  =  2
prec "=>"   =  1
prec _      =  0


lnot e = F "!" [e]
\end{code}

We have defined a number of functions that optimise certain
situations, so that, for example, $a + (b + c)$ becomes $a + b + c$
\begin{code}
aF nm es = F nm $ assocflat nm es

assocflat _ [] = []
assocflat nm (F nm' es':es)
 | nm' == nm  =  es' ++ assocflat nm es
assocflat nm (e:es) = e : assocflat nm es
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
type Number = Expr -- Atomic (I, D or N only)
data Type
  = BoolT | IntT | DblT -- basic types
  | RngT Number Number -- range type, lowest to highest
  | ArrT Number Number Type -- array type
  deriving (Eq,Show,Read)

-- functions that enforce the use of Number, rather than Expr
rngT n1 n2
 | isNum n1 && isNum n2  =  RngT n1 n2
 | otherwise  =  error "rngT: both expressions must be number or variable"

arrT n1 n2 t
 | isNum n1 && isNum n2  =  ArrT n1 n2 t
 | otherwise  =  error "arrT: both expressions must be number or variable"
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
_1 = I 1 ; _2 = I 2 ; _3 = I 3 ; _4 = I 4
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

\paragraph{Variables} from Prism, using array declarations
\begin{prism}
fm_clean: array [1..b] of [0..p];
fm_erase: array [1..b] of [0..w];
pc: [INIT..FINISH] init INIT;
i: [0..c] init 0;
\end{prism}
\begin{code}
_0 = I 0
vdecl
  = [ Var "fm_clean" $ arrT _1 b $ rngT _0 p
    , Var "fm_erase" $ arrT _1 b $ rngT _0 w
    , VInit "pc" (rngT _INIT _FINISH) _INIT
    , VInit "i" (rngT _0 c) _0
    ]
 -- as most commonly used expressions
fm_clean[x] = AI (N "fm_clean") x ; fm_clean'[x] = AI (N' "fm_clean") x
fm_erase[x] = AI (N "fm_erase") x ; fm_erase'[x] = AI (N' "fm_erase") x
pc       = N "pc"       ; pc'       = N' "pc"
i        = N "i"        ; i'        = N' "i"
\end{code}

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
Here we see the need for arrays
and a new \texttt{for}-expression:
\begin{prism}
for vars:ranges apply op to expr
\end{prism}

We can use this to simplify all of the above:
\begin{prism}
formula writeable = for x:[1..b] apply + to (fm_clean[x]!=0 ? 1 : 0);
formula dirty(x) = p-fm_clean[x];
formula cand(x,y) = x/=y & dirty(x)>0 & fm_clean[y] >= dirty(x);
formula candidates = for x,y:[1..b] apply + to (x/= && cand(x,y)?1:0);
\end{prism}
We see the new \texttt{for}-construct, where expressions replace updates
as well as having parameterised formul\ae.
So far the parameters are only variables.
So the general form is a formula-name,
zero or more variable arguments,
and a body-expression.
We shall treat an update as an expression,
that has dashed-forms of variables in it.
\begin{code}
data Formula
  = Formula Ident [Ident] Expr
  deriving (Eq,Show,Read)
\end{code}

\subsubsection{Formulas from Flash.prism}

Rewritten ``our style'':
\begin{prism}
formula writeable = for x:[1..b] apply + to (fm_clean[x]!=0 ? 1 : 0);
\end{prism}
\begin{code}
x = N "x" ; y = N "y"
_writeable
  = Formula "writeable" []
            $ AF [Var "x" (rngT _1 b)]
                 "+"
                 (fm_clean[x] .!= _0 .? _1 .: _0)
writeable = N "writeable"
\end{code}
\begin{prism}
formula dirty(x) = p-fm_clean[x];
\end{prism}
\begin{code}
_dirty
  = Formula "dirty" ["x"]
            (p .- fm_clean[x])
dirty e = F "dirty" [e]
\end{code}
\begin{prism}
formula cand(x,y) = x!=y & dirty(x)>0 & fm_clean[y] >= dirty(x);
\end{prism}
\begin{code}
_cand
  = Formula "cand" ["x","y"]
            ( x .!= y .&
              dirty(x) .> _0 .&
              fm_clean[x] .>= dirty(x) )
cand (e, f) = F "cand" [e,f]
\end{code}
\begin{prism}
formula candidates = for x,y:[1..b] apply + to (x!=y & cand(x,y)?1:0);
\end{prism}
\begin{code}
_candidates
  = Formula "candidates" []
            $ AF [Var "x" (rngT _1 b),Var "y" (rngT _1 b)]
                 "+"
                 ( x .!= y .&
                   cand (x, y) .? _1 .: _0 )
candidates = N "candidates"
\end{code}
\begin{prism}
formula can_erase = for x:[1..b] apply & to fm_erase[x]<w ;
\end{prism}
\begin{code}
_can_erase
  = Formula "can_erase" []
            $ AF [Var "x" (rngT _1 b)]
                 "&"
                 ( fm_erase[x] .< w)
can_erase = N "can_erase"
\end{code}
\begin{prism}
formula diff(x,y) = fm_erase(x)-fm_erase(y);
\end{prism}
\begin{code}
_diff
  = Formula "diff" ["x","y"]
            ( fm_erase[x] .- fm_erase[y] )
diff (e,f) = F "diff" [e,f]
\end{code}
\begin{prism}
formula toobig = for x,y:[1..b] apply | to (x!=y & diff(x,y) >= MAXDIFF)
\end{prism}
\begin{code}
_toobig
  = Formula "toobig" []
            $ AF [Var "x" (rngT _1 b),Var "y" (rngT _1 b)]
                 "|"
                 ( x .!= y .&
                   diff(x, y) .>= _MAXDIFF )
toobig = N "toobig"
\end{code}
\begin{code}
formulae = [_writeable,_dirty,_cand,_candidates,_can_erase,_diff,_toobig]
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
The latter can be considered as as using two extensions
to the expression idea, namely tagging with a probability expression,
and using dashed variables in expressions.
\begin{code}
data Command
  = Cmd [String]  -- synchronisation labels
        Expr      -- boolean guard
        Expr      -- Update Expression
  deriving (Eq, Show, Read)
\end{code}


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
Here the \texttt{for}-construct plays the role of a probabilistic choice over updates.

\subsubsection{Commands from Flash.prism}

Rewritten ``our style'':

\begin{prism}
[] pc=INIT ->
  ( for x:[1..b] apply & to (fm_clean'[x]=p) & (fm_erase'[x]=0)) )
  & (pc'=WRITE);
\end{prism}
\begin{code}
cmd1 = Cmd [] (pc .= _INIT)
           ( ( AF [Var "x" $ rngT _1 b]
                "&"
                ( fm_clean'[x] .= p) .& fm_erase[x] .= _0 )
              .& pc' .= _WRITE )
\end{code}
\begin{prism}
[] pc=WRITE & i<c & writeable!=0 ->
  for x:[1..b] apply + @
    (fm_clean[x]>0?1/writeable:0): (fm_clean'[x]=fm_clean[x]-1) & (i'=i+1);
\end{prism}
\begin{code}
cmd2 = Cmd [] (pc .= _WRITE .& writeable .!= _0)
           ( AF [Var "x" $ rngT _1 b]
                "+"
                ( P (fm_clean[x] .> _0 .? _1./writeable .: _0)
                    ( fm_clean'[x] .= fm_clean[x]
                      .& i' .= i .+ _1 ) ) )
\end{code}
\begin{prism}
[] pc=WRITE & i<c & writeable=0 -> (pc'=FINISH);
\end{prism}
\begin{code}
cmd3 = Cmd [] (pc .= _WRITE .& writeable .= _0) (pc' .= _FINISH)
\end{code}
\begin{prism}
[] pc=WRITE & i=c -> (pc'=SELECT);
\end{prism}
\begin{code}
cmd4 = Cmd [] (pc .= _WRITE .& i .= c) (pc' .= _SELECT)
\end{code}
\begin{prism}
[] pc=SELECT & (candidates=0 | !can_erase) -> (pc'=FINISH);
\end{prism}
\begin{code}
cmd5 = Cmd [] (pc .= _SELECT .& ( candidates .= _0 .| lnot can_erase ) )
              (pc' .= _FINISH)
\end{code}
\begin{prism}
[] pc=SELECT & candidates!=0 & can_erase ->
  for from,to:[1..b] apply + @
  (from != to & cand(from,to) ? 1/candidates : 0):
     (fm_clean[to]'=fm_clean[to]-dirty(from)) &
     (fm_clean[from]'=p) & (fm_erase[from]'=fm_erase[from]+1) &
     (i'=0) & (pc'=WRITE) ;
\end{prism}
\begin{code}
from = N "from" ; to = N "to"
cmd6 = Cmd [] (pc .= _SELECT .& candidates .!= _0 .& can_erase)
           ( AF [Var "from" $ rngT _1 b,Var "to" $ rngT _1 b]
                "+"
                ( P ( from .!= to .& cand(from,to) .? _1./candidates .: _0)
                    ( fm_clean'[to] .= fm_clean[to] .- dirty(from)
                      .& fm_clean'[from] .= p
                      .& fm_erase'[from] .= fm_erase[from] .+ _1
                      .& i' .= _0 .& pc' .= _WRITE ) ) )
\end{code}
\begin{prism}
[] pc=FINISH -> true;
\end{prism}
\begin{code}
true = B True
cmd7 = Cmd [] (pc .= _FINISH) true
\end{code}
\begin{code}
commands = [cmd1,cmd2,cmd3,cmd4,cmd5,cmd6,cmd7]
\end{code}

\subsubsection{The Big Picture}

\begin{code}
data SemModel = DTMC | Others deriving (Eq, Show, Read)
type Module1 = (Ident, [VDecl], [Command])
type Prism1 = (SemModel,[CDecl], [Module1], [Formula] )

prism1 = (DTMC, cdecl, [("Flash",vdecl,commands)], formulae)
\end{code}

\newpage
\subsection{Generating Prism}

In order to generate Prism,
we know we have to fix \prsm{b},
but can allow other constants to remain underspecified.
At this level of abstraction,
we assume some oracle (us!) that can supply a list of constants
that need fixing, along with suggested values.

\begin{code}
prism1code  :: Prism1 -> [(String,Int)] -> String
prism1code (smod,cdcl,ms@[(nm,vdcl,cmmds)],form) fixedpars
  = let parsf = alookup fixedpars in
     unlines (
       [    "// Abs1 under development"
       ,  prismSM smod
       ,  ( "\n// Fixed Parameters are "++show fixedpars ) ]
       ++ ( "\n// Constant Decls:\n// -----"
            : prismKs parsf cdcl  )
       ++ ( "\n// Module Decls:\n// -----"
            : prismMs parsf ms  )
       ++ ( "\n// Formulae:\n// -----"
            : prismFs parsf form  ) )

prismSM DTMC = "dtmc"
prismSM _ = "// unknown semantic model !"
\end{code}

\subsubsection{Generating Prism Constants}
\begin{code}
prismKs :: (String -> Maybe Int) -> [CDecl] -> [String]
prismKs fpars = map (prismK fpars)

prismK :: (String -> Maybe Int)-> CDecl -> String
prismK fpars (Constant id typ num) -- const int INIT = 1;
  = "const "++prismT fpars typ++" "++id++" = "++prismE fpars num++";"
prismK fpars (Parameter id typ) -- const int p;
  = case fpars id of
      Nothing  ->  "const "++prismT fpars typ++" "++id++";"
      Just n   ->  "const "++prismT fpars typ++" "++id++" = "++show n++";"
\end{code}

\subsubsection{Generating Prism Modules}
\begin{code}
prismMs :: (String -> Maybe Int) -> [Module1] -> [String]
prismMs fpars = concat . map (prismM fpars)

prismM :: (String -> Maybe Int)-> Module1 -> [String]
prismM parsf (nm, vdcl, cmmds)
  = ( "\nmodule "++ nm )
     : ( "\n// Variable Decls:\n// -----"
          : prismVs parsf vdcl
    ++ ( "\n// Commands:\n// -----"
          : prismCs parsf cmmds )
    ++ [ "\nendmodule\n"] )
\end{code}


\subsubsection{Generating Prism Variables}
\begin{code}
prismVs :: (String -> Maybe Int) -> [VDecl] -> [String]
prismVs fpars = map ((++";") . prismV fpars)

prismV fpars (Var id typ)
 = id ++ ": " ++ prismT fpars typ
prismV fpars (VInit id typ exp)
 = id ++ ": " ++ prismT fpars typ ++ " init "++prismE fpars exp
\end{code}

\subsubsection{Generating Prism Commands}
\begin{code}
prismCs :: (String -> Maybe Int) -> [Command] -> [String]
prismCs fpars = map (prismC fpars)

prismC fpars (Cmd syncs grd upd)
  = '\n':show syncs
    ++ " "    ++ prismE fpars grd
    ++ " -> " ++ prismE fpars upd
\end{code}

\subsubsection{Generating Prism Formul\ae}
\begin{code}
prismFs :: (String -> Maybe Int) -> [Formula] -> [String]
prismFs fpars = map (prismF fpars)

prismF fpars (Formula nm [] body)
  = "\nformula "++nm++" = "++prismE fpars body
prismF fpars (Formula nm args body)
  = "\nformula "++nm++"("++intercalate "," args++") = " ++prismE fpars body
\end{code}

\subsubsection{Generating Prism Types}
\begin{code}
prismT fpars BoolT = "bool"
prismT fpars IntT = "int"
prismT fpars DblT = "double"
prismT fpars (RngT n1 n2) = "["++prismE fpars n1++".."++prismE fpars n2++"]"
prismT fpars (ArrT n1 n2 typ)
  = "array ["++prismE fpars n1++".."++prismE fpars n2++"] of "
     ++ prismT fpars typ
\end{code}

\subsubsection{Generating Prism Expressions}
\begin{code}
prismE :: (String -> Maybe Int) -> Expr -> String
prismE fpars expr
  = prismE' 0 expr
  where
    -- for array declarations
    prismAD idcls = intercalate "," $ map (prismV fpars) idcls

    prismE' pc (B b)  =  if b then "true" else "false"
    prismE' pc (I i)  = show i
    prismE' pc (D d)  = show d
    prismE' pc (N n)  = n
    prismE' pc (N' n)  = n ++ "'"
    prismE' pc (P prob expr) = "("++prismE' 0 prob++"): "++ prismE' pc expr
    prismE' pc (AI arr idx) = prismE' pc arr ++ "["++prismE' 0 idx++"]"
    prismE' pc (AF idcls op expr)
     =    "\n  for " ++ prismAD idcls ++ " apply " ++ op
       ++ "\n   to " ++ prismE' 0 expr
\end{code}

The treatment of function/operators is complicated.
\begin{code}
    prismE' pc (F "?:" [c,t,e])
     = "("++prismE' 0 c++" ? "++prismE' 0 t++" : "++prismE' 0 e++")"
    prismE' pc (F op es)
      | isInfix op
        =  bracket pc pop (intercalate (' ':op++" ") $ map (prismE' pop) es)
      where pop = prec op
    prismE' pc (F f es) = f ++ "("++(intercalate "," $ map (prismE' 0) es)++")"

bracket pc pop str -- pc: context precedence, pop: operator precedence
 | pop < pc   =  "("++str++")"
 | otherwise  =  str
\end{code}

\subsection{Random Code bits}

\begin{code}
alookup :: (Eq a, Monad m) => [(a,b)] -> a -> m b
alookup [] _ = fail "not found"
alookup ((x,y):xys) z
 | z == x  =  return y
 | otherwise  = alookup xys z
\end{code}
