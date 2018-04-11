\section{Domain Specific Language, Level One}\label{sec:lhs:DSL1}

\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at smcgen root
\end{verbatim}
\begin{code}
module DSL1 where
import Data.List
import Data.Maybe

import Utilities

import Debug.Trace
dbg msg x = trace (msg ++ show x) x
\end{code}

\subsection{Expressions}

We need to support Prism expressions,
plus our extensions
\begin{code}
type ADecl  -- array index declaration
  = ( Ident       -- index variable
    , ( Expr      -- lower bound
      , Expr ) )  -- upper bound

data Expr
  = B Bool -- literal boolean
  | I Int    -- literal int
  | D Double -- literal double
  | N Ident  -- variable/constant name
  | U Ident Expr -- simple variable update
  | UA Ident Expr Expr -- array variable update
  | F String -- function name /operator symbol
      [Expr] -- function/operator arguments
  | P Expr  -- probability
      Expr  -- (update) expression
  -- added stuff
  | AI Expr  -- array-valued expression
       Expr  -- array index
  | AF [ADecl]  -- array index declarations.
       String   -- operator symbol
       Expr     -- guard expression
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
-- faking updates
infix  4 .:=  ;  n  .:= e   =  n e

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
the following is a constant declaration:
\begin{prism}
const int b = 3
\end{prism}
whilst this is a parameter declaration:
\begin{prism}
const int p
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
pc : [INIT..FINISH] init INIT
i : [0..c] init 0
\end{prism}
\begin{code}
data VDecl
  =  Var Ident Type
  | VInit Ident Type Number
  -- note, we can't init arrays with this.
  deriving (Eq,Show,Read)
\end{code}

\subsubsection{Declarations from Flash.prism}

\paragraph{Constants}

\begin{code}
_1 = I 1 ; _2 = I 2 ; _3 = I 3 ; _4 = I 4
\end{code}

\newpage
\subsection{Formul\ae}


We can use this to simplify all of the above:
\begin{prism}
formula writeable = for x:[1..b] apply + over (fm_clean[x]!=0 ? 1 : 0);
formula dirty(x:[1..b]) = p-fm_clean[x];
formula cand(x,y:[1..b]) = x/=y ->  dirty(x)>0 & fm_clean[y] >= dirty(x);
formula candidates = for x,y:[1..b] apply + over x!=y -> cand(x,y)?1:0);
\end{prism}
We see the new \texttt{for}-construct, where expressions replace updates
as well as having parameterised formul\ae.
So far the parameters are only variables.
So the general form is a formula-name,
zero or more variable arguments,
and a body-expression.
We shall treat an update as an expression,
that has dashed-forms of variables in it.
We have tow variants here, as we want an explicit guard at the top-level
if we have parameters
\begin{code}
data Formula
  = Formula Ident  -- formula name
            Expr   -- formula expression - can be a for-construct
  | PFormula Ident   -- formula name
             [ADecl] -- parameter declarations (non-empty)
             Expr    -- guard expression over parameters only
             Expr    -- formula expression, no for-constructs.
  deriving (Eq,Show,Read)
\end{code}


\newpage
\subsection{Flow of Control}

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

\subsubsection{The Big Picture}

\begin{code}
data SemModel = DTMC | Others deriving (Eq, Show, Read)
type Module1 = (Ident, [VDecl], [Command])
type Prism1 = (SemModel,[CDecl], [Module1], [Formula] )
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
       [  prismSM smod
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
    ++ " ;"
\end{code}

\subsubsection{Generating Prism Formul\ae}
\begin{code}
prismFs :: (String -> Maybe Int) -> [Formula] -> [String]
prismFs fpars = map (prismF fpars)

prismF fpars (Formula nm body)
  = "\nformula "++nm++" = "++prismE fpars body ++ " ;"
prismF fpars (PFormula nm args grd body)
  = "\nformula "
       ++ nm ++ "(" ++ prismADs fpars args ++ ") = "
       ++ optGrd fpars grd ++ prismE fpars body ++ " ;"

optGrd fpars (B True) = ""
optGrd fpars grd = prismE fpars grd ++ " -> "

prismADs fpars adecls  = intercalate "," (map (prismAD fpars) adecls)

prismAD fpars ((nm,bounds))  = nm ++ ":[" ++ prismA fpars bounds ++ "]"

prismA fpars (low,high)  = prismE fpars low ++ ".." ++ prismE fpars high
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
    prismE' pc (B b)  =  if b then "true" else "false"
    prismE' pc (I i)  = show i
    prismE' pc (D d)  = show d
    prismE' pc (N n)  = n
    prismE' pc (U n e)  = "(" ++ n ++ "' = " ++ prismE' 0 e ++ ")"
    prismE' pc (P prob expr) = "("++prismE' 0 prob++"): "++ prismE' 0 expr
    prismE' pc (AI arr idx) = prismE' pc arr ++ "["++prismE' 0 idx++"]"
    prismE' pc (UA n idx e)
      = "(" ++ n ++ "'["++prismE' 0 idx ++ "] = "
         ++ prismE' 0 e ++ ")"
    prismE' pc (AF adcls op grd expr)
      | pc == 0 = "\n" ++ forstr
      | otherwise  =  "\n  (" ++ forstr ++ ")"
      where
       forstr =
           "  for  " ++ prismADs fpars adcls ++ " apply " ++ op
        ++ " over \n    " ++ optGrd fpars grd ++ prismE' 0 expr
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

\subsection{Compiling Arrays Away}

We have abstract syntax and code output for our extended form of Prism,
of which ``standard'' Prism is a subset.
We will now define a compiler that maps our extended-prism abstract syntax
into a sematintically equivalent standard abstract syntax.
The standard syntax does not use the array type or the \texttt{for}-construct.

At this level of abstraction we assume that everything is ``well-formed'',
and perform no checks for this.
In fact we are using this level of abtraction
to clarify what well-formedness should be.
In the code that follows, any lack of well-formedness
should lead to a runtime error%
\footnote{
We will address this more rigourously in Abstraction Level Two
}%
.

\subsubsection{Compiling Extended Prism}
The semantic module and constant declarations
are all just standard.
\begin{code}
x2sPrism :: [(String,Int)] -> Prism1 -> Prism1
x2sPrism fixedpars (smod,cdcl,ms,form)
 = ( smod ,cdcl
   , map (x2sModule pfnames fxparnms cval) ms
   , concat $ map (x2sFormula pfnames fxparnms cval) form )
 where
   fxparnms = map fst fixedpars
   cval :: Ident -> Int
   cval = aget fixedpars

   -- names of formulae with parameters
   pfnames = catMaybes $ map getPFN form

   getPFN (PFormula nm args _ _)  =  if null args then Nothing else Just nm
   getPFN _                       =  Nothing

\end{code}

\subsubsection{Compiling Extended Modules}
\begin{code}
x2sModule :: [Ident] -> [Ident] -> (Ident -> Int) -> Module1 -> Module1
x2sModule pfnames fxparnms cval (nm,vdcl,cmmds)
  = ( nm
    , concat $ map (x2sVDecl cval) vdcl
    , map (x2sCommand pfnames fxparnms cval) cmmds )
\end{code}

\newpage
\subsubsection{Compiling Extended Variable Declarations}
The extended declarations are those involving an array type.

\WF{array bounds}
{The range-types that define the array bounds
only use literal numbers, or initialised constants.}

The \texttt{cval} argument of this function assumes this well-formedness.
\begin{code}
x2sVDecl :: (Ident -> Int) -> VDecl -> [VDecl]
x2sVDecl cval (Var i typ)
 = let
     (basetype,bounds) = collArrBounds cval [] typ
     variants = bounds2variants bounds
   in map (declVV i basetype) variants
x2sVDecl _ vdcl = [vdcl]

-- we assume n1 and n2 are either ints, or a constant known to cval
collArrBounds :: (Ident -> Int) -> [(Int,Int)] -> Type -> (Type,[(Int,Int)])
collArrBounds cval bounds (ArrT n1 n2 t)
  = collArrBounds cval (numEval2 cval (n1,n2) : bounds) t
collArrBounds cval bounds basetype  =  (basetype,reverse bounds)

numEval2 :: (Ident->Int) -> (Expr,Expr) -> (Int,Int)
numEval2 envf (e1,e2) = (numEval envf e1, numEval envf e2)

numEval :: (Ident->Int) -> Expr -> Int
-- will fail at runtime if expression is not known to be a number
numEval _    (I i) = i
numEval envf (N n) = envf n

bounds2variants :: [(Int,Int)] -> [[Int]]
bounds2variants bounds = lprod $ map bExp bounds

bExp (n1,n2) = [n1..n2]

declVV i btyp ns = Var (i ++ concat (map pvalue2str ns)) btyp

pvalue2str n = '_' : show n
\end{code}

\newpage
\subsubsection{Compiling Extended Commands}

\WF{For-Commands}
{The \texttt{for}-constructs occur
only in the update expression,
but could be at any level within function/operator applications.
Currently we assume they are not nested.}

\begin{code}
x2sCommand :: [Ident] -> [Ident] -> (Ident -> Int) -> Command -> Command
x2sCommand pfnames fxparnms cval (Cmd synch cgrd update)
  = Cmd synch cgrd $ x2sUpdate pfnames fxparnms cval update


x2sUpdate pfnames fxparnms cval (AF adcls op bgrd body)
  = x2sForCmd pfnames fxparnms cval adcls op bgrd body
x2sUpdate pfnames fxparnms cval (F nm upds)
  = F nm $ map (x2sUpdate pfnames fxparnms cval) upds
x2sUpdate pfnames fxparnms cval cmd  =  cmd

x2sForCmd pfnames fxparnms cval adcls op bgrd body
  = let
      (pnms,variants) = genParameterVariants cval adcls
      instfs = map (aget . zip pnms) variants
      grds' = map (exprEval fxparnms cval . specialiseExpr' pnms bgrd) instfs
      bodies' = map (specialiseFormCall pfnames . specialiseExpr' pnms body)
                    instfs
      stuff = zip grds' bodies'
      bodies'' = map snd $ filter (theBool . fst) stuff
      theBool (B b) = b
    in F op bodies''

specialiseExpr' pnms e instf  =  specialiseExpr pnms instf e
\end{code}

\newpage
\subsubsection{Compiling Extended Formul\ae}
The extensions to formulas include the addition of arguments to formulas.

\WF{array usage in formul\ae}
{The \texttt{for}-construct can only be used in formulas without arguments.}

\begin{code}
x2sFormula :: [Ident] -> [Ident] -> (Ident -> Int) -> Formula -> [Formula]
x2sFormula pfnames fxparnms cval (Formula nm body)
  =  [Formula nm $ x2sExpr pfnames fxparnms cval body]
x2sFormula pfnames fxparnms cval form@(PFormula fnm args grd body)
  =  map pformula stuff'
  where
    (pnms,variants) = genParameterVariants cval args
    instfs = map (aget . zip pnms) variants
    grds'    =  map (exprEval fxparnms cval . specialiseExpr' pnms grd) instfs
    fnms' = map (specialiseFName pnms fnm) instfs
    bodies'  =  map (specialiseFormCall pfnames . specialiseExpr' pnms body)
                    instfs
    stuff = zip grds' $ zip fnms' bodies'
    stuff' = map snd $ filter (theBool . fst) stuff
    theBool (B b) = b
    pformula (fnm',body') = Formula fnm' body'

specialiseFName pnms fnm instf
  = fnm ++ concat (map (pvalue2str . instf) pnms)
\end{code}

\newpage
\subsubsection{Compiling Extended Expressions}
Extensions for expressions include array indexing,
and the \texttt{for}-construct.

\WF{array usage in expressions}
{The \texttt{for}-construct can only occur at the top-level}

\WF{formula usage in expressions}
{Any application of a parameterised formula
can only be to the variables declared in the enclosing \texttt{for}-construct}

\begin{code}
x2sExpr :: [Ident] -> [Ident] -> (Ident -> Int) -> Expr -> Expr
x2sExpr pfnames fxparnms cval (AF adcls op g e)
  = x2sFor pfnames fxparnms cval adcls op g e
x2sExpr pfnames fxparnms cval e = e
\end{code}

\subsubsection{Compiling For-Expressions}

We need to know here the \emph{names} of the parameterised formul\ae.

Assuming \prsm{b=3} and given (for example):
\begin{prism}
for x,y:[1..b] apply & over (x != y) ->  (cand(x,y) ? 1 : 0)
\end{prism}
We first take the declaration types and compute their \texttt{lprod}:
\begin{verbatim}
[[1,1],[1,2],[1,3],[2,1],[2,2],[2,3],[3,1],[3,2],[3,3]]
\end{verbatim}
We then want \prsm{x} and \prsm{y} to range over these values.
Consider the case \prsm{x=3 & y=2}.
We then do a substition in the guard and body, to obtain:
\begin{prism}
(3 != 2) ->  (cand(3,2) ? 1 : 0)
\end{prism}
We then attepmpt to evaluate guards to eliminate terms,
as much as is possible.
Here we obtain:
\begin{prism}
cand(3,2) ? 1 : 0
\end{prism}
We then look for applications of known parameterised formulae
and use the parameters to transform the name, getting
\begin{prism}
cand_3_2 ? 1 : 0
\end{prism}
We finish by applying the operator \texttt{op} to the list of the outcomes,
with some removal of unit values.
\begin{code}
x2sFor :: [Ident] -> [Ident] -> (Ident->Int)
       -> [ADecl] -> String -> Expr -> Expr
       -> Expr
x2sFor pfnames fxparnms cval adcls op g e
  = let
      (bvars,variants) = genParameterVariants cval adcls
      bodies = catMaybes $ map (specialiseBody fxparnms cval bvars g e) variants
      bodies' = map (specialiseFormCall pfnames) bodies
    in F op bodies'

genParameterVariants cval args
  = let
      (bvars,bounds) = unzip args
      variants = bounds2variants $ map (numEval2 cval) bounds
    in (bvars,variants)
\end{code}

\newpage
Specialising the body of an array expression.
We assume that the length of \texttt{bvars} and \texttt{variant}
are the same.

\WF{array guards}
{\texttt{for}-construct guard-expressions are boolean-valued,
and their value depends only on the array index variables}
\begin{code}
specialiseBody fxparnms cval bvars g e variant
  = let
      instf = aget $ zip bvars variant
      g' = specialiseExpr bvars instf g
    in case exprEval fxparnms cval g' of
      (B False)  ->  Nothing
      (B True) -> Just $ specialiseExpr bvars instf e
      gv  ->  Just (gv .=> specialiseExpr bvars instf e)
\end{code}

Specialising an expression:
\begin{code}
specialiseExpr bvars instf e@(N n)
  | n `elem` bvars  =  I $ instf n
  | otherwise       =  e
specialiseExpr bvars instf (U n e)
  = U n $ specialiseExpr bvars instf e
specialiseExpr bvars instf (F nm es)
  = F nm $ map (specialiseExpr bvars instf) es
specialiseExpr bvars instf (P e1 e2)
  = P (specialiseExpr bvars instf e1) (specialiseExpr bvars instf e2)
specialiseExpr bvars instf (AI e1 e2)
  = AI (specialiseExpr bvars instf e1) (specialiseExpr bvars instf e2)
specialiseExpr bvars instf (UA n e1 e2)
  = UA n (specialiseExpr bvars instf e1) (specialiseExpr bvars instf e2)
specialiseExpr bvars instf (AF adcls op e1 e2)
  = let
      bvars' = bvars \\ (map fst adcls)
    in AF adcls op (specialiseExpr bvars' instf e1)
                   (specialiseExpr bvars' instf e2)
specialiseExpr bvars instf e = e
\end{code}

Evaluating an expression.
\begin{code}
exprEval fxparnms cval e@(N n)
 | n `elem` fxparnms  =  I $ cval n
 | otherwise          =  e
exprEval fxparnms cval e@(F op es)
  = case opEval fxparnms cval op $ map (exprEval fxparnms cval) es of
      Nothing  ->  e
      Just e'  ->  e'
exprEval fxparnms cval (U n e) = U n $ exprEval fxparnms cval e
exprEval fxparnms cval (P e1 e2)
  = P (exprEval fxparnms cval e1) (exprEval fxparnms cval e2)
exprEval fxparnms cval (UA n e1 e2)
  = UA n (exprEval fxparnms cval e1) (exprEval fxparnms cval e2)
exprEval fxparnms cval e = e
\end{code}

Evaluating an operator.
We succeed if all the sub-expressions are values of the same type,
that is also compatible with the specific operator.
For now we assume all arithmetic is done only on integer values.
Later, we should design the evaluator to mimic that of Prism.
For now, we just handle the integer not-equal operator.
\begin{code}
opEval fxparnms cval op [] = Nothing
opEval fxparnms cval "!=" [I i1, I i2]  = Just $ B (i1 /= i2)
opEval _ _ _ _ = Nothing
\end{code}

Look for calls involving parameterised formula names
and array indexing
and convert to appropriate identifiers.
\begin{code}
specialiseFormCall :: [Ident] -> Expr -> Expr
specialiseFormCall pfnames (F nm es)
 | nm `elem` pfnames && allArgsInt = N (nm++ concat (map pvalue2str intargs))
 | otherwise  =  F nm es'
 where
   es' = map (specialiseFormCall pfnames) es
   (allArgsInt,intargs) = chkIntArgs es'
   chkIntArgs [] = (True,[])
   chkIntArgs (I i:rest) = let (ok,args') = chkIntArgs rest in (ok,i:args')
   chkIntArgs _ = (False,[])
specialiseFormCall pfnames (AI (N n) (I i))  =  N  (n ++ "_" ++ show i)
specialiseFormCall pfnames (UA n (I i) e)
  =  U (n ++ "_" ++ show i) $ specialiseFormCall pfnames e
specialiseFormCall pfnames (P e1 e2)
 = P (specialiseFormCall pfnames e1) (specialiseFormCall pfnames e2)
specialiseFormCall pfnames e = e
\end{code}
