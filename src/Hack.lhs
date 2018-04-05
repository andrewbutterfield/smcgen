\section{Hacking}\label{sec:lhs:Hack}
\begin{verbatim}
Copyright  Andrew Buttefield (c) 2018

LICENSE: BSD3, see file LICENSE at smcgen root
\end{verbatim}
\begin{code}
module Hack (hack) where
import Data.List
\end{code}

\subsection{Top Level}

Currently we are hacking ways to generalise \texttt{Flash.prism}
from having parameter \texttt{b} fixed equal to 3.
\begin{code}
hack b
 | b < 2 = putStrLn "smcgen with b less than two is somewhat pointless"
 | otherwise = writeFile ("models/gen/Flash"++show b++".prism") $ prismcode b

prismcode b
 = unlines $ intercalate [""]
     [ sem, params b, control
     , mdl b, vars b
     , step1 b, step2 b, step3, step4, step5, step6 b, step7, endm
     , writeable b, dirty b
     , cand b, candidates b, can_erase b
     , diff b, toobig b ]
\end{code}

\begin{prism}
dtmc
\end{prism}
\begin{code}
sem = ["dtmc"]
\end{code}

\subsection{Constant Declarations}

\begin{prism}
const int b=3; // Block Count: Our problematic parameter
const int p; // Pages per Block
const int c; // Number of page writes between wear levelling
const int w; // Maximum wear tolerance (no. of erasures)
const int MAXDIFF; // Maximum desired difference in wear across blocks.
\end{prism}
\begin{code}
params b
  = [ "const int b="++show b++"; // Block Count: Our problematic parameter"
    , "const int p; // Pages per Block"
    , "const int c; // Number of page writes between wear levelling"
    , "const int w; // Maximum wear tolerance (no. of erasures)"
    , "const int MAXDIFF; // Maximum desired difference in wear across blocks."
  ]
\end{code}

\begin{prism}
// control flow
const int INIT = 1;    // startup
const int WRITE = 2;   // page writes
const int SELECT = 3;  // wear-levelling
const int FINISH = 4;  // done: mempory full or worn out
\end{prism}
\begin{code}
control
  = [ "// control flow"
    , "const int INIT = 1;    // startup"
    , "const int WRITE = 2;   // page writes"
    , "const int SELECT = 3;  // wear-levelling"
    , "const int FINISH = 4;  // done: memory full or worn out"
    ]
\end{code}


\subsection{Module Declaration}


\begin{prism}
module Flash
\end{prism}
\begin{code}
mdl b = [ "module Flash"++show b ]
\end{code}


\subsubsection{Variable declarations}

\begin{prism}
// fm_clean_i, for i in 1..b - the number of clean pages in block i
fm_clean_1: [0..p];
fm_clean_2: [0..p];
fm_clean_3: [0..p];
// fm_erase_i, i in 1..b, the number of times block i has been erased.
fm_erase_1: [0..w];
fm_erase_2: [0..w];
fm_erase_3: [0..w];
pc: [INIT..FINISH] init INIT; // program counter
i: [0..c] init 0; // number of page writes done since last wear-levelling.
\end{prism}
\begin{code}
vars :: Int -> [String]
vars b
  = ( ("// fm_clean_i, for i in 1.."++show b++" - no of clean pages in block i")
    : map (idecl "fm_clean_" ": [0..p];") [1..b] )
    ++
    ( ("// fm_erase_i, i in 1.."++show b++", no of times block i has been erased.")
    : map (idecl "fm_erase_" ":[0..w];") [1..b] )
    ++
    [ "pc: [INIT..FINISH] init INIT; // program counter"
    , "i: [0..c] init 0; // number of writes done since last wear-levelling."
    ]

idecl root typ i = root ++ show i ++ typ
\end{code}

\subsubsection{Command Definitions}

\begin{prism}
// Step 1
[] pc=INIT ->
  (fm_clean_1'=p) & (fm_clean_2'=p) & (fm_clean_3'=p) &
  (fm_erase_1'=0) & (fm_erase_2'=0) & (fm_erase_3'=0) &
  (pc'=WRITE);
\end{prism}
\begin{code}
step1 b
  =    "// Step 1"
    :  "[] pc=INIT ->"
    :  (map (iinit "  (fm_clean_" "'=p) &") [1..b])
    ++ (map (iinit "  (fm_erase_" "'=p) &") [1..b])
    ++ [ "  (pc'=WRITE);" ]

iinit root val i = root ++ show i ++ val
\end{code}



\begin{prism}
// Step 2
[] pc=WRITE & i<c & writeable!=0 ->
  (fm_clean_1>0?1/writeable:0): (fm_clean_1'=fm_clean_1-1) & (i'=i+1) +
  (fm_clean_2>0?1/writeable:0): (fm_clean_2'=fm_clean_2-1) & (i'=i+1) +
  (fm_clean_3>0?1/writeable:0): (fm_clean_3'=fm_clean_3-1) & (i'=i+1);
\end{prism}
\begin{code}
step2 b
  =    "// Step 2"
    : "[] pc=WRITE & i<c & writeable!=0 ->"
    : map (iwrite b) [1..b]

iwrite b i
  =     "  (fm_clean_"++show i
     ++ ">0?1/writeable:0): (fm_clean_"++show i
     ++ "'=fm_clean_"++show i
     ++ "-1) & (i'=i+1)"
     ++ addend b i

addend b i = if i == b then ";" else " +"
\end{code}



\begin{prism}
// Step 3
[] pc=WRITE & i<c & writeable=0 -> (pc'=FINISH);
\end{prism}
\begin{code}
step3
  = [ "// Step 3"
    , "[] pc=WRITE & i<c & writeable=0 -> (pc'=FINISH);"
    ]
\end{code}



\begin{prism}
// Step 4
[] pc=WRITE & i=c -> (pc'=SELECT);
\end{prism}
\begin{code}
step4
  = [ "// Step 4"
    , "[] pc=WRITE & i=c -> (pc'=SELECT);"
    ]
\end{code}



\begin{prism}
// Step 5
[] pc=SELECT & (candidates=0 | !can_erase) -> (pc'=FINISH);
\end{prism}
\begin{code}
step5
  = [ "// Step 5"
    , "[] pc=SELECT & (candidates=0 | !can_erase) -> (pc'=FINISH);"
    ]
\end{code}



\begin{prism}
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
\end{prism}
\begin{code}
step6 b
  =    "// Step 6"
    :  "[] pc=SELECT & candidates!=0 & can_erase ->"
    : (concat $ map (ierase $ lst b) $ ndTuples b)

ndTuples n = filter nonDiag $ [(i,j)| i <- [1..n], j <- [1..n]]
nonDiag (i,j) = i /= j

lst n = (n,n-1)

ierase last curr@(from,to)
  = [    "  (cand_"++show from++"_"++show to
      ++ " ? 1/candidates : 0): (fm_clean_"++show to
      ++ "'=fm_clean_"++show to++"-dirty_"++show from++") &"
    ,    "                                 (fm_clean_"++show from
      ++ "'=p) & (fm_erase_"++show from++"'=fm_erase_"++show from++"+1) &"
    ,    "                                 (i'=0) & (pc'=WRITE)"
      ++ addend last curr
    ]
\end{code}



\begin{prism}
// Step 7
[] pc=FINISH -> true;
\end{prism}
\begin{code}
step7
  = [ "// Step 7"
    , "[] pc=FINISH -> true;"
    ]
\end{code}



\begin{prism}
endmodule
\end{prism}
\begin{code}
endm = [ "endmodule" ]
\end{code}

\subsection{Formula Definitions}

\begin{prism}
// a block is writeable if it has at least one clean page
// We need to know how many of these there are.
formula writeable =
  (fm_clean_1!=0 ? 1 : 0) +
  (fm_clean_2!=0 ? 1 : 0) +
  (fm_clean_3!=0 ? 1 : 0);
\end{prism}
\begin{code}
writeable b
  =   "// a block is writeable if it has at least one clean page"
    : "// We need to know how many of these there are."
    : "formula writeable ="
    : map (iwriteable b) [1..b]

iwriteable b i = "  (fm_clean_"++show i++"!=0 ? 1 : 0)" ++ addend b i
\end{code}



\begin{prism}
// dirty_i, for i in 1..b - number of dirty pages in block i
formula dirty_1 = p-fm_clean_1;
formula dirty_2 = p-fm_clean_2;
formula dirty_3 = p-fm_clean_3;
\end{prism}
\begin{code}
dirty b
  =   ( "// dirty_i, for i in 1.."++show b
        ++" - number of dirty pages in block i" )
    : map (idirty b) [1..b]

idirty b i = "formula dirty_"++show i++" = p-fm_clean_"++show i++";"
\end{code}



\begin{prism}
// cand_i_j, for i,j in 1..b, i /= j
//  block i is dirty but there is space in block j for its pages
formula cand_1_2 = dirty_1>0 & fm_clean_2 >= dirty_1;
formula cand_1_3 = dirty_1>0 & fm_clean_3 >= dirty_1;
formula cand_2_1 = dirty_2>0 & fm_clean_1 >= dirty_2;
formula cand_2_3 = dirty_2>0 & fm_clean_3 >= dirty_2;
formula cand_3_1 = dirty_3>0 & fm_clean_1 >= dirty_3;
formula cand_3_2 = dirty_3>0 & fm_clean_2 >= dirty_3;
\end{prism}
\begin{code}
cand b
  =    ( "// cand_i_j, for i,j in 1.."++show b++", i /= j" )
    :  "//  block i is dirty but there is space in block j for its pages"
    : ( map icand $ ndTuples b)

icand (from,to)
 =    "formula cand_"++show from++"_"++show to
   ++ " = dirty_"++show from
   ++ ">0 & fm_clean_"++show to++" >= dirty_"++show from++";"
\end{code}



\begin{prism}
// the number of ways in which we can relocate dirty pages from one block
// to another so we can erase (clean) the first block.
formula candidates =
  (cand_1_2?1:0) + (cand_1_3?1:0) + (cand_2_1?1:0) +
  (cand_2_3?1:0) + (cand_3_1?1:0) + (cand_3_2?1:0);
\end{prism}
\begin{code}
candidates b
  =  "// the number of ways in which we can relocate dirty pages from one block"
   : "// to another so we can erase (clean) the first block."
   : "formula candidates ="
   : ( map (icandidate $ lst b) $ ndTuples b )

icandidate last curr@(from,to)
  =  "  (cand_"++show from++"_"++show to++"?1:0)" ++ addend last curr
\end{code}



\begin{prism}
// true when it is still possibe to erase ANY block,
// without exceeding the maximum allowable erase operations.
formula can_erase =
  fm_erase_1<w &
  fm_erase_2<w &
  fm_erase_3<w;
\end{prism}
\begin{code}
can_erase b
  =   "// true when it is still possibe to erase ANY block,"
    : "// without exceeding the maximum allowable erase operations."
    : "formula can_erase ="
    : map (icanerase b) [1..b]

icanerase b i = "  fm_erase_"++show i++"<w" ++ andend b i

andend b i = if b == i then ";" else " &"
\end{code}



\begin{prism}
// diff_i_j, for i,j in 1..b, i /= j
// the difference in number of erasure of blocks i and j
formula diff_1_2 = fm_erase_1-fm_erase_2;
formula diff_1_3 = fm_erase_1-fm_erase_3;
formula diff_2_1 = fm_erase_2-fm_erase_1;
formula diff_2_3 = fm_erase_2-fm_erase_3;
formula diff_3_1 = fm_erase_3-fm_erase_1;
formula diff_3_2 = fm_erase_3-fm_erase_2;
\end{prism}
\begin{code}
diff b
  =  ( "// diff_i_j, for i,j in 1.."++show b++", i /= j" )
   : "// the difference in number of erasure of blocks i and j"
   : ( map idiff $ ndTuples b )

idiff (i,j)
  =    "formula diff_"++show i++"_"++show j
    ++ " = fm_erase_"++show i++"-fm_erase_"++show j++";"
\end{code}



\begin{prism}
// true if difference in wear equals some limit.
formula toobig =
  diff_1_2 >= MAXDIFF |
  diff_1_3 >= MAXDIFF |
  diff_2_1 >= MAXDIFF |
  diff_2_3 >= MAXDIFF |
  diff_3_1 >= MAXDIFF |
  diff_3_2 >= MAXDIFF;
\end{prism}
\begin{code}
toobig b
  =   "// true if difference in wear equals some limit."
    : "formula toobig ="
    : ( map (itoobig $ lst b) $ ndTuples b )

itoobig last curr@(i,j)
  = "  diff_"++show i++"_"++show j++" >= MAXDIFF" ++ orend last curr

orend last curr = if last == curr then ";" else " |"
\end{code}
