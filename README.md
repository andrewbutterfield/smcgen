# Statistical Model Checker Generator

Prototype tool to convert parameterised statistical models into the Prism language. The key issue being addressed is where the code structure of the Prism model varies in a non-trivial way with changes to certain parameters, in terms of number and combinations of terms and expressions that are required.

Currently we are looking at *Flash.prism*  - a model of Flash Memory wear-levelling. This has parameters, `b`, `p`, `c`, `w` and `MAXDIFF`. All but `b` can be changed at simulation/analysis time. However changing `b` requires changes to the Prism source. The original model uses `b=3`.

The first approach wasto hack a very direct solution that outputs the bits of `b`-independent code as boilerplate, and then adopts simple code generation very tailored to the *Flash.prism* example. 

The current aim is to generalise this by much more general purpose functions to describe the various aspects of the model.

Then we will try to generalise to find out the key code abstractions, to form a Haskell DSL.

## Installation

The code is written is Haskell, with its build system based on the `stack` tool.

The simplest path is to install `stack` on your system from [https://docs.haskellstack.org/en/stable/README/](https://docs.haskellstack.org/en/stable/README/) and follow guidance on how to ensure that `stack` will install executables somewhere on your `PATH` ([https://docs.haskellstack.org/en/stable/install_and_upgrade/#path](https://docs.haskellstack.org/en/stable/install_and_upgrade/#path)) .

Then, in a command-line/shell window at the top level of this repository, issue the following commands:

`stack test`  --- this builds the app, libraries, test-suite and runs the tests. It may take some time as it may install suitable versions of the haskell compiler and software libraries the first time it is run. Once this is done, subsequent use of this and other stack commands will be much faster.

`stack install` --- this will build the executable if necessary, and then install it, so that it can be run anywhere from the command line.

`smcgen` --- runs the application.

At present the tests are trivial stubs. This should change in the near future.
The application simply runs the latest version (currently Abstraction Level One)
with parameter `b` ranging from 2 to 8.

## Pretty-Printing

This repository contains a Haskell program written as a literate script --- the Haskell source files (`.lhs`)
are also legitimate LaTeX source files. The code and supporting descriptive material can be rendered by using LaTeX/PDFLaTeX in the usual way on the file `MAIN.tex` in the top-level of the respository. Most of the packages used are standard, or supplied in the `doc` folder.

## Contents

At the top-level there are Haskell build files (`stack.yaml`, `smcgen.cabal`,`Setup.hs`,`LICENSE`) and LaTeX top-level files (`MAIN.tex`, `MAIN.bib`).

The `doc` folder contains LaTeX style files and pure LaTeX files.

The `models` folder contains two folders, `init` and `gen`. Folder `init` contains hand-written models, or ones imported from some external source. The `gen` folder contains modules produced by this software.

The `app`, `src` and `test` folders contain Haskell source code. The modules that do the work lie in the `src` folder. At present, these are:

* `Hack` : a quick and dirty way to take the original `init/Flash.prism` model, written with parameter `b` equal to three, and to generalise it to arbitrary `b`, greater than one.


* `Abs1` : (Abstraction Level One) introduces (1) an abstract syntax for a version of Prism extended with arrays, as well as a compiler that converts this to standard Prism (`DSL1`) and (2) the initial Flash model encoded in this abstract syntax using the extended array features (`FlashA1`).

We also have a `Utilities` module that has useful bits of Haskell code.