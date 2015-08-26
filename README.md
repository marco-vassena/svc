svc
============

A minimal Structure-aware Version Control system.

Master Thesis Project, Utrecht University 2014.

Abstract
--------
This thesis studies the problem of structure-aware revision control, 
which consists of exploiting the knowledge of the structure of data 
to improve the quality of version control systems. 
Formats are firstly described using an EDSL, which distinguishes meta-data 
from the actual content.  From the unique format specification inverse-by-construction 
parser and printer are derived.
The data stored in a file is converted into a heterogeneous rose tree, 
a generic representation of algebraic data types, used by a diff and diff3 algorithm to 
respectively detect changes and merge revisions. 
Lastly the semantics and the properties of the two algorithms are studied with a formal 
model developed in the Agda proof assistant.

Overview
--------

This project implements the ideas discussed in the thesis:
* An extensible combinator library that unifies parsing and printing 
  for binary and text-based data formats, implemented in Haskell.
* A data-type generic diff and diff3 algorithm for detecting changes
  in data and merging revisions, implemented in Haskell.
* A formal model, developed in the Agda proof assistant, used to describe 
  the diff and diff3 algorithms, show their correctness and to prove several properties about them.

Building
------------------------
The Haskell libraries have been developed using GHC 7.8.3.
The Haskell code can be built with the following commands:
```
$ cabal configure --enable-tests
$ cabal build
```

It is advised to use a sandbox.

The tests can be run also via cabal:
```
$ cabal test
```

The directory data contains some real-world netpbm images used for tests.
Furthermore the directory examples contains additional concrete examples
of simple format descriptions, diff and diff3.
They can be run interactively, e.g. :
```
$ cabal repl
*> :l examples/formats/Csv.hs
*> main
```

The formal model has been developed and type-checked using Agda version 2.4.3
and standard library version 0.9.
The Agda code is found under the directory agda.
The file main rexports all the modules of the model and can be used
to typecheck it all.

# Authors
* Marco Vassena <m.vassena@students.uu.nl>
* Wouter Swierstra <W.S.Swierstra@uu.nl>

