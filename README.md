This repository holds the code for a (re)implementation of MetaOCaml I
did as part of my Master's thesis work at UBC.  The thesis is
available
[from the UBC's cIrcle system](https://open.library.ubc.ca/cIRcle/collections/ubctheses/24/items/1.0166800)
(if the link above is dead, then try
[googling for `"Evgeny Roubinchtein" "IR-MetaOCaml"`](https://www.google.com/#q=%22Evgeny+Roubinchtein%22+%22IR-MetaOCaml%22)).

The main motivation for this work came from me wanting to explore a
particular option for avoiding redundant type-checking in the
MetaOCaml compiler.  The fact that the type checking is redundant was
pointed out in [The MetaOCaml files (2010 ACM SIGPLAN Workshop on ML)](http://okmij.org/ftp/ML/metaocaml-files.pdf).  The
particular strategy that I chose for avoiding redundant type-checking
was to use an OCaml intermediate representation (specifically, values
of type `Lambda`) as the implementation of values of type `code`.

Things that are currently working:

1. "Turn-key" generation of native code.  The generated OCaml code is native code
for the architecture for which native code generation is supported (internally, the implementation hooks into ocamlnat).
2. Cross-stage persistence: values are preserved between the levels
   ("stages" of evaluation).
3. Covers: the example of covers given in [Walid Taha's Ph.D Thesis "Multistage Programming: Its Theory and Applications"](http://www.cs.rice.edu/~taha/teaching/02F/511/papers/msp.pdf) works.

Things that are not currently working:

1. Using "let rec" in the code fragments.  The basic difficulty is the circularity of
   reference required by "let rec", combined with the current implementation strategy
   for cross-stage persistence.

Things that are unlikely to ever work:

1. Presenting terms of type "code" to the programmer in a way the latter can recognize
   as "code written by me, with some mechanical transformations applied."
   I consider this to be a serious limitation, because interactively experimenting
   with fragments of code is extremely valuable for both learning about multi-stage
   programming and debugging multi-stage programs.  This presentation of terms to the
   programmer was not a design goal of the system.
