#!/bin/sh

t=${HOME}/src/ocaml
p=${HOME}/prefix/ocaml-meta/

# echo $t/boot/ocamlrun   $t/ocamlc -I $t/stdlib/ -nostdlib  -c $1 1>&2
# $t/boot/ocamlrun   $t/ocamlc -I $t/stdlib/ -nostdlib  -c $1

$p/bin/ocamlc -c $1

# echo $t/boot/ocamlrun  $t/ocamlc  $t/compilerlibs/ocamlcommon.cma $t/compilerlibs/ocamlbytecomp.cma $t/compilerlibs/ocamltoplevel.cma $t/bytecomp/metaocaml.cmo $(basename $1 .ml).cmo $t/stdlib/stdlib.cma $t/stdlib/std_exit.cmo  -linkall 1>&2
# $t/boot/ocamlrun  $t/ocamlc  -nostdlib $t/compilerlibs/ocamlcommon.cma $t/compilerlibs/ocamlbytecomp.cma $t/compilerlibs/ocamltoplevel.cma $t/bytecomp/metaocaml.cmo $(basename $1 .ml).cmo $t/stdlib/stdlib.cma $t/stdlib/std_exit.cmo  -linkall
# this fails with error "cannot find file: std_exit.cmo" (???)

$p/bin/ocamlc  $t/compilerlibs/ocamlcommon.cma $t/compilerlibs/ocamlbytecomp.cma $t/compilerlibs/ocamltoplevel.cma $t/bytecomp/metaocaml.cmo $(basename $1 .ml).cmo -linkall
