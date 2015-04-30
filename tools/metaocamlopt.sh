#!/bin/sh

t=${HOME}/src/ocaml
p=${HOME}/src/ocaml

NATMETAOCAML="$t/asmcomp/metaocaml_native.cmx"

NATTOPEXTRA="$t/toplevel/genprintval.cmx $t/toplevel/opttoploop.cmx $t/toplevel/opttopdirs.cmx $t/toplevel/opttopmain.cmx ${NATMETAOCAML}"

NATTOPOBJS="$t/compilerlibs/ocamlcommon.cmxa $t/compilerlibs/ocamloptcomp.cmxa ${NATTOPEXTRA}" 
RUN_CODE="$t/asmrun/run_code.d.o"

$p/bin/ocamlopt.opt -g -runtime-variant "d" $t/otherlibs/dynlink/dynlink.cmxa $RUN_CODE $NATTOPOBJS $1 -linkall
