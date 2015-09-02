#!/bin/sh

t=${HOME}/src/ocaml
p=${HOME}/src/ocaml

NATMETAOCAML="$t/asmcomp/metaocaml_native.cmx"

NATTOPEXTRA="$t/toplevel/genprintval.cmx $t/toplevel/opttoploop.cmx $t/toplevel/opttopdirs.cmx $t/toplevel/opttopmain.cmx ${NATMETAOCAML}"

NATTOPOBJS="$t/compilerlibs/ocamlcommon.cmxa $t/compilerlibs/ocamloptcomp.cmxa ${NATTOPEXTRA}"
RUN_CODE="$t/asmrun/run_code.d.o"

mode=unknown
for a; do
    case $a in
        -c|-where) mode=compile; break
            ;;
        -o) mode=link; break
                ;;
    esac
done

case $mode in
    compile) $p/ocamlopt.opt $@
             ;;
    link) $p/ocamlopt.opt \
                          $t/otherlibs/dynlink/dynlink.cmxa \
                          $RUN_CODE \
                          $NATTOPOBJS \
                          $@ \
                          -linkall
          ;;
    *) echo The metaocamlopt wrapper script could not determine whether ocamlopt is being called to compile or link 1>&2; exit 1
       ;;
esac
