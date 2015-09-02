#!/bin/sh
set +x

t=${HOME}/src/ocaml
p=${HOME}/src/ocaml

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
    compile) $p/ocamlc $@
             ;;
    link) $p/ocamlc  $t/compilerlibs/ocamlcommon.cma \
                     $t/compilerlibs/ocamlbytecomp.cma \
                     $t/compilerlibs/ocamltoplevel.cma \
                     $t/bytecomp/metaocaml.cmo \
                     $@ \
                     -linkall
          ;;
    *) echo The metaocamlc wrapper script could not determine whether ocamlc is being called to compile or link 1>&2; exit 1
       ;;
esac
