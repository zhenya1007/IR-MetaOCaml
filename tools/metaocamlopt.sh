#!/bin/sh

t=${HOME}/src/ocaml
p=${HOME}/prefix/ocaml-meta/

UTILS="$t/utils/misc.cmx $t/utils/tbl.cmx $t/utils/config.cmx    $t/utils/clflags.cmx $t/utils/terminfo.cmx $t/utils/ccomp.cmx $t/utils/warnings.cmx    $t/utils/consistbl.cmx"

PARSING="$t/parsing/location.cmx $t/parsing/longident.cmx    $t/parsing/syntaxerr.cmx $t/parsing/parser.cmx    $t/parsing/lexer.cmx $t/parsing/parse.cmx $t/parsing/printast.cmx    $t/parsing/pprintast.cmx    $t/parsing/ast_mapper.cmx"

TYPING="$t/typing/ident.cmx $t/typing/path.cmx    $t/typing/primitive.cmx $t/typing/types.cmx    $t/typing/btype.cmx $t/typing/oprint.cmx    $t/typing/subst.cmx $t/typing/predef.cmx    $t/typing/datarepr.cmx $t/typing/cmi_format.cmx $t/typing/env.cmx    $t/typing/typedtree.cmx $t/typing/printtyped.cmx $t/typing/ctype.cmx    $t/typing/printtyp.cmx $t/typing/includeclass.cmx    $t/typing/mtype.cmx $t/typing/envaux.cmx $t/typing/includecore.cmx    $t/typing/includemod.cmx $t/typing/typetexp.cmx $t/typing/parmatch.cmx    $t/typing/typedtreeIter.cmx $t/typing/typedtreeMap.cmx $t/typing/cmt_format.cmx    $t/typing/stypes.cmx $t/typing/typecore.cmx    $t/typing/typedecl.cmx $t/typing/typeclass.cmx    $t/typing/typemod.cmx"

COMP="$t/bytecomp/lambda.cmx $t/bytecomp/printlambda.cmx    $t/bytecomp/typeopt.cmx $t/bytecomp/switch.cmx $t/bytecomp/matching.cmx    $t/bytecomp/translobj.cmx $t/bytecomp/translcore.cmx    $t/bytecomp/translclass.cmx $t/bytecomp/translmod.cmx    $t/bytecomp/simplif.cmx $t/bytecomp/runtimedef.cmx    $t/driver/pparse.cmx $t/driver/main_args.cmx    $t/driver/compenv.cmx $t/driver/compmisc.cmx"

ASMCOMP="$t/asmcomp/arch.cmx $t/asmcomp/debuginfo.cmx    $t/asmcomp/cmm.cmx $t/asmcomp/printcmm.cmx    $t/asmcomp/reg.cmx $t/asmcomp/mach.cmx $t/asmcomp/proc.cmx    $t/asmcomp/clambda.cmx $t/asmcomp/printclambda.cmx $t/asmcomp/compilenv.cmx    $t/asmcomp/closure.cmx $t/asmcomp/cmmgen.cmx    $t/asmcomp/printmach.cmx $t/asmcomp/selectgen.cmx $t/asmcomp/selection.cmx    $t/asmcomp/comballoc.cmx $t/asmcomp/liveness.cmx    $t/asmcomp/spill.cmx $t/asmcomp/split.cmx    $t/asmcomp/interf.cmx $t/asmcomp/coloring.cmx    $t/asmcomp/reloadgen.cmx $t/asmcomp/reload.cmx    $t/asmcomp/printlinear.cmx $t/asmcomp/linearize.cmx    $t/asmcomp/schedgen.cmx $t/asmcomp/scheduling.cmx    $t/asmcomp/emitaux.cmx $t/asmcomp/emit.cmx $t/asmcomp/asmgen.cmx    $t/asmcomp/asmlink.cmx $t/asmcomp/asmlibrarian.cmx $t/asmcomp/asmpackager.cmx    $t/driver/opterrors.cmx $t/driver/optcompile.cmx"

NATMETAOCAML="$t/asmcomp/metaocaml.cmx"

NATTOPEXTRA="$t/toplevel/genprintval.cmx $t/toplevel/opttoploop.cmx $t/toplevel/opttopdirs.cmx $t/toplevel/opttopmain.cmx ${NATMETAOCAML}"

NATTOPOBJS="${UTILS} ${PARSING} ${TYPING} ${COMP} ${ASMCOMP} ${NATTOPEXTRA}" 

RUN_CODE="$t/byterun/run_code.d.o"

$p/bin/ocamlopt.opt -g -runtime-variant "d" $t/otherlibs/dynlink/dynlink.cmxa $RUN_CODE $NATTOPOBJS $1 -linkall
