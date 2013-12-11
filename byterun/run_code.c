#include <stdlib.h>
#include <stdio.h>
#include "alloc.h"
#include "mlvalues.h"
#include "memory.h"
#include "callback.h"
#include "fail.h"
#include "config.h"
#include "fix_code.h"
#include "interp.h"

CAMLprim value metaocaml_run_code(value code, value closure)
{
  static value * run_code_function = NULL;
  CAMLparam2(code, closure);
  CAMLlocal1(result);
  if (run_code_function == NULL) {
    /* First time around, look up by name */
    run_code_function = caml_named_value("Metaocaml.run_code");
  }
  if (run_code_function != NULL) {
     result = caml_callback2(*run_code_function, code, closure);
     CAMLreturn(result);
  }
  else
     caml_failwith("metaocaml_run_code: run_code_function is NULL (did Callback.register not get called?)");
}

/* copied from meta.c:caml_reify_bytecode(), and modified */
CAMLprim value metaocaml_replace_code(value prog, value len, value clos)
{
#ifdef ARCH_BIG_ENDIAN
  caml_fixup_endianness((code_t) prog, (asize_t) Long_val(len));
#endif
#ifdef THREADED_CODE
  caml_thread_code((code_t) prog, (asize_t) Long_val(len));
#endif
  caml_prepare_bytecode((code_t) prog, (asize_t) Long_val(len));
  Code_val(clos) = (code_t) prog;
  return clos;
}
