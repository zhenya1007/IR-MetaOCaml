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

#ifndef NATIVE_CODE

CAMLprim value metaocaml_run_code(value block)
{
  static value * run_code_function = NULL;
  CAMLparam1(block);
  CAMLlocal1(result);
  if (run_code_function == NULL) {
     /* First time around, look up by name */
     run_code_function = caml_named_value("Metaocaml.run_code");
  }
  if (run_code_function != NULL) {
     result = caml_callback(*run_code_function, block);
     CAMLreturn(result);
  }
  else
     caml_failwith("metaocaml_run_code: run_code_function is NULL (did Callback.register not get called?)");
}

/* copied from meta.c:caml_reify_bytecode(), and modified */
CAMLprim value metaocaml_prepare_bytecode(value prog, value len)
{
#ifdef ARCH_BIG_ENDIAN
  caml_fixup_endianness((code_t) prog, (asize_t) Long_val(len));
#endif
#ifdef THREADED_CODE
  caml_thread_code((code_t) prog, (asize_t) Long_val(len));
#endif
  caml_prepare_bytecode((code_t) prog, (asize_t) Long_val(len));
  return Val_unit;
}

#else /* NATIVE_CODE */

CAMLprim value metaocaml_run_code(value block)
{
  static value * run_code_function = NULL;
  CAMLparam1(block);
  CAMLlocal2(code, result);
  if (run_code_function == NULL) {
     /* First time around, look up by name */
     run_code_function = caml_named_value("Metaocaml.run_code");
  }
  if (run_code_function != NULL) {
     /* field 0 is the function label */
     code = Field(block, 1); 
     Field(block, 1) = Val_long(1); /* c.f. the following code in cmmgen.ml:transl
				         | Uclosure(fundecls, clos_vars) ->
					 let block_size =
					 fundecls_size fundecls + List.length clos_vars in
					 let rec transl_fundecls pos = function
					 [...]
					 if f.arity = 1 then
					 header ::
					 Cconst_symbol f.label ::
					 int_const 1 :: (* <---- *)
					 transl_fundecls (pos + 3) rem
				     */
     result = caml_callback(*run_code_function, code);
     CAMLreturn(result);
  }
  else
     caml_failwith("metaocaml_run_code: run_code_function is NULL (did Callback.register not get called?)");
}

#endif /* ? NATIVE_CODE */
