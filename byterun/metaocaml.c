#include <stdlib.h>
#include <stdio.h>
#include "mlvalues.h"
#include "memory.h"
#include "callback.h"

CAMLprim value metaocaml_run_code(value code)
{
  static value * run_code_function = NULL;
  CAMLparam1(code);
  CAMLlocal1(result);
  if (run_code_function == NULL) {
    /* First time around, look up by name */
    run_code_function = caml_named_value("metaocaml load lambda");
  }
  if (run_code_function != NULL) {
     result = caml_callback(*run_code_function, code);
     CAMLreturn(result);
  }
  else
     caml_failwith("metaocaml_run_code: run_code_function is NULL (did Callback.register not get called?)");
}
