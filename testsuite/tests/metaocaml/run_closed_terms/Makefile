#########################################################################
#                                                                       #
#                                 OCaml                                 #
#                                                                       #
#                 Xavier Clerc, SED, INRIA Rocquencourt                 #
#                                                                       #
#   Copyright 2010 Institut National de Recherche en Informatique et    #
#   en Automatique.  All rights reserved.  This file is distributed     #
#   under the terms of the Q Public License version 1.0.                #
#                                                                       #
#########################################################################

BASEDIR=../../..
include $(BASEDIR)/makefiles/Makefile.toplevel
include $(BASEDIR)/makefiles/Makefile.common
TOPFLAGS = -w A

.PHONY: seed_results
seed_reference:
	@for f in *.ml; do touch $${f}.reference; done
