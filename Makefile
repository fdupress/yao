# -*- Makefile -*-

# --------------------------------------------------------------------
ECROOT   ?= 
ECCHECK  ?=
ECARGS   ?=
ECCONF   := config/tests.config 
XUNITOUT ?= xunit.xml
CHECKS   ?= gcircuits

ifeq ($(ECCHECK),)
ifeq ($(ECROOT),)
ECCHECK := ec-runtest
else
PATH    := ${ECROOT}:${PATH}
ECCHECK := $(ECROOT)/scripts/testing/runtest
endif
endif

# --------------------------------------------------------------------
.PHONY: default check check-xunit

default:
	@echo "Usage: make <target> where <target> in [check|check-xunit]" >&2

check:
	$(ECCHECK) --bin-args="$(ECARGS)" $(ECCONF) $(CHECKS)

check-xunit:
	$(ECCHECK) --bin-args="$(ECARGS)" --xunit=$(XUNITOUT) $(ECCONF) $(CHECKS)
