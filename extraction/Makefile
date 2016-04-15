# -*- Makefile -*-

# --------------------------------------------------------------------
OCAMLBUILD_BIN   = ocamlbuild -use-ocamlfind
OCAMLBUILD_EXTRA = -classic-display

# In Emacs, use classic display to enable error jumping.
ifeq ($(shell echo $$TERM), dumb)
 OCAMLBUILD_EXTRA += -classic-display
endif
OCAMLBUILD := $(OCAMLBUILD_BIN) $(OCAMLBUILD_EXTRA)

# --------------------------------------------------------------------
.PHONY: all build byte native clean

all: build

build: native

define do-build
	$(OCAMLBUILD) "$(1)"
endef

byte:
	$(call do-build,src/sfeRun.byte)

native:
	$(call do-build,src/sfeRun.native)

dependencies:
	./configure.sh

clean:
	$(OCAMLBUILD) -clean
	rm -f sfeRun.native sfeRun.byte
