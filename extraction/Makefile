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

p2stage1:
	$(call do-build,src/p2_stage1.native)

p1stage1:
	$(call do-build,src/p1_stage1.native)

p2stage2:
	$(call do-build,src/p2_stage2.native)

p1stage2:
	$(call do-build,src/p1_stage2.native)

stages: p2stage1 p1stage1 p2stage2 p1stage2

clean:
	$(OCAMLBUILD) -clean
	rm -f sfeRun.native sfeRun.byte
