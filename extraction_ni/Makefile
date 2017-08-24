CC=gcc
CAML=ocamlfind ocamlopt
MENHIR=menhir
LEX=ocamllex
CFLAGS=-c
CAMLFLAGS=-cc gcc -o
GMP=~/.opam/4.02.3/lib/gmp/
CRYPTOKIT=~/.opam/4.02.3/lib/cryptokit/
ZARITH=~/.opam/4.02.3/lib/zarith/
LINKS=-linkpkg -package cryptokit,gmp,bigarray
CINCLUDE=-I`ocamlopt -where`
CCOPT=-ccopt
INTFLAGS=-Wall -O3 -maes -msse2 -msse
SRCINCLUDE=-I src/

all: sfeRun

sfeRun: ecPervasive.cmx lint.cmx ecInt.cmx ecIArray.cmx aesprf.cmx aes.o aes_prf.o SFE.cmx utils.cmx sfeParser.ml sfeParser.cmi sfeParser.cmx sfeLexer.ml sfeLexer.cmx sfeRun.cmx
	$(CAML) $(CCOPT) -Wall $(CCOPT) -O3 $(CCOPT) -maes $(CCOPT) -msse2 $(CCOPT) -msse $(CAMLFLAGS) sfeRun.native -I $(ZARITH) -I $(GMP) -I $(CRYPTOKIT) $(SRCINCLUDE) $(LINKS) src/ecPervasive.cmx src/lint.cmx src/ecInt.cmx src/ecIArray.cmx src/aesprf.cmx src/SFE.cmx src/utils.cmx src/sfeParser.cmx src/sfeLexer.cmx src/sfeRun.cmx src/aes.o src/aes_prf.o

SFE.cmx: src/SFE.ml
	$(CAML) -I $(CRYPTOKIT) $(CFLAGS) $(SRCINCLUDE) src/SFE.ml

aes_prf.o: src/aes_prf.c
	$(CC) $(CFLAGS) $(CINCLUDE) $(INTFLAGS) src/aes_prf.c -o src/aes_prf.o

aes.o: src/aes.c
	$(CC) $(CFLAGS) $(CINCLUDE) $(INTFLAGS) src/aes.c -o src/aes.o

ecBool.cmx: src/ecBool.ml
	$(CAML) $(CFLAGS) $(SRCINCLUDE) src/ecBool.ml

ecIArray.cmx: src/ecIArray.ml
	$(CAML) $(CFLAGS) $(SRCINCLUDE) src/ecIArray.ml

ecInt.cmx: src/ecInt.ml
	$(CAML) $(CFLAGS) $(SRCINCLUDE) src/ecInt.ml

ecPair.cmx: src/ecPair.ml
	$(CAML) $(CFLAGS) $(SRCINCLUDE) src/ecPair.ml

ecPervasive.cmx: src/ecPervasive.ml
	$(CAML) $(CFLAGS) $(SRCINCLUDE) src/ecPervasive.ml

lint.cmx: src/lint.ml
	$(CAML) -I $(GMP) $(CFLAGS) $(SRCINCLUDE) src/lint.mli src/lint.ml

aesprf.cmx: src/aesprf.ml
	$(CAML) $(CFLAGS) $(SRCINCLUDE) src/aesprf.ml

sfeLexer.ml: src/sfeLexer.mll
	$(LEX) src/sfeLexer.mll

sfeLexer.cmx: src/sfeLexer.ml
	$(CAML) $(CFLAGS) $(SRCINCLUDE) src/sfeLexer.ml

sfeParser.ml: src/sfeParser.mly
	$(MENHIR) src/sfeParser.mly

sfeParser.cmi: src/sfeParser.mli
	$(CAML) $(CFLAGS) $(SRCINCLUDE) src/sfeParser.mli

sfeParser.cmx: src/sfeParser.ml
	$(CAML) $(CFLAGS) $(SRCINCLUDE) src/sfeParser.ml

sfeRun.cmx: src/sfeRun.ml
	$(CAML) $(CFLAGS) $(SRCINCLUDE) src/sfeRun.ml

utils.cmx: src/utils.ml
	$(CAML) $(CFLAGS) $(SRCINCLUDE) src/utils.ml

clean:
	rm -f sfeRun.native src/*.cmi src/*.cmx src/*.o src/lexer.ml src/parser.ml src/parser.mli
