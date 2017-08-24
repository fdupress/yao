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

all: sfeRun.native

sfeRun: ecPervasive.cmx lint.cmx ecInt.cmx ecIArray.cmx aesprf.cmx aes.o aes_prf.o SFE.cmx utils.cmx sfeParser.ml sfeParser.cmi sfeParser.cmx sfeLexer.ml sfeLexer.cmx sfeRun.cmx
	$(CAML) $(CCOPT) -Wall $(CCOPT) -O3 $(CCOPT) -maes $(CCOPT) -msse2 $(CCOPT) -msse $(CAMLFLAGS) sfeRun -I $(ZARITH) -I $(GMP) -I $(CRYPTOKIT) $(LINKS) ecPervasive.cmx lint.cmx ecInt.cmx ecIArray.cmx aesprf.cmx SFE.cmx utils.cmx sfeParser.cmx sfeLexer.cmx sfeRun.cmx aes.o aes_prf.o

SFE.cmx: SFE.ml
	$(CAML) -I $(CRYPTOKIT) $(CFLAGS) src/SFE.ml

aes_prf.o: aes_prf.c
	$(CC) $(CFLAGS) $(CINCLUDE) $(INTFLAGS) src/aes_prf.c

aes.o: aes.c
	$(CC) $(CFLAGS) $(CINCLUDE) $(INTFLAGS) src/aes.c

ecBool.cmx: ecBool.ml
	$(CAML) $(CFLAGS) src/ecBool.ml

ecIArray.cmx: ecIArray.ml
	$(CAML) $(CFLAGS) src/ecIArray.ml

ecInt.cmx: ecInt.ml
	$(CAML) $(CFLAGS) src/ecInt.ml

ecPair.cmx: ecInt.ml
	$(CAML) $(CFLAGS) src/ecPair.ml

ecPervasive.cmx: ecInt.ml
	$(CAML) $(CFLAGS) src/ecPervasive.ml

lint.cmx: lint.ml
	$(CAML) -I $(GMP) $(CFLAGS) src/lint.mli src/lint.ml

aesprf.cmx: aesprf.ml
	$(CAML) $(CFLAGS) src/aesprf.ml

sfeLexer.ml: sfeLexer.mll
	$(LEX) src/sfeLexer.mll

sfeLexer.cmx: sfeLexer.ml
	$(CAML) $(CFLAGS) src/sfeLexer.ml

sfeParser.ml: sfeParser.mly
	$(MENHIR) src/sfeParser.mly

sfeParser.cmi: sfeParser.mli
	$(CAML) $(CFLAGS) src/sfeParser.mli

sfeParser.cmx: sfeParser.ml
	$(CAML) $(CFLAGS) src/sfeParser.ml

sfeRun.cmx: sfeRun.ml
	$(CAML) $(CFLAGS) src/sfeRun.ml

utils.cmx: utils.ml
	$(CAML) $(CFLAGS) src/utils.ml

clean:
	rm -f sfeRun.native src/*.cmi src/*.cmx src/*.o src/lexer.ml src/parser.ml src/parser.mli
