#!/bin/sh

# -- COMMANDS -- #
COMMAND=command
C_FLAGS=-v

BREW=brew
B_FLAGS=install

APT_GET=apt-get

# -- TO BE INSTALLED -- #
OPAM=opam

OCAML=ocamlfind
OCAML_VERSION=4.02.1

DEPENDENCIES="menhir cryptokit mlgmp"

if ! $COMMAND $C_FLAGS $OPAM &> /dev/null ; then
    echo $OPAM not found! Installing...
    if [ "$(uname)" == "Darwin" ]; then
	$BREW $B_FLAGS $OPAM
    $BREW link $OPAM
    elif [ "$(expr substr $(uname -s) 1 5)" == "Linux" ]; then
	$APT_GET $B_FLAGS $OPAM
    fi
    $OPAM init
else
    echo $OPAM installed! Proceding...
fi

if !  $COMMAND $C_FLAGS $OCAML &> /dev/null ; then
    echo $OCAML not found! Installing...
    $OPAM switch $OCAML_VERSION
    eval 'opam config env'
else
    echo $OCAML installed! Proceding...
fi

$OPAM $B_FLAGS $DEPENDENCIES

