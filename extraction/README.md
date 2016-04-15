Installing requirements
====================================================================

In order to be able to run our benchmark, the following third-party
tools/libraries are needed:

	* OCaml (>= 4.02)
	  Available at [http://caml.inria.fr/]

	* menhir
	  Available at [http://gallium.inria.fr/~fpottier/menhir]

	* cryptokit (=1.10)
	  Available at [https://forge.ocamlcore.org/projects/cryptokit/]

	* GMP
	  Available at [https://gmplib.org]

	* mlgmp
	  Available at [http://www-verimag.imag.fr/~monniaux/download/]

Installing requirements using OPAM (preferred)
--------------------------------------------------------------------

All the above mentioned requirements can be installed using OPAM. OPAM
is the OCaml packages manager.

	0. Installing OPAM and OCaml
	   OPAM can be installed via any system packages management, like brew or
	   apt-get.
		   $> brew install opam
		   or
		   $> apt-get install opam
	   The commands above already install an OCaml distribution. However,
	   it is possible to switch to a dedicated compiler by doing:
		   $> opam switch $OVERSION
		   where $OVERSION is a valid OCaml version (e.g. 4.02.1)

	1. Installing menhir
	   $> opam install menhir

	2. Installing cryptokit
	   $> opam install cryptokit

	3. Installing mlgmp
	   $> opam install mlgmp

See [https://opam.ocaml.org/doc/Install.html] for how to install OPAM.
See [https://opam.ocaml.org/doc/Usage.html] for how to initialize
OPAM.

Optinally, we provide a script to install the dependencies
automatically. This script however does not contemplates the
installation of external dependencies. Just do
	$> make dependencies


Compilation
====================================================================

The shell command
	$> make
should build the Yao's protocol analyser and create an exectutable
'sfeRun.native '.

Execution
====================================================================

'sfeRun.native' can be called with any circuit file in 'data'
folder and it will output the time results when evaluating the circuit
using our Yao's protocol analyser.

Additionally, we provide a script 'benchmark' in the 'data' folder
that runs 'sfeRun.native' on every circuit in the folder and produces
a '.csv' file with the evaluation results.

Circuit generation
====================================================================

We provide a simple circuit generator script that, given a text decription of
a circuit, produces a circuit file that is readable by our
evaluator. It can be found in the 'circuits' folder and it is called
'sfe_example_generator.py'. This folder also contemplates a series of
examples of circuits described in '.txt' files.
