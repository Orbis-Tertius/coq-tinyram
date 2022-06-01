# `coq-tinyram`

This directory contains the Haskell files needed to run the extracted VM. `Tinyram_VM.hs` contains, verbatum with no modifications, the haskell code produced by `Extraction.v`. `Main.hs` implements a simple interactive mode which asks for user inputs whenever the tapes are read.

Example:

```
> cabal new-run coq-tinyram -- tinyram_programs/fib_16_4.tr
Running program tinyram_programs/fib_16_4.tr in interactive mode.

Main Tape Input> 20
	BitString: 0001101001101101
	Nat: 6765
	Int: 6765

> cabal new-run coq-tinyram -- tinyram_programs/fib_16_4.tr -s 100
Running program tinyram_programs/fib_16_4.tr in interactive mode for 100 steps.

Main Tape Input> 20
Error: Program did not halt within 100 steps.

> cabal new-run coq-tinyram -- tinyram_programs/add_16_4.tr tinyram_programs/add/main.tape tinyram_programs/add/aux.tape 20000
Running program tinyram_programs/add_16_4.tr in non-interactive mode with main tape
tinyram_programs/add/main.tape and auxiliary tape tinyram_programs/add/aux.tape for 20000 steps.

	BitString: 0000000001001000
	Nat: 72
	Int: 72
```
