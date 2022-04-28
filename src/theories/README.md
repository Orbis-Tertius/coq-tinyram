# `coq-tinyram`

This directory contains the formalization of the TinyRam Harvard architecture.

- `/Utils` contains miscellaneous theorems and functions for dealing with the various datatypes used in the implementation.
- `/Machine` contains the virtual machine implementation.
  - `Parameters.v` contains the parameters required to form the architecture and a few simple theorems. This is primarily the bitwidth of words and the number of registers.
  - `Words.v` and `Memory.v` describe a few virtual-machine specific data structures.
  - `Coding.v` contains an abstract datatype for machine instructions as well as encoding and decoding functions to and from binary. Every line from table 2 in the TinyRAM spec is verified as a theorem here.
  - `Denotations.v` and `Handlers.v` implement the ITrees events and handlers allowing the extracted VM to actually be run.
  - `InstructionTheorems.v` contains most of the formal theorems satisfied by the architecture, verifying that the various instructions do what they're supposed to according to the spec. It also contains proofs that programs halt on answer instructions and don't on non-answer instructions.
- `Extraction.v` contains the code necessary to extract the architecture to Haskell.
- `FibExample.v` contains a fully worked out example of verifying a TinyRAM assembly program implementing the Fibonacci function. The function implemented there is the same as that implemented in `./tinyram_programs/fib_16_4.tr`.
