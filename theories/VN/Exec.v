From TinyRAM Require
     Types.
From TinyRAM Require Import
     Combinators.

Module Exec (Params : Types.TinyRAMParameters).
  Module TRCombinators := Combinators Params.
  Import TRCombinators TRInterp TRDenote TRTypes.

End Exec.
