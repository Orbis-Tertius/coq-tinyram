From vnTinyRAM Require Import
     Types.

Module eights <: Params.
  Definition wordSize := 8.
  Definition registerCount := 8.
End eights.

Module Import Instructions := vnTinyRAMTypes eights.

From Coq Require Import Vector.
