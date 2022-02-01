From Coq Require Import
     List.
From TinyRAM Require Import
     Types.
Import ListNotations.

Section Examples.
  Variable (H0 : exists k, wordSize = 4 * k).
  Variable (H1 : 6 + 2 * Nat.log2 registerCount <= wordSize).

  Definition instr : Type := Operand -> Register -> Register -> Instruction.
  Definition Iandb : instr := mkInstruction (mkOpcode 0 (zerolt29 H1)).
  Definition Iorb : instr := mkInstruction (mkOpcode 1 (onelt29 H1)).
  Definition Ixorb : instr := mkInstruction (mkOpcode 2 (twolt29 H1)).
  Definition Inot : instr := mkInstruction (mkOpcode 3 (threelt29 H1)).
  Definition Icmpe : instr := mkInstruction (mkOpcode 13 (thirteenlt29 H1)).

  Definition p1 : list Instruction :=
    [
      (Inot )
    ]
