Require Coq.extraction.Extraction.
Extraction Language Haskell.

From TinyRAM.Machine Require Import
     Parameters Handlers.
Import PeanoNat.Nat.

(* Example archetecture with 4 registers and a wordsize of 16 bits. *)
Module SixteenFour <: TinyRAMParameters.
  Definition wordSizeEighth : nat := 2.
  Definition registerCount : nat := 4.
  Definition wordSize := wordSizeEighth * 8.
  Definition wordSizeLength : nat := 4.
  Theorem wordSizePow2 : wordSize = 2 ^ wordSizeLength.
  Proof. unfold wordSize. simpl. reflexivity. Qed.
  Theorem encodingAxiom : 6 + 2 * log2_up registerCount <= wordSize.
  Proof. unfold registerCount. unfold wordSize. simpl.
         repeat (apply le_S; try apply le_n). Qed.
End SixteenFour.

Module TRHand := TinyRAMHandlers SixteenFour.
Import TRHand.

(*Extraction "tinyram_vm.hs" eval_prog.*)
