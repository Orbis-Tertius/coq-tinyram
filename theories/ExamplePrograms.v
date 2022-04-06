From Coq Require Import
     Lia VectorDef VectorEq List.
From TinyRAM.Utils Require Import
     Fin BitVectors.
From TinyRAM.Machine Require Import
     Parameters Coding Handlers.
Import PeanoNat.Nat VectorNotations.

From ITree Require Import
     ITree
     ITreeFacts
     Events.State
     Events.StateFacts.

(* Example archetecture with 4 registers and a wordsize of 16 bits. *)
Module SixteenFour <: TinyRAMParameters.
  Definition wordSizeEighth : nat := 2.
  Definition registerCount : nat := 4.
  Definition wordSize := wordSizeEighth * 8.
  Definition wordSizeLength : nat := 4.
  Theorem wordSizePow2 : wordSize = 2 ^ wordSizeLength.
  Proof. unfold wordSize. simpl. reflexivity. Qed.
  Theorem encodingAxiom : 6 + 2 * log2_up registerCount <= wordSize.
  Proof. unfold registerCount. unfold wordSize. simpl. lia. Qed.
End SixteenFour.

Module TRHand := TinyRAMHandlers SixteenFour.
Import TRHand.

Definition FibProgram : Program.
  apply (List.map InstructionEncode).

  (* Store 1 into address 0001 *)
    (*0: Store 1 into register 00 *)
  apply (cons (movI (bitvector_fin_big [b0; b0]), inl (nat_bitvector_big _ 1))).
    (*1: Store [00] into address 0001 *)
  apply (cons (store_bI (bitvector_fin_big [b0; b0]), inl (nat_bitvector_big _ 1))).

  (*2: Read input from main tape into register 00. *)
  apply (cons (readI (bitvector_fin_big [b0; b0]), inl (nat_bitvector_big _ 0))).

  (*3: Check if 00 is 0*)
  apply (cons (cmpeI (bitvector_fin_big [b0; b0]), inl (nat_bitvector_big _ 0))).

  (*4: If flag is set, jump.*)
  apply (cons (cjmpI, inl (nat_bitvector_big _ 12))).

  (* Read two addresses into registers *)
  (*5: read address 0 into 01 *)
  apply (cons (load_bI (bitvector_fin_big [b0; b1]), inl (nat_bitvector_big _ 0))).
  (*6: read address 1 into 10  *)
  apply (cons (load_bI (bitvector_fin_big [b1; b0]), inl (nat_bitvector_big _ 1))).

  (*7: add two registers together; [01] := [01] + [10] *)
  apply (cons (addI (bitvector_fin_big [b0; b1]) (bitvector_fin_big [b0; b1]),
                    (inr (bitvector_fin_big [b1; b0])))).

  (* Store both registers *)
  (*8: store [10] into adress 0 *)
  apply (cons (store_bI (bitvector_fin_big [b1; b0]), inl (nat_bitvector_big _ 0))).
  (*9: store [01] into adress 1 *)
  apply (cons (store_bI (bitvector_fin_big [b0; b1]), inl (nat_bitvector_big _ 1))).

  (*10: decriment [00] *)
  apply (cons (subI (bitvector_fin_big [b0; b0]) (bitvector_fin_big [b0; b0]),
                    (inl (nat_bitvector_big _ 1)))).

  (*11: jump back to 0 check. *)
  apply (cons (jmpI, inl (nat_bitvector_big _ 3))).

  (*12: Output sum. *)
  apply (cons (answerI, inr (bitvector_fin_big [b1; b0]))).

  apply nil.
Defined.

Definition fibFun (n : nat) : itree void1 Word :=
  eval_prog FibProgram (cons (nat_bitvector_big _ n) nil) nil.
