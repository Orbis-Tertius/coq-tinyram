From Coq Require Import
     Lia
     List.
From TinyRAM Require
     Types.
From TinyRAM.Utils Require Import
     Fin.
Import ListNotations.

Module TwelveEight <: Types.TinyRAMParameters.
  Definition wordSize : nat := 12.
  Definition registerCount : nat := 8.
  Lemma H0 : exists k, wordSize = 4 * k.
  Proof.
    exists 3.
    unfold wordSize.
    lia.
  Defined.
  Lemma H1 : 6 + 2 * Nat.log2 registerCount <= wordSize.
  Proof.
    unfold wordSize, registerCount.
    simpl.
    lia.
  Defined.
  Lemma H2 : 0 < wordSize. Proof. lia. Defined.
  Lemma H3 : wordSize - 1 < wordSize. Proof. lia. Defined.
  Definition modulus : nat := Nat.pow 2 wordSize.
  Definition incrAmount : nat := Nat.div wordSize 4.
End TwelveEight.

Module TwelveEightTypes := Types.TinyRAMTypes TwelveEight.
Import TwelveEightTypes.

Lemma zerolt8 : 0 < 8. Proof. lia. Qed.
Lemma onelt8 : 1 < 8. Proof. lia. Qed.
Lemma twolt8 : 2 < 8. Proof. lia. Qed.
Lemma threelt8 : 3 < 8. Proof. lia. Qed.
Lemma fourlt8 : 4 < 8. Proof. lia. Qed.
Lemma fivelt8 : 5 < 8. Proof. lia. Qed.
Lemma sixlt8 : 6 < 8. Proof. lia. Qed.
Lemma sevenlt8 : 7 < 8. Proof. lia. Qed.

Definition f1 : Register := exist _ 1 onelt8.
Definition f2 : Register := exist _ 2 twolt8.
Definition f3 : Register := exist _ 3 threelt8.
Definition f4 : Register := exist _ 4 fourlt8.
Definition f5 : Register := exist _ 5 fivelt8.
Definition f6 : Register := exist _ 6 sixlt8.
Definition f7 : Register := exist _ 7 sevenlt8.

Definition instr : Type := Operand -> Register -> Register -> Instruction.
Definition Iandb : instr := mkInstruction (mkOpcode 0 zerolt29).
Definition Iorb : instr := mkInstruction (mkOpcode 1 onelt29).
Definition Ixorb : instr := mkInstruction (mkOpcode 2 twolt29).
Definition Inot : instr := mkInstruction (mkOpcode 3 threelt29).
Definition Icmpe : instr := mkInstruction (mkOpcode 13 thirteenlt29).

Section Examples.
(*
  Definition p1 : list Instruction :=
    [
      (Inot )
    ]
 *)
End Examples.
