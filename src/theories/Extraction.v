Require Coq.extraction.Extraction.
Extraction Language Haskell.

Require Import ExtrHaskellBasic.

From TinyRAM.Machine Require Import
     Parameters Handlers.
Import PeanoNat.Nat BinNat.

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

Extract Inductive Datatypes.nat => "Prelude.Integer" ["0" "succ"]
 "(\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))".
Extract Inductive positive => "Prelude.Integer" [ "((1 Prelude.+) GHC.Base.. (2 Prelude.*))" "(2 Prelude.*)" "1" ]
 "(\fxI fxO xH n -> if n Prelude.== 1 then xH () else 
    ( if (Prelude.mod n 2) Prelude.== 1
      then fxI (Prelude.div (n Prelude.- 1) 2)
      else fxO (Prelude.div n 2)
    )
  )".
Extract Inductive N => "Prelude.Integer" [ "0" "GHC.Base.id" ] 
 "(\fZ fP n -> if n Prelude.== 0 then fZ () else fP n)".
Extract Inductive Z => "Prelude.Integer" [ "0" "GHC.Base.id" "(0 Prelude.-)" ]
 "(\fZ fP fN n -> if n Prelude.== 0 then fZ () else 
    ( if n Prelude.> 0
      then fP n
      else fN (Prelude.abs n)
    )
  )".
Extract Inductive comparison => "Prelude.Ordering" [ "Prelude.EQ" "Prelude.LT" "Prelude.GT" ].
Extract Inductive VectorDef.t => "([])" [ "[]" "(\x _ xs -> x : xs)" ]
  "(\fnil fcons v -> 
     case v of
       [] -> fnil ()
       (x : xs) -> fcons x (Prelude.toInteger (Prelude.length xs)) xs)".

Extraction "Tinyram_VM.hs" interp_program_for.
