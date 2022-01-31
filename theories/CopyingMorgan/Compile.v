From ITree Require Import
     ITree.
From ExtLib Require Import
     Monads.
From TinyRAM.CopyingMorgan Require Import
     CMTypes
     Instructions.

Module eights <: Params.
  Definition wordSize := 8.
  Definition registerCount := 8.
End eights.

Module Import Instructions := vnTinyRAMTypes eights.

Variant Reg : Type -> Type :=
| GetReg (x : Register) : Reg nat
| SetReg (x : Register) (y : nat) : Reg unit.

Inductive Exit : Type -> Type :=
| Done : Exit void.

Definition exit {E A} `{Exit -< E} : itree E A :=
  vis Done (fun v => match v : void with end).
