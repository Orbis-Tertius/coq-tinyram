From vnTinyRAM Require Import
     Types.
From ExtLib Require Import
     Monad.
Import MonadNotation.
Open Scope monad_scope.
Module eights <: Params.
  Definition wordSize := 8.
  Definition registerCount := 8.
End eights.

Module Import Instructions := vnTinyRAMTypes eights.

From Coq Require Import Vector.
Import VectorNotations.

Definition band (b1 b2 : bit) : bit :=
  match b1, b2 with
  | off, off => off
  | off, on => off
  | on, off => off
  | on, on => on
  end.

Definition bor (b1 b2 : bit) : bit :=
  match b1, b2 with
  | off, off => off
  | off, on => on
  | on, off => on
  | on, on => on
  end.

Fixpoint forallb {A : Type} {n : nat} (f : A -> bool) (v : t A n) : bool :=
  match v with
  | nil _ => true
  | cons _ x _ xs => andb (f x) (forallb f xs)
  end.

Definition w1 := [off; off; off; off; on; on; on; on].
Definition w2 := [on; on; on; on; off; off; off; off].

(* You should probably do an instance of a decidable typeclass, is that in extlib??? *)
Definition bit_eqb (b1 b2 : bit) : bool :=
  match b1, b2 with
  | off, off => true
  | off, on => false
  | on, off => false
  | on, on => true
  end.
Notation "b1 '=?' b2" := (bit_eqb b1 b2) (at level 50).

Fixpoint offst (n : nat) : t bit n :=
  match n with
  | 0 => []
  | S n' => cons _ off _ (offst n')
  end.

(* sanitychecks *)
Compute forallb (fun b => b =? off) (map2 band w1 w2).
Compute offst eights.wordSize.

Definition andBits {m : Type -> Type} `{Monad m} `{HasMachineState m} (r1 r2 : Register) (ior : ImmediateOrRegister) : m unit :=
  a' <- getImmediateRegister ior ;;
  r2' <- getRegisterValue r2 ;;
  match a', r2' with
  | Some a'', Some r2'' =>
    let y := map2 band a'' r2'' in
    _ <- setRegisterValue r1 y ;;
    _ <- setConditionFlag (conditionToFlag (forallb (fun b => b =? off) y)) ;;
    ret tt
  | _, _ => ret tt
  end.

Definition orBits {m : Type -> Type} `{Monad m} `{HasMachineState m} (r1 r2 : Register) (ior : ImmediateOrRegister) : m unit :=
  a' <- getImmediateRegister ior ;;
  r2' <- getRegisterValue r2 ;;
  match a', r2' with
  | Some a'', Some r2'' =>
    let y := map2 bor a'' r2'' in
    _ <- setRegisterValue r1 y ;;
    _ <- setConditionFlag (conditionToFlag (forallb (fun b => b =? off) y)) ;;
    ret tt
  | _, _ => ret tt
  end.

Definition jump {m : Type -> Type} `{Monad m} `{HasMachineState m} (ior : ImmediateOrRegister) : m unit :=
  ior' <- getImmediateRegister ior ;;
  match ior' with
  | Some ior'' => setProgramCounter (mkProgramCounter ior'')
  | None => ret tt
  end.
