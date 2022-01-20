From Coq Require Import
     Vector.
From Coq Require
     List.
Import VectorNotations.
From ExtLib Require Import
     Functor
     Applicative
     Monad
     StateMonad
     MonadState
     MonadTrans.
From ExtLib.Data.Map Require Import
     FMapAList.
Import MonadNotation.
Open Scope monad_scope.
Existing Instance Monad_stateT.

Module Type Params.
  Parameter wordSize : nat.
  Parameter registerCount : nat.
  (* TODO: proof obligation for the relation, that log equation from the paper*)
End Params.

Definition compose {A B C : Type} (f : B -> C) (g : A -> B) : A -> C := fun (x : A) => f (g x).

Module vnTinyRAMTypes (params : Params).
  Import params.

  Inductive bit : Type :=
  | off
  | on.

  Definition Word : Type := t bit wordSize.

  Definition Register : Type := nat.

  Inductive Flag : Type :=
  | fls
  | tru.

  Inductive TapeType : Type :=
  | auxiliary
  | primary.

  Record InputTape (tapeType : TapeType) : Type :=
   mkInputTape {
       unInputTape : list Word;
     }.

  Definition ProgramCounter : Type := nat.

  Record MachineState : Type :=
    mkMachineState {
        programCounter : ProgramCounter;
        registerValues : alist Register Word;
        conditionFlag : Flag;
        memoryValues : alist nat Word;
        primaryInput : InputTape primary;
        auxiliaryInput : InputTape auxiliary;
      }.

  Class HasMachineState (m : Type -> Type) : Type :=
    {
    getProgramCounter : m ProgramCounter;
    setProgramCounter : ProgramCounter -> m unit;
    getRegisterValue : Register -> m (option Word);
    setRegisterValue : Register -> Word -> m unit;
    getConditionFlag : m Flag;
    setConditionFlag : Flag -> m unit;
    getMemoryValue : nat -> m (option Word);
    setMemoryValue : nat -> Word -> m unit;
    readPrimaryInput : m (option Word);
    readAuxiliaryInput : m (option Word)
    }.

  Record TinyRAMT (m : Type -> Type) (a : Type) : Type :=
    mkTinyRAMT {
        unTinyRAMT : stateT MachineState m a
      }.

  (* instances *)

  (*
  Global Instance monadT_TinyRAMT (m : Type -> Type) : MonadT m (TinyRAMT m) :=
    {
      lift f x := (mkTinyRAMT (lift f))
    }.
   *)
  Global Instance Functor_stateT_MachineState (m : Type -> Type) `{Monad m} : Functor (stateT MachineState m) :=
    {
      fmap _ _ f x := x >>= (compose ret f)
    }.
  Global Instance Functor_TinyRAMT (m : Type -> Type) `{Functor m} `{Functor (stateT MachineState m)} : Functor (TinyRAMT m) :=
    {
      fmap _ _ f := compose (compose (mkTinyRAMT _ _) (fmap f)) (unTinyRAMT _ _)
    }.
  (*
  Global Instance Applicative_TinyRAMT (m : Type -> Type) `{Applicative m} `{Applicative (stateT MachineState m)} : Applicative (TinyRAMT m) :=
    {
      pure _ := compose (mkTinyRAMT m _) pure;
      ap f x := f >>= (fun xf => x >>= (fun xx => ret (xf xx)))
    }.
    *)
  (*
  Global Instance hasMachineState_TRT (m : Type -> Type) `{Monad m} : HasMachineState (TinyRAMT m).
  Proof.
    {
      getProgramCounter := MkTinyRAMT (gets programCounter)
    }.
   *)

  Inductive ImmediateOrRegister : Type :=
  | IsImmediate (w : Word)
  | IsRegister (r : Register).

  Definition conditionToFlag (b : bool) : Flag := match b with
                                               | true => tru
                                               | false => fls
                                               end.

  Definition getImmediateRegister {m : Type -> Type} `{Monad m} `{HasMachineState m} (ior : ImmediateOrRegister) : m (option Word) :=
    match ior with
    | IsImmediate w => ret (Some w)
    | IsRegister r => getRegisterValue r
    end.

End vnTinyRAMTypes.
