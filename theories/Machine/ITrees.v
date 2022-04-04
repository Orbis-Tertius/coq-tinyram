From Coq Require Import
  Lia ZArith.Int Numbers.BinNums BinIntDef
  VectorDef VectorEq ProofIrrelevance.
Import BinInt.Z PeanoNat.Nat VectorNotations EqNotations.
From TinyRAM.Utils Require Import
  Vectors BitVectors Fin Arith.
From TinyRAM.Machine Require Import
  Parameters Words Memory Coding.

From ITree Require Import
     ITree
     ITreeFacts
     ITreeMonad
     Basics.Monad
     Basics.CategorySub
     Events.State
     Events.StateFacts.

Module TinyRAMIMach (Params : TinyRAMParameters).
  Module TRMem := TinyRAMMem Params.
  Import TRMem.
  Export TRMem.
  Module TRCod := TinyRAMCoding Params.
  Import TRCod.
  Export TRCod.

  Import Monads.

  Variant RegisterE : Type -> Type :=
  | GetReg (x : Register) : RegisterE Word
  | SetReg (x : Register) (v : Word) : RegisterE unit.

  Variant MemoryE : Type -> Type :=
  | LoadByte  (a : Address) : MemoryE Byte
  | StoreByte (a : Address) (val : Byte) : MemoryE unit
  | LoadWord  (a : Address) : MemoryE Word
  | StoreWord (a : Address) (val : Word) : MemoryE unit.

  Variant ProgramCounterE : Type -> Type :=
  | SetPC (v : Word) : ProgramCounterE unit
  | IncPC : ProgramCounterE unit.

  Variant FlagE : Type -> Type :=
  | GetFlag : FlagE bool
  | SetFlag (b : bool) : FlagE unit.

  Variant AnswerE : Type -> Type :=
  | AnswerWord (v : Word) : AnswerE void.

  Variant ReadE : Type -> Type :=
  | ReadMain : ReadE Byte
  | ReadAux : ReadE Byte.

  Section with_event.
    Context {E : Type -> Type}.
    Context {HasRegister : RegisterE -< E}.
    Context {HasFlag : FlagE -< E}.
    Context {HasProgramCounter : ProgramCounterE -< E}.
    Context {HasMemory : MemoryE -< E}.
    Context {HasAnswer : AnswerE -< E}.
    Context {ReadAnswer : ReadE -< E}.

    Definition denote_operand (o : operand) : itree E Word :=
      match o with
      | inl v => Ret v
      | inr v => trigger (GetReg v)
      end.


End TinyRAMIMach.
