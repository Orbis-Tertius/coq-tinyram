(* This approach is based on https://github.com/DeepSpec/InteractionTrees/blob/master/tutorial/Asm.v *)
From Coq Require Import
     String
     Lia.
From Coq.Vectors Require Import
     Fin.
From Coq Require
     List
     Vector.
From ExtLib Require Import
     Monad.
From ExtLib.Data Require Import
     Map.FMapAList.
From ITree Require Import
     ITree.
From ITree.Basics Require Import
     Monad
     CategorySub.
From ITree.Events Require Import
     MapDefault.
From TinyRAM Require Import
     Types.
From TinyRAM.VN Require Import
     Denote.

(*Import Monads.*)
Import MonadNotation.

Section Interp.
  Local Open Scope monad_scope.

  Existing Instance RelDec_Register.
  Existing Instance RelDec_Address.
  Existing Instance RelDec_fin1.

  Definition h_reg {E' : Type -> Type} `{mapE Register zeroword -< E'} : Reg ~> itree E' :=
    fun _ e =>
      match e with
      | GetReg x => lookup_def x
      | SetReg x v => insert x v
      end.

  Definition h_memory {E' : Type -> Type} `{mapE Address zerobyte -< E'} : Mem ~> itree E' :=
    fun _ e =>
      match e with
      | Load x => lookup_def x
      | Store x v => insert x v
      end.

  Definition h_programcounter {E' : Type -> Type} `{mapE (fin 1) (mkProgramCounter 0) -< E'} : PC ~> itree E' :=
    fun _ e =>
      match e with
      | IncPc f => x <- lookup_def f0 ;; insert f0 (f x)
      | SetPc x => insert f0 x
      | GetPc => lookup_def f0
      end.

  Definition h_flag {E' : Type -> Type} `{mapE (fin 1) fls -< E'} : FFlag ~> itree E' :=
    fun _ e =>
      match e with
      | ReadFlag => lookup_def f0
      | SetFlag x => insert f0 x
      end.

  Definition interp_asm {E' : Type -> Type} {A : Type} (t : itree (MachineState E') A)
    : counter -> flag -> memory -> registers -> itree E' (counter * (flag * (memory * (registers * A)))) :=
    let h := bimap h_reg (bimap h_memory (bimap h_flag (bimap h_programcounter (id_ _)))) in
    let t' := interp h t in
    fun count flg mem regs => interp_map (interp_map (interp_map (interp_map t' regs) mem) flg) count.

  Context {E' : Type -> Type}.
  Notation E := (MachineState E').
  Context {HasReg : Reg -< E}.
  Context {HasMem : Mem -< E}.
  Context {HasExit : Exit -< E}.
  Context {HasFFlag : FFlag -< E}.
  Context {HasPC : PC -< E}.
  Context `{Case_bif : Case nat (sub (ktree E) fin) Nat.add}.
  Context `{Inl_bif : Inl nat (sub (ktree E) fin) Nat.add}.
  Context `{Inr_bif : Inr nat (sub (ktree E) fin) Nat.add}.
  Context `{Iter_bif : Iter nat (sub (ktree E) fin) Nat.add}.
  Context `{Initial_al_fin1 : Initial Type alist (fin 1)}.
  Context `{Initial_al_Register : Initial Type alist Register}.
  Context `{Initial_al_Address : Initial Type alist Address}.

  Definition run_asm (p : asm 1 0) : itree E' (counter * (flag * (memory * (registers * fin 0)))) := interp_asm (denote_asm p f0) empty empty empty empty.

End Interp.
