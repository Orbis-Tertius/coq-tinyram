From Coq Require Import
     Morphisms.
From ExtLib Require Import
     Monad.
From ExtLib.Data.Map Require Import
     FMapAList.
From ITree Require Import
     ITree
     ITreeFacts.
From ITree.Basics Require Import
     (*Monad*)
     Category
     CategoryKleisli
     CategorySub.
From ITree.Events Require Import
     MapDefault.
From TinyRAM Require
     Types.
From TinyRAM.Utils Require Import
     Fin.
From TinyRAM.VN Require Import
     Denote.
Import MonadNotation.


(*
Module Interp (Params : Types.TinyRAMParameters).
  (* Denote Params exports TinyRAMTypes *)
  Module TRDenote := Denote Params.
  Import TRDenote TRTypes.
  Export TRDenote.

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

  Notation E' := TRDenote.E'.
(*  Context {E' : Type -> Type}.
  Notation E := (MachineState E').
  Context {HasReg : Reg -< E}.
  Context {HasMem : Mem -< E}.
  Context {HasExit : Exit -< E}.
  Context {HasFFlag : FFlag -< E}.
  Context {HasPC : PC -< E}.
  Context `{Case_bif : Case nat (sub (ktree E) fin) Nat.add}.
  Context `{Inl_bif : Inl nat (sub (ktree E) fin) Nat.add}.
  Context `{Inr_bif : Inr nat (sub (ktree E) fin) Nat.add}.
  Context `{Iter_bif : Iter nat (sub (ktree E) fin) Nat.add}.*)
  Context `{Initial_al_fin1 : Initial Type alist (fin 1)}.
  Context `{Initial_al_Register : Initial Type alist Register}.
  Context `{Initial_al_Address : Initial Type alist Address}.

  Definition run_asm (p : asm 1 0) : itree E' (counter * (flag * (memory * (registers * fin 0)))) :=
    interp_asm (denote_asm p f0) empty empty empty empty.

  Definition eq_asm_denotations {A B : Type} (t1 t2 : Kleisli (itree E) A B) : Prop :=
    forall a count flg mem regs, interp_asm (t1 a) count flg mem regs ≈ interp_asm (t2 a) count flg mem regs.

  Definition eq_asm {A B} (p1 p2 : asm A B) : Prop :=
    eq_asm_denotations (denote_asm p1) (denote_asm p2).

  Section InterpProperties.

    (** This interpreter is compatible with the equivalence-up-to-tau. *)
    Global Instance eutt_interp_asm {A} :
      Proper (@eutt E A A (@eq A) ==>
                    (@eq counter) ==>
                    (@eq flag) ==>
                    (@eq memory) ==>
                    (@eq registers) ==>
                    @eutt E' (prod counter (prod flag (prod memory (prod registers A)))) (prod _ (prod _ (prod _ (prod _ A)))) eq)
             interp_asm.
    Proof.
      repeat intro.
      subst.
      (* TODO *)
    Admitted.

    (** [interp_asm] commutes with [Ret]. *)
    Lemma interp_asm_ret: forall {R} (r: R) (regs : registers) (mem: memory) (flg : flag) (count : counter),
        @eutt E' _ _ eq (interp_asm (ret r) count flg mem regs)
              (ret (count, (flg, (mem, (regs, r))))).
    Proof.
      unfold interp_asm, interp_map.
      repeat intro.
      unfold ret at 1, Monad_itree.
      (* TODO *)
    Admitted.

    (** [interp_asm] commutes with [bind]. *)
    Lemma interp_asm_bind: forall {R S} (t: itree E R) (k: R -> itree _ S) (regs : registers) (mem: memory) (flg : flag) (count : counter),
        @eutt E' _ _ eq (interp_asm (ITree.bind t k) count flg mem regs)
              (ITree.bind (interp_asm t count flg mem regs) (fun '(count', (flg', (mem', (regs', x)))) => interp_asm (k x) count' flg' mem' regs')).
    Proof.
      (* TODO *)
    Admitted.

  End InterpProperties.
End Interp.
*)
