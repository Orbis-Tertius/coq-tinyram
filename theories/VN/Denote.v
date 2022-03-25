From ExtLib Require Import
     Monad.
From ITree Require Import
     ITree.
From ITree.Basics Require Import
     CategorySub.
From TinyRAM Require Import
     Types.
From TinyRAM.Utils Require Import
     Fin.
Import Monads.
Import MonadNotation.

(*
Module Denote (Params : TinyRAMParameters).
  Module TRTypes := TinyRAMTypes Params.
  Import TRTypes.

  Local Open Scope monad_scope.

  Context {E' : Type -> Type}.
  Notation E := (MachineState E').
  Context {HasReg : Reg -< E}.
  Context {HasMem : Mem -< E}.
  Context {HasExit : Exit -< E}.
  Context {HasFFlag : FFlag -< E}.
  Context {HasPC : PC -< E}.

  Definition denote_operand (o : Operand) : itree E Word :=
    match o with
    | Oimm v => Ret v
    | Oreg v => trigger (GetReg v)
    end.

  Definition denote_binop (op : Word -> Word -> Word) (ri rj : Register) (o : Operand) : itree E unit :=
    lv <- trigger (GetReg rj) ;;
    rv <- denote_operand o ;;
    let res := op lv rv in
    trigger (SetReg ri res) ;;
    trigger (SetFlag (if iszeroWord res then tru else fls)) ;;
    trigger (IncPc increment_pc).

  Definition denote_andb : Register -> Register -> Operand -> itree E unit :=
    denote_binop (Vector.map2 andbit).

  Definition denote_orb : Register -> Register -> Operand -> itree E unit :=
    denote_binop (Vector.map2 orbit).

  Definition denote_xorb : Register -> Register -> Operand -> itree E unit :=
    denote_binop (Vector.map2 xorbit).

  Definition denote_not (ri : Register) (o : Operand) : itree E unit :=
    rv <- denote_operand o ;;
    let res := Vector.map flipb rv in
    trigger (SetReg ri res) ;;
    trigger (SetFlag (if iszeroWord res then tru else fls)) ;;
    trigger (IncPc increment_pc).

  Definition denote_cmpe (ri : Register) (o : Operand) : itree E unit :=
    lv <- trigger (GetReg ri) ;;
    rv <- denote_operand o ;;
    let flag := forallb (Bool.eqb true) (Vector.map2 bit_eqb lv rv) in
    trigger (SetFlag (conditionToFlag flag)) ;;
    trigger (IncPc increment_pc).

  Set Typeclasses Depth 4.

  Variable o : Operand.
  Variable ri : Register.
  Check Store.
  (*Check rv <- denote_operand o ;; lv <- trigger (GetReg ri) ;; trigger (SetReg rv lv) ;; trigger NullipotentFlag ;; trigger (IncPc increment_pc).*)

  Definition denote_store_b (o : Operand) (ri : Register) : itree E unit :=
    rv <- denote_operand o ;;
    lv <- trigger (GetReg ri) ;;
    let lsb := Vector.nth_order lv Params.H2 in
    (* TODO: interpret a the word rv as an address (a fin of a large number) *)
    trigger NullipotentFlag ;;
    trigger (IncPc increment_pc).

  Definition denote_load_b (ri : Register) (o : Operand) : itree E unit :=
    rv <- trigger (GetReg ri) ;;
    lv <- denote_operand o ;;
    trigger (SetReg rv lv) ;;
    trigger NullipotentFlag ;;
    trigger (IncPc increment_pc).
  (*
  Definition denote_store_w (o : Operand) (ri : Register) : itree E unit :=
    rv <- denote_operand o ;;
    lv <- trigger (GetReg ri) ;;
    trigger (SetReg lv rv) ;;
    trigger NullipotentFlag ;;
    trigger (IncPc increment_pc).
  *)
  Definition denote_instr (i : Instruction) : itree E unit :=
    let ri' := ri i in
    let rj' := rj i in
    let a' := a i in
    match opcode i with
    | exist _ 0 _ => denote_andb ri' rj' a'
    | exist _ 1 _ => denote_orb ri' rj' a'
    | exist _ 2 _ => denote_xorb ri' rj' a'
    | exist _ 3 _ => denote_not ri' a'
    | exist _ 4 _ => Ret tt (* TODO: add *)
    | exist _ 5 _ => Ret tt (* TODO: sub *)
    | exist _ 6 _ => Ret tt (* TODO: mull *)
    | exist _ 7 _ => Ret tt (* TODO: umulh *)
    | exist _ 8 _ => Ret tt (* TODO: smulh *)
    | exist _ 9 _ => Ret tt (* TODO: udiv *)
    | exist _ 10 _ => Ret tt (* TODO: umod *)
    | exist _ 11 _ => Ret tt (* TODO: shl *)
    | exist _ 12 _ => Ret tt (* TODO: shr *)
    | exist _ 13 _ => denote_cmpe ri' a'
    | exist _ 14 _ => Ret tt (* TODO: cmpa *)
    | exist _ 15 _ => Ret tt (* TODO: cmpae *)
    | exist _ 16 _ => Ret tt (* TODO: cmpg *)
    | exist _ 17 _ => Ret tt (* TODO: cmpge *)
    | exist _ 18 _ => Ret tt (* TODO: mov *)
    | exist _ 19 _ => Ret tt (* TODO: cmov *)
    | exist _ 20 _ => Ret tt (* TODO: jmp *)
    | exist _ 21 _ => Ret tt (* TODO: cjmp *)
    | exist _ 22 _ => Ret tt (* TODO: cnjmp *)
    | exist _ 23 _ => denote_store_b a' ri' (* TODO: store.b *)
    | exist _ 24 _ => denote_load_b ri' a'
    | exist _ 25 _ => Ret tt (*denote_store_w a' ri'*) (* TODO: store.w *)
    | exist _ 26 _ => Ret tt (* TODO: load.w *)
    | exist _ 27 _ => Ret tt (* TODO: read *)
    | exist _ 28 _ => Ret tt (* TODO: answer *)
    | exist _ _ _ => Ret tt (* TODO *)
    end.
(*
    Definition denote_instr (i : instr) : itree E unit :=
      match i with
      | Imov d s =>
        v <- denote_operand s ;;
        trigger (SetReg d v)
      | Iadd d l r =>
        lv <- trigger (GetReg l) ;;
        rv <- denote_operand r ;;
        trigger (SetReg d (Vector.map2 orb lv rv))
      | Isub d l r =>
        lv <- trigger (GetReg l) ;;
        rv <- denote_operand r ;;
        trigger (SetReg d (Vector.map2 orb lv rv))
      | Imul d l r =>
        lv <- trigger (GetReg l) ;;
        rv <- denote_operand r ;;
        trigger (SetReg d (Vector.map2 andb lv rv))
      (*| IEq d l r =>
        lv <- trigger (GetReg l) ;;
        rv <- denote_operand r ;;
        trigger (SetReg d (if Nat.eqb lv rv then (onst wordSize) else (offst wordSize)))
      | ILe d l r =>
        lv <- trigger (GetReg l) ;;
        rv <- denote_operand r ;;
        trigger (SetReg d (if Nat.leb lv rv then (onst wordSize) else (offst wordSize))) *)
      | INot d r =>
        rv <- denote_operand r ;;
        trigger (SetReg d (flipWord rv))
      | IAnd d l r =>
        lv <- trigger (GetReg l) ;;
        rv <- denote_operand r ;;
        trigger (SetReg d (Vector.map2 andb lv rv)) ;;
        trigger (SetFlag (if iszeroWord (Vector.map2 andb lv rv) then tru else fls))
      | Iload d addr =>
        val <- trigger (Load addr) ;;
            trigger (SetReg d val)
      | Istore addr v =>
        val <- denote_operand v ;;
            trigger (Store addr val)
      end.
*)
  Definition denote_br {B : Type} (br : branch B) : itree E B :=
    match br with
    | Bjmp l => ret l
    | Bbrz r y n =>
      val <- trigger (GetReg r) ;;
      if iszeroWord val then ret y else ret n
    | Bhalt => exit
    end.

  Fixpoint denote_bk {L : Type} (b : @block L) : itree E L :=
    match b with
    | bbi i b' => denote_instr i ;; denote_bk b'
    | bbb b' => denote_br b'
    end.

  Definition denote_bks {a b : nat} (bs : bks a b) : fin a -> itree E (fin b) :=
    fun x => denote_bk (bs x).

  Definition sub_ktree_fin : nat -> nat -> Type := sub (ktree E) fin.

  Context `{Case_bif : Case nat (sub (ktree E) fin) Nat.add}.
  Context `{Inl_bif : Inl nat (sub (ktree E) fin) Nat.add}.
  Context `{Inr_bif : Inr nat (sub (ktree E) fin) Nat.add}.
  Context `{Iter_bif : Iter nat (sub (ktree E) fin) Nat.add}.

  Definition denote_asm {a b : nat} : asm a b -> sub (ktree E) fin a b :=
    fun s => loop (denote_bks (code s)).

End Denote.
*)
