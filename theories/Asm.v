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
     Monad
     RelDec
     Maps.
From ExtLib.Data Require Import
     Map.FMapAList
     String.
From ITree Require Import
     ITree
     ITreeFacts
     ITreeMonad.
From ITree.Basics Require Import
     Monad
     Category
     CategorySub.
From ITree.Events Require Import
     State
     StateFacts
     MapDefault.
Import Vector.VectorNotations.
Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Definition compose {A B C : Type} (f : B -> C) (g : A -> B) : A -> C := fun (x : A) => f (g x).
Definition fin (n : nat) : Type := { x : nat | x < n }.
Fixpoint forallb {A : Type} {n : nat} (f : A -> bool) (v : Vector.t A n) : bool :=
  match v with
  | Vector.nil _ => true
  | Vector.cons _ x _ xs => andb (f x) (forallb f xs)
  end.

Section vnTinyRAM.

  Parameter (wordSize registerCount : nat).
  Definition modulus : nat := Nat.pow 2 wordSize.
  Variable (H0 : exists k, wordSize = 4 * k).
  Definition incrAmount : nat := Nat.div wordSize 4.
  Variable (H1 : 6 + 2 * Nat.log2 registerCount <= wordSize).

  Inductive bit : Type :=
  | off
  | on.

  Fixpoint offst (n : nat) : Vector.t bit n :=
    match n with
    | 0 => []
    | S n' => Vector.cons _ off _ (offst n')
    end.

  Fixpoint onst (n : nat) : Vector.t bit n :=
    match n with
    | 0 => []
    | S n' => Vector.cons _ on _ (onst n')
    end.

  (* You should probably do an instance of a decidable typeclass, is that in extlib??? *)
  Definition bit_eqb (b1 b2 : bit) : bool :=
    match b1, b2 with
    | off, off => true
    | off, on => false
    | on, off => false
    | on, on => true
    end.

  Definition flipb (b : bit) : bit := match b with | off => on | on => off end.

  Definition Word : Type := Vector.t bit wordSize.

  Definition iszeroWord (w : Word) : bool := forallb (fun x => bit_eqb x off) w.

  Definition flipWord : Word -> Word := Vector.map flipb.

  Definition Register : Type := fin registerCount.

  Definition Address : Type := string.

  Inductive Flag : Type :=
  | fls
  | tru.

  Definition flag_eqb (f1 f2 : Flag) : bool :=
    match f1, f2 with
    | fls, fls => true
    | fls, tru => false
    | tru, fls => false
    | tru, tru => true
    end.

  Definition conditionToFlag (b : bool) : Flag :=
    match b with
    | true => tru
    | false => fls
    end.

  Inductive TapeType : Type :=
  | auxiliary
  | primary.

  Record InputTape (tapeType : TapeType) : Type :=
   mkInputTape {
       unInputTape : list Word;
     }.

  Record ProgramCounter : Type :=
    mkProgramCounter {
        unProgramCounter : nat
      }.

  Record MachineState : Type :=
    mkMachineState {
        programCounter : ProgramCounter;
        registerValues : alist Register Word;
        conditionFlag : Flag;
        memoryValues : alist Address Word;
        primaryInput : InputTape primary;
        auxiliaryInput : InputTape auxiliary;
      }.

  Variant Operand : Type :=
  | Oimm (_ : Word)
  | Oreg (_ : Register).

  Record Instruction : Type :=
    mkInstruction {
      opcode : fin 29
    ; a : Operand
    ; ri : Register
    ; rj : Register
      }.

  Lemma zerolt29 : 0 < 29. Proof. lia. Qed.
  Lemma onelt29 : 1 < 29. Proof. lia. Qed.
  Lemma twolt29 : 2 < 29. Proof. lia. Qed.
  Lemma threelt29 : 3 < 29. Proof. lia. Qed.
  Lemma fourlt29 : 4 < 29. Proof. lia. Qed.
  Lemma fivelt29 : 5 < 29. Proof. lia. Qed.
  Lemma sixlt29 : 6 < 29. Proof. lia. Qed.
  Lemma sevenlt29 : 7 < 29. Proof. lia. Qed.
  Lemma eightlt29 : 8 < 29. Proof. lia. Qed.
  Lemma ninelt29 : 9 < 29. Proof. lia. Qed.
  Lemma tenlt29 : 10 < 29. Proof. lia. Qed.
  Lemma elevenlt29 : 11 < 29. Proof. lia. Qed.
  Lemma twelvelt29 : 12 < 29. Proof. lia. Qed.
  Lemma thirteenlt29 : 13 < 29. Proof. lia. Qed.
  Lemma fourteenlt29 : 14 < 29. Proof. lia. Qed.
  Lemma fifteenlt29 : 15 < 29. Proof. lia. Qed.
  Lemma sixteenlt29 : 16 < 29. Proof. lia. Qed.
  Lemma seventeenlt29 : 17 < 29. Proof. lia. Qed.
  Lemma eighteenlt29 : 18 < 29. Proof. lia. Qed.
  Lemma nineteenlt29 : 19 < 29. Proof. lia. Qed.
  Lemma twentylt29 : 20 < 29. Proof. lia. Qed.
  Lemma twentyonelt29 : 21 < 29. Proof. lia. Qed.
  Lemma twentytwolt29 : 22 < 29. Proof. lia. Qed.
  Lemma twentythreelt29 : 23 < 29. Proof. lia. Qed.
  Lemma twentyfourlt29 : 24 < 29. Proof. lia. Qed.
  Lemma twentyfivelt29 : 25 < 29. Proof. lia. Qed.
  Lemma twentysixlt29 : 26 < 29. Proof. lia. Qed.
  Lemma twentysevenlt29 : 27 < 29. Proof. lia. Qed.
  Lemma twentyeightlt29 : 28 < 29. Proof. lia. Qed.

  Definition mkOpcode (n : nat) (H : n < 29) : fin 29 := exist (fun x => x < 29) n H.

  (*
  Variant instr : Type :=
  | Imov   (dest : Register) (src : Operand)
  | Iadd   (dest : Register) (src : Register) (o : Operand)
  | Isub   (dest : Register) (src : Register) (o : Operand)
  | Imul   (dest : Register) (src : Register) (o : Operand)
(*  | IEq    (dest : Register) (src : Register) (o : operand)
  | ILe    (dest : Register) (src : Register) (o : operand) *)
  | IAnd   (dest : Register) (src : Register) (o : Operand)
  | INot   (dest : Register) (o : Operand)
  | Iload  (dest : Register) (addr : Address)
  | Istore (addr : Address) (val : Operand).
   *)
  Variant branch {label : Type} : Type :=
  | Bjmp (_ : label)  (* Jump to label *)
  | Bbrz (_ : Register) (yes no : label)  (* Conditional jump *)
  | Bhalt.

  Global Arguments branch _ : clear implicits.

  Inductive block {label : Type} : Type :=
  | bbi (_ : Instruction) (_ : block)  (* instruction *)
  | bbb (_ : branch label).  (* final branch *)
  Global Arguments block _ : clear implicits.

  Definition bks (a b : nat) : Type := fin a -> block (fin b).

  Record asm (a b : nat) : Type :=
    {
      internal : nat
    ; code : bks (internal + a) (internal + b)
    }.
  Arguments internal {a b}.
  Arguments code {a b}.

  Inductive Reg : Type -> Type :=
  | GetReg (r : Register) : Reg Word
  | SetReg (r : Register) (w : Word) : Reg unit.

  Inductive FFlag : Type -> Type :=
  | ReadFlag : FFlag Flag
  | SetFlag (f : Flag) : FFlag unit.

  Inductive Memory : Type -> Type :=
  | Load (r : Address) : Memory Word
  | Store (r : Address) (w : Word) : Memory unit.

  Inductive Exit : Type -> Type :=
  | Done : Exit void.

  Definition exit {E A} `{Exit -< E} : itree E A :=
    vis Done (fun v => match v : void with end).

  Inductive PC : Type -> Type :=
  | SetPc (p : ProgramCounter) : PC unit
  | GetPc : PC ProgramCounter.

  Definition increment_pc (p : ProgramCounter) : ProgramCounter :=
    let p' := unProgramCounter p in
    mkProgramCounter (Nat.modulo (p' + incrAmount) modulus).

  Section Denote.

    Definition orb (x y : bit) : bit :=
      match x, y with
      | off, off => off
      | off, on => on
      | on, off => on
      | on, on => on
      end.

    Definition andb (x y : bit) : bit :=
      match x, y with
      | off, off => off
      | off, on => off
      | on, off => off
      | on, on => on
      end.

    Definition xorb (x y : bit) : bit :=
      match x, y with
      | off, off => off
      | off, on => on
      | on, off => on
      | on, on => off
      end.

    Context {E : Type -> Type}.
    Context {HasReg : Reg -< E}.
    Context {HasMemory : Memory -< E}.
    Context {HasExit : Exit -< E}.
    Context {HasFFlag : FFlag -< E}.
    Context {HasPC : PC -< E}.

    Definition denote_operand (o : Operand) : itree E Word :=
      match o with
      | Oimm v => Ret v
      | Oreg v => trigger (GetReg v)
      end.

    Definition denote_binop (pc : ProgramCounter) (op : Word -> Word -> Word) (ri rj : Register) (o : Operand) : itree E unit :=
      lv <- trigger (GetReg rj) ;;
      rv <- denote_operand o ;;
      let res := op lv rv in
      trigger (SetReg ri res) ;;
      trigger (SetFlag (if iszeroWord res then tru else fls)) ;;
      trigger (SetPc (increment_pc pc)).

    Definition denote_andb (p : ProgramCounter) : Register -> Register -> Operand -> itree E unit :=
      denote_binop p (Vector.map2 andb).

    Definition denote_orb (p : ProgramCounter) : Register -> Register -> Operand -> itree E unit :=
      denote_binop p (Vector.map2 orb).

    Definition denote_xorb (p : ProgramCounter) : Register -> Register -> Operand -> itree E unit :=
      denote_binop p (Vector.map2 xorb).

    Definition denote_not (p : ProgramCounter) (ri : Register) (o : Operand) : itree E unit :=
      rv <- denote_operand o ;;
      let res := Vector.map flipb rv in
      trigger (SetReg ri res) ;;
      trigger (SetFlag (if iszeroWord res then tru else fls)) ;;
      trigger (SetPc (increment_pc p)).

    Definition denote_cmpe (p : ProgramCounter) (ri : Register) (o : Operand) : itree E unit :=
      lv <- trigger (GetReg ri) ;;
      rv <- denote_operand o ;;
      let flag := forallb (Bool.eqb true) (Vector.map2 bit_eqb lv rv) in
      trigger (SetFlag (conditionToFlag flag)).

    Definition denote_instr (p : ProgramCounter) (i : Instruction) : itree E unit :=
      let ri' := ri i in
      let rj' := rj i in
      let a' := a i in
      match opcode i with
      | exist _ 0 _ => denote_andb p ri' rj' a'
      | exist _ 1 _ => denote_orb p ri' rj' a'
      | exist _ 2 _ => denote_xorb p ri' rj' a'
      | exist _ 3 _ => denote_not p ri' a'
      | exist _ 4 _ => Ret tt (* TODO: add *)
      | exist _ 5 _ => Ret tt (* TODO: sub *)
      | exist _ 6 _ => Ret tt (* TODO: mull *)
      | exist _ 7 _ => Ret tt (* TODO: umulh *)
      | exist _ 8 _ => Ret tt (* TODO: smulh *)
      | exist _ 9 _ => Ret tt (* TODO: udiv *)
      | exist _ 10 _ => Ret tt (* TODO: umod *)
      | exist _ 11 _ => Ret tt (* TODO: shl *)
      | exist _ 12 _ => Ret tt (* TODO: shr *)
      | exist _ 13 _ => denote_cmpe p ri' a'
      | exist _ 14 _ => Ret tt (* TODO: cmpa *)
      | exist _ 15 _ => Ret tt (* TODO: cmpae *)
      | exist _ 16 _ => Ret tt (* TODO: cmpg *)
      | exist _ 17 _ => Ret tt (* TODO: cmpge *)
      | exist _ 18 _ => Ret tt (* TODO: mov *)
      | exist _ 19 _ => Ret tt (* TODO: cmov *)
      | exist _ 20 _ => Ret tt (* TODO: jmp *)
      | exist _ 21 _ => Ret tt (* TODO: cjmp *)
      | exist _ 22 _ => Ret tt (* TODO: cnjmp *)
      | exist _ 23 _ => Ret tt (* TODO: store.b *)
      | exist _ 24 _ => Ret tt (* TODO: load.b *)
      | exist _ 25 _ => Ret tt (* TODO: store.w *)
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

    Fixpoint denote_bk {L : Type} (p : ProgramCounter) (b : @block L) : itree E L :=
      match b with
      | bbi i b' => denote_instr p i ;; denote_bk p b'
      | bbb b' => denote_br b'
      end.

    Definition denote_bks {a b : nat} (p : ProgramCounter) (bs : bks a b) : fin a -> itree E (fin b) :=
      fun x => denote_bk p (bs x).

    Definition sub_ktree_fin : nat -> nat -> Type := sub (ktree E) fin.
    Check Case (sub (ktree E) fin) Nat.add.

    Context `{Case_bif : Case nat (sub (ktree E) fin) Nat.add}.
    Context `{Inl_bif : Inl nat (sub (ktree E) fin) Nat.add}.
    Context `{Inr_bif : Inr nat (sub (ktree E) fin) Nat.add}.
    Context `{Iter_bif : Iter nat (sub (ktree E) fin) Nat.add}.

    Definition denote_asm {a b : nat} (p : ProgramCounter) : asm a b -> sub (ktree E) fin a b :=
      fun s => loop (denote_bks p (code s)).

  End Denote.

  (** ** Interpretation *)
  Instance RelDec_string : RelDec (@eq string) :=
    { rel_dec := fun s1 s2 => if string_dec s1 s2 then true else false }.

  Instance RelDec_string_correct : RelDec_Correct RelDec_string.
  Proof.
    constructor; intros x y.
    split.
    - unfold rel_dec; simpl.
      destruct (string_dec x y) eqn:EQ; [intros _; apply string_dec_sound; assumption | intros abs; inversion abs].
    - intros EQ; apply string_dec_sound in EQ; unfold rel_dec; simpl; rewrite EQ; reflexivity.
  Qed.

  Instance RelDec_reg : RelDec (@eq Register).
  Proof.
    constructor.
    intros ri rj.
    induction ri; induction rj.
    exact (Nat.eqb x x0).
  Qed.

  Definition h_reg {E : Type -> Type} `{mapE Register (offst wordSize) -< E} : Reg ~> itree E :=
    fun _ e =>
      match e with
      | GetReg x => lookup_def x
      | SetReg x v => insert x v
      end.

  Definition h_memory {E : Type -> Type} `{mapE Address (offst wordSize) -< E} : Memory ~> itree E :=
    fun _ e =>
      match e with
      | Load x => lookup_def x
      | Store x v => insert x v
      end.

  Definition registers : Type := alist Register Word.
  Definition memory : Type := alist Address Word.

  Check @denote_asm.

  Locate "+'".
  Check sum1.
  Set Typeclasses Depth 6.

  Check interp.
  Definition interp_asm {E A} (t : itree (Reg +' Memory +' FFlag +' PC +' E) A)
    : memory -> registers -> itree E (memory * (registers * A)) :=
    let h := bimap h_reg (bimap h_memory (id_ _)) in
    let t' := interp h t in
    fun mem regs => interp_map (interp_map t' regs) mem.

  



(*)
  Definition getImmediateRegister {m : Type -> Type} `{Monad m} `{HasMachineState m} (ior : ImmediateOrRegister) : m (option Word) :=
    match ior with
    | IsImmediate w => ret (Some w)
    | IsRegister r => getRegisterValue r
    end.
*)
End vnTinyRAM.
