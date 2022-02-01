From Coq Require Import
     Lia
     String.
From ExtLib Require Import
     RelDec.
From ExtLib.Data Require Import
     String
     Map.FMapAList.
From ITree Require Import
     ITree.
From TinyRAM.Utils Require Import
     Fin.
Definition compose {A B C : Type} (f : B -> C) (g : A -> B) : A -> C := fun (x : A) => f (g x).
Fixpoint forallb {A : Type} {n : nat} (f : A -> bool) (v : Vector.t A n) : bool :=
  match v with
  | Vector.nil _ => true
  | Vector.cons _ x _ xs => andb (f x) (forallb f xs)
  end.

Module Type TinyRAMParameters.
  Parameter (wordSize registerCount : nat).
  Axiom (H0 : exists k, wordSize = 4 * k).
  Axiom H1 : 6 + 2 * Nat.log2 registerCount <= wordSize.
  Definition modulus : nat := Nat.pow 2 wordSize.
  Definition incrAmount : nat := Nat.div wordSize 4.
End TinyRAMParameters.

Module TinyRAMTypes (Params : TinyRAMParameters).
  Import Params.
  Export Params.

  Inductive bit : Type :=
  | off
  | on.

  Fixpoint bit_offs_t (n : nat) : Vector.t bit n :=
    match n with
    | 0 => Vector.nil bit
    | S n' => Vector.cons _ off _ (bit_offs_t n')
    end.

  Fixpoint bit_ons_t (n : nat) : Vector.t bit n :=
    match n with
    | 0 => Vector.nil bit
    | S n' => Vector.cons _ on _ (bit_ons_t n')
    end.

  Definition orbit (x y : bit) : bit :=
    match x, y with
    | off, off => off
    | off, on => on
    | on, off => on
    | on, on => on
    end.

  Definition andbit (x y : bit) : bit :=
    match x, y with
    | off, off => off
    | off, on => off
    | on, off => off
    | on, on => on
    end.

  Definition xorbit (x y : bit) : bit :=
    match x, y with
    | off, off => off
    | off, on => on
    | on, off => on
    | on, on => off
    end.

  Definition bit_eqb (b1 b2 : bit) : bool :=
    match b1, b2 with
    | off, off => true
    | off, on => false
    | on, off => false
    | on, on => true
    end.

  Instance RelDec_bit : RelDec (@eq bit) := { rel_dec := bit_eqb }.

  Definition flipb (b : bit) : bit := match b with | off => on | on => off end.

  Definition Word : Type := Vector.t bit wordSize.
  Definition zeroword : Word := bit_offs_t wordSize.
  Definition iszeroWord (w : Word) : bool := forallb (fun x => bit_eqb x off) w.

  Definition flipWord : Word -> Word := Vector.map flipb.

  Definition Register : Type := fin registerCount.

  (*Definition Address : Type := string.*)

  Definition memorySize : nat := Nat.pow 2 wordSize.
  Definition Address : Type := fin memorySize.
  Definition Byte : Type := Vector.t bit 8.
  Definition zerobyte : Byte := bit_offs_t 8.
  (*Definition Memory : Type := Vector.t (Vector.t bit 8) memorySize.
  Definition MemoryIdx : Type := t memorySize.

  Definition Mem_lookup (m : Memory) (idx : MemoryIdx) : Vector.t bit 8 :=
    Vector.nth m idx.
*)

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
  Instance RelDec_flag : RelDec (@eq Flag) := { rel_dec := flag_eqb }.

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
  Global Arguments unProgramCounter : clear implicits.
(*  Record MachineState : Type :=
    mkMachineState {
        programCounter : ProgramCounter;
        registerValues : alist Register Word;
        conditionFlag : Flag;
        memoryValues : alist Address Word;
        primaryInput : InputTape primary;
        auxiliaryInput : InputTape auxiliary;
      }.
*)
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
    mkAsm {
      internal : nat
    ; code : bks (internal + a) (internal + b)
    }.
  Global Arguments internal {a b}.
  Global Arguments code {a b}.

  Inductive Reg : Type -> Type :=
  | GetReg (r : Register) : Reg Word
  | SetReg (r : Register) (w : Word) : Reg unit.

  Inductive FFlag : Type -> Type :=
  | ReadFlag : FFlag Flag
  | SetFlag (f : Flag) : FFlag unit.

  Inductive Mem : Type -> Type :=
  | Load (r : Address) : Mem Byte
  | Store (r : Address) (b : Byte) : Mem unit.

  Inductive Exit : Type -> Type :=
  | Done : Exit void.

  Definition exit {E A} `{Exit -< E} : itree E A :=
    vis Done (fun v => match v : void with end).

  Definition increment_pc (p : ProgramCounter) : ProgramCounter :=
    let p' := unProgramCounter p in
    mkProgramCounter (Nat.modulo (p' + incrAmount) modulus).

  Inductive PC : Type -> Type :=
  | IncPc (f : ProgramCounter -> ProgramCounter) : PC unit
  | SetPc (p : ProgramCounter) : PC unit
  | GetPc : PC ProgramCounter.

  Definition MachineState (E : Type -> Type) : Type -> Type := Reg +' Mem +' FFlag +' PC +' E.

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

  Instance RelDec_Register : RelDec (@eq Register).
  Proof.
    constructor.
    intros ri rj.
    destruct ri; destruct rj.
    exact (Nat.eqb x x0).
  Qed.

  Instance RelDec_fin_correct (n : nat) {H : RelDec (@eq (fin n))} : RelDec_Correct H.
  Proof.
    (* TODO *)
  Admitted.

  Instance RelDec_Byte : RelDec (@eq Byte).
  Proof.
    constructor.
    intros x y.
    induction x; induction y.
    - exact true.  (* nil case *)
    - exact false.  (* Branch should be unreachable *)
    - exact false.  (* Branch should be unreachable *)
    - exact (andb (bit_eqb h h0) (Bool.eqb IHx IHy)).
  Qed.

  Instance RelDec_Register_correct : RelDec_Correct RelDec_Register.
  Proof.
    constructor.
    intros x y.
    (* TODO *)
  Admitted.

  Instance RelDec_Address : RelDec (@eq Address).
  Proof.
    constructor.
    intros ri rj.
    destruct ri; destruct rj.
    exact (Nat.eqb x x0).
  Qed.

  Instance RelDec_Address_correct : RelDec_Correct RelDec_Address.
  Proof.
    constructor.
    intros a1 a2.
    destruct a1; destruct a2.
    Admitted.

  Instance RelDec_fin1 : RelDec (@eq (fin 1)) :=
    { rel_dec := fun _ _ => true }.

  Definition registers : Type := alist Register Word.
  Definition memory : Type := alist Address Byte.
  (* by convention 0 is the key of the counter, which will mutate *)
  Definition counter : Type := alist (fin 1) ProgramCounter.
  Definition flag : Type := alist (fin 1) Flag.

End TinyRAMTypes.
