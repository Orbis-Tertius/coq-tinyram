From Coq Require Import
  VectorDef BinIntDef VectorEq
  Morphisms Setoid RelationClasses.
From ExtLib Require Import
     Monad.
From ITree Require Import
     ITree
     ITreeFacts
     Events.State
     Events.StateFacts.
From ITree.Basics Require Import
     CategorySub.
From TinyRAM.Machine Require Import
  Parameters Words Memory Coding Denotations.
From TinyRAM.Utils Require Import
  Fin Vectors BitVectors.
Import Monads MonadNotation VectorNotations.

Module TinyRAMHandlers (Params : TinyRAMParameters).
  Module TRDen := TinyRAMDenotations Params.
  Import TRDen.
  Export TRDen.

  Local Open Scope monad_scope.

  Record MachineState : Type :=
    mkMachineState {
        (*"""
        The program counter, denoted pc; it consists of [wordSize] bits.
        """*)
        programCounter : Word;
        (*"""
        [registerCount] general-purpose registers, [...]
        """*)
        registers : Registers;
        (*"""
        The (condition) flag [...]; it consists of a single bit.
        """*)
        flag : bool;
        memory : Memory;

        tapeMain : Tape;
        tapeAux : Tape;

        program : Program;
      }.

  Definition updtPC (n : Word) (m : MachineState) : MachineState :=
    match m with
    | {| programCounter := pc0; registers := r0; flag := f0; memory := m0; tapeMain := t0; tapeAux := t1; program := p0|} => 
      {| programCounter := n; registers := r0; flag := f0; memory := m0; tapeMain := t0; tapeAux := t1; program := p0 |}
    end.

  Definition updtReg (n : Registers) (m : MachineState) : MachineState :=
    match m with
    | {| programCounter := pc0; registers := r0; flag := f0; memory := m0; tapeMain := t0; tapeAux := t1; program := p0|} => 
      {| programCounter := pc0; registers := n; flag := f0; memory := m0; tapeMain := t0; tapeAux := t1; program := p0 |}
    end.

  Definition updtFlag (n : bool) (m : MachineState) : MachineState :=
    match m with
    | {| programCounter := pc0; registers := r0; flag := f0; memory := m0; tapeMain := t0; tapeAux := t1; program := p0|} => 
      {| programCounter := pc0; registers := r0; flag := n; memory := m0; tapeMain := t0; tapeAux := t1; program := p0 |}
    end.

  Definition updtMem (n : Memory) (m : MachineState) : MachineState :=
    match m with
    | {| programCounter := pc0; registers := r0; flag := f0; memory := m0; tapeMain := t0; tapeAux := t1; program := p0|} => 
      {| programCounter := pc0; registers := r0; flag := f0; memory := n; tapeMain := t0; tapeAux := t1; program := p0 |}
    end.

  Definition updtMTape (n : Tape) (m : MachineState) : MachineState :=
    match m with
    | {| programCounter := pc0; registers := r0; flag := f0; memory := m0; tapeMain := t0; tapeAux := t1; program := p0|} => 
      {| programCounter := pc0; registers := r0; flag := f0; memory := m0; tapeMain := n; tapeAux := t1; program := p0 |}
    end.

  Definition updtATape (n : Tape) (m : MachineState) : MachineState :=
    match m with
    | {| programCounter := pc0; registers := r0; flag := f0; memory := m0; tapeMain := t0; tapeAux := t1; program := p0|} => 
      {| programCounter := pc0; registers := r0; flag := f0; memory := m0; tapeMain := t0; tapeAux := n; program := p0 |}
    end.

  Definition handle_registers {E: Type -> Type} `{stateE MachineState -< E}: 
    RegisterE ~> itree E :=
  fun _ e =>
    s <- get;;
    let reg := registers s in
    match e in (RegisterE T) return (itree E T) with
    | GetReg x => ret (nth reg x)
    | SetReg x v => put (updtReg (replace reg x v) s)
    end.

  Definition handle_memory {E: Type -> Type} `{stateE MachineState -< E}: 
    MemoryE ~> itree E :=
  fun _ e =>
    s <- get;;
    let m := memory s in
    match e in (MemoryE T) return (itree E T) with
    | LoadByte x => ret (nth m x)
    | StoreByte x v => put (updtMem (replace m x v) s)
    | LoadWord x => ret (Memory_Word_Load m x)
    | StoreWord x v => put (updtMem (Memory_Word_Store m x v) s)
    end.

  (*""" The program counter, denoted pc; it consists of [wordSize] bits. """*)
  Definition handle_programCounter {E: Type -> Type} `{stateE MachineState -< E}: 
    ProgramCounterE ~> itree E :=
  fun _ e =>
    s <- get;;
    let pc := programCounter s in
    match e in (ProgramCounterE T) return (itree E T) with
    | SetPC v => put (updtPC v s)
    | IncPC => put (updtPC (bv_succ pc) s)
    | GetPC => ret pc
    end.

  (*""" The (condition) flag [...]; it consists of a single bit. """*)
  Definition handle_flag {E: Type -> Type} `{stateE MachineState -< E}: 
    FlagE ~> itree E :=
  fun _ e =>
    s <- get;;
    let fl := flag s in
    match e in (FlagE T) return (itree E T) with
    | SetFlag b => put (updtFlag b s)
    | GetFlag => ret fl
    end.

  Definition handle_read {E: Type -> Type} `{stateE MachineState -< E}: 
    ReadE ~> itree E :=
  fun _ e =>
    s <- get;;
    let main := tapeMain s in
    let aux := tapeAux s in
    match e in (ReadE T) return (itree E T) with
    | ReadMain => 
      match main with
      | List.nil => ret None
      | List.cons x xs =>
        put (updtMTape xs s) ;;
        ret (Some x)
      end
    | ReadAux => 
      match aux with
      | List.nil => ret None
      | List.cons x xs =>
        put (updtATape xs s) ;;
        ret (Some x)
      end
    end.

  Definition handle_instruction {E: Type -> Type} `{stateE MachineState -< E}: 
    InstructionE ~> itree E :=
  fun _ e =>
    s <- get;;
    let prog := program s in
    match e in (InstructionE T) return (itree E T) with
    | ReadInst x => 
      match List.nth_error prog x with
      (* """ If pc is not an integer in {0, . . . , L-1}, where L is 
            the number of instructions in [program], then the instruction
            answer 1 is fetched as default. """ *)
      | None => ret (InstructionEncode answer1)
      | Some x => ret x
      end
    end.

  Definition MachineE: Type -> Type :=
    (InstructionE +' ReadE +' FlagE +' ProgramCounterE +' MemoryE +' RegisterE).

  Definition handle_machine {E: Type -> Type} 
      `{stateE MachineState -< E}: 
    MachineE ~> itree E :=
    (case_ handle_instruction 
    (case_ handle_read 
    (case_ handle_flag
    (case_ handle_programCounter 
    (case_ handle_memory handle_registers))))).

  Theorem handle_machine_GetReg : forall r,
    handle_machine _ (subevent _ (GetReg r)) 
    ≅ handle_registers _ (GetReg r).
  Proof. cat_auto. Qed.

  Theorem handle_machine_SetReg : forall r x,
    handle_machine _ (subevent _ (SetReg r x)) 
    ≅ handle_registers _ (SetReg r x).
  Proof. cat_auto. Qed.

  Theorem handle_machine_LoadByte : forall a,
    handle_machine _ (subevent _ (LoadByte a)) 
    ≅ handle_memory _ (LoadByte a).
  Proof. cat_auto. Qed.

  Theorem handle_machine_StoreByte : forall a v,
    handle_machine _ (subevent _ (StoreByte a v)) 
    ≅ handle_memory _ (StoreByte a v).
  Proof. cat_auto. Qed.

  Theorem handle_machine_LoadWord : forall a,
    handle_machine _ (subevent _ (LoadWord a)) 
    ≅ handle_memory _ (LoadWord a).
  Proof. cat_auto. Qed.

  Theorem handle_machine_StoreWord : forall a v,
    handle_machine _ (subevent _ (StoreWord a v)) 
    ≅ handle_memory _ (StoreWord a v).
  Proof. cat_auto. Qed.

  Theorem handle_machine_SetPC : forall a,
    handle_machine _ (subevent _ (SetPC a)) 
    ≅ handle_programCounter _ (SetPC a).
  Proof. cat_auto. Qed.

  Theorem handle_machine_IncPC :
    handle_machine _ (subevent _ IncPC) 
    ≅ handle_programCounter _ IncPC.
  Proof. cat_auto. Qed.

  Theorem handle_machine_GetPC :
    handle_machine _ (subevent _ GetPC) 
    ≅ handle_programCounter _ GetPC.
  Proof. cat_auto. Qed.

  Theorem handle_machine_ReadInst : forall a,
    handle_machine _ (subevent _ (ReadInst a)) 
    ≅ handle_instruction _ (ReadInst a).
  Proof. cat_auto. Qed.

  Theorem handle_machine_GetFlag :
    handle_machine _ (subevent _ GetFlag) 
    ≅ handle_flag _ GetFlag.
  Proof. cat_auto. Qed.

  Theorem handle_machine_SetFlag : forall a,
    handle_machine _ (subevent _ (SetFlag a)) 
    ≅ handle_flag _ (SetFlag a).
  Proof. cat_auto. Qed.

  Theorem handle_machine_ReadMain :
    handle_machine _ (subevent _ ReadMain) 
    ≅ handle_read _ ReadMain.
  Proof. cat_auto. Qed.

  Theorem handle_machine_ReadAux :
    handle_machine _ (subevent _ ReadAux) 
    ≅ handle_read _ ReadAux.
  Proof. cat_auto. Qed.

  Definition machine_h {E: Type -> Type}: 
    (MachineE +' E ~> stateT MachineState (itree E)).
    eapply (cat (C := fun x y => x ~> y)
                (a := (MachineE +' E))
                (b := itree (stateE MachineState +' E))
                (c := stateT MachineState (itree E))).
    - exact (bimap handle_machine (id_ E)).
    - exact run_state.
  Defined.

  Definition interp_machine {E A} (t : itree (MachineE +' E) A) :
    stateT MachineState (itree E) A.
    apply (interp_state machine_h).
    exact t.
  Defined.
  
  (* Equality of machine denotaions. *)
  Definition eq_machine_denotations {E A} (t1 t2 : itree (MachineE +' E) A) : Prop :=
    forall s, interp_machine t1 s ≈ interp_machine t2 s.

  Definition initialState (s : Program) (t0 t1 : Tape) : MachineState :=
    {|(*""" the initial state of the machine is as follows: """*)
      (*""" the contents of pc [...] are all 0; """*)
      programCounter := const b0 _;
      (*""" the contents of [...] all general-purpose registers [...] are all 0; """*)
      registers := const (const b0 _) _;
      (*""" the contents of [...] flag [...] are all 0; """*)
      flag := b0;
      (*""" the contents of [...] memory are all 0; """*)
      memory := const (const b0 _) _;
      tapeMain := t0;
      tapeAux := t1;
      program := s
    |}.

  Definition interp_program {E} (s: Program) (t0 t1 : Tape) : itree E Word :=
    ITree.map snd (interp_machine run (initialState s t0 t1)).

  Definition interp_program_for {E} (n : nat) (s: Program) (t0 t1 : Tape) : itree E (option Word) :=
    ITree.map snd (interp_machine (run_for n) (initialState s t0 t1)).

  (* Equality between programs. *)
  Definition eq_machine (s1 s2 : Program) : Prop :=
    forall t1 t2,
    eq_machine_denotations
      (E := void1)
      (interp_program s1 t1 t2)
      (interp_program s2 t1 t2).

  Section InterpProperties.
    Context {E': Type -> Type}.
    Notation E := (MachineE +' E').

    Global Instance eutt_interp_machine {R}:
    Proper (@eutt E R R eq ==> eq ==> eutt eq) interp_machine.
    Proof.
      repeat intro.
      repeat unfold interp_machine.
      rewrite H0.
      rewrite H.
      reflexivity.
    Qed.

    Global Instance eq_itree_interp_machine {R}:
      Proper (@eq_itree E R R eq ==> eq ==> eq_itree eq) interp_machine.
    Proof. apply eq_itree_interp_state. Qed.


    Global Instance eutt_prod_rel_interp_machine {R} {RR : R -> R -> Prop}:
      Proper (@eutt E R R RR ==> eq ==> eutt (HeterogeneousRelations.prod_rel eq RR)) interp_machine.
    Proof. apply eutt_interp_state. Qed.

    Lemma interp_machine_bind: forall {R S} (t: itree E R) (k: R -> itree E S) (g : MachineState),
      (interp_machine (ITree.bind t k) g)
    ≅ (ITree.bind (interp_machine t g) (fun '(g',  x) => interp_machine (k x) g')).
    Proof.
      intros R S t k g.
      unfold interp_machine.
      rewrite interp_state_bind.
      apply eqit_bind; [ reflexivity | ].
      red; intros [m r].
      reflexivity.
    Qed.

    Lemma interp_machine_ret:
      forall {R : Type} (s : MachineState) (r : R),
      interp_machine (Ret r: itree E R) s ≅ Ret (s, r).
    Proof.
      intros.
      unfold interp_machine.
      destruct s.
      rewrite interp_state_ret.
      reflexivity.
    Qed.

    Lemma interp_machine_tau:
      forall {F : Type -> Type} {T : Type} 
      (t : itree E T) (s : MachineState), 
      interp_machine (Tau t) s ≅ Tau (interp_machine t s).
    Proof.
      intros.
      unfold interp_machine.
      rewrite interp_state_tau.
      reflexivity.
    Qed.

    Lemma interp_machine_trigger : 
      forall (R : Type) (e : E R) (s : MachineState), 
         interp_machine (ITree.trigger e) s ≈ machine_h R e s.
    Proof.
      intros.
      unfold interp_machine.
      rewrite interp_state_trigger.
      reflexivity.
    Qed.

    Lemma interp_machine_trigger_eqit : 
      forall (R : Type) (e : E R) (s : MachineState), 
         interp_machine (ITree.trigger e) s ≅ 
         ITree.bind (machine_h R e s) (fun x : MachineState * R => Tau (Ret x)).
    Proof.
      intros.
      unfold interp_machine.
      rewrite interp_state_trigger_eqit.
      reflexivity.
    Qed.

    Lemma interp_machine_vis:
      forall {T U : Type} (e : E T) (k : T -> itree E U)
         (s : MachineState),
       interp_machine (Vis e k) s
       ≅ ITree.bind (machine_h T e s)
           (fun sx : MachineState * T => Tau (interp_machine (k (snd sx)) (fst sx))).
    Proof.
      intros.
      unfold interp_machine.
      rewrite interp_state_vis.
      reflexivity.
    Qed.

  End InterpProperties.
End TinyRAMHandlers.
