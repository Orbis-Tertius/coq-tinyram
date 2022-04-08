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

  Definition Program : Type := list (Word * Word).
  Definition Tape : Type := list Word.
  (*""" [registerCount] general-purpose registers, [...] """*)
  Definition Registers : Type := Vector.t Word registerCount.

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
        conditionFlag : bool;
        memory : Memory;

        tapeMain : Tape;
        tapeAux : Tape;

        program : Program;
      }.

  Definition handle_registers {E: Type -> Type} `{stateE Registers -< E}: 
    RegisterE ~> itree E :=
  fun _ e =>
    reg <- get;;
    match e in (RegisterE T) return (itree E T) with
    | GetReg x => ret (nth reg x)
    | SetReg x v => put (replace reg x v)
    end.

  Definition interp_registers {E A} (t : itree (RegisterE +' E) A) :
    stateT Registers (itree E) A :=
  run_state (interp (bimap handle_registers (id_ E)) t).

  Definition handle_memory {E: Type -> Type} `{stateE Memory -< E}: 
    MemoryE ~> itree E :=
  fun _ e =>
    m <- get;;
    match e in (MemoryE T) return (itree E T) with
    | LoadByte x => ret (nth m x)
    | StoreByte x v => put (replace m x v)
    | LoadWord x => ret (Memory_Word_Load m x)
    | StoreWord x v => put (Memory_Word_Store m x v)
    end.

  Definition interp_memory {E A} (t : itree (MemoryE +' E) A) :
    stateT Memory (itree E) A :=
  run_state (interp (bimap handle_memory (id_ E)) t).

  (*""" The program counter, denoted pc; it consists of [wordSize] bits. """*)
  Definition handle_programCounter {E: Type -> Type} `{stateE Word -< E}: 
    ProgramCounterE ~> itree E :=
  fun _ e =>
    match e in (ProgramCounterE T) return (itree E T) with
    | SetPC v => put v
    | IncPC => pc <- get;;
               put (bv_incr 1 pc)
    | GetPC => get
    end.

  Definition interp_programCounter {E A} (t : itree (ProgramCounterE +' E) A) :
    stateT Word (itree E) A :=
  run_state (interp (bimap handle_programCounter (id_ E)) t).

  (*""" The (condition) flag [...]; it consists of a single bit. """*)
  Definition handle_flag {E: Type -> Type} `{stateE bool -< E}: 
    FlagE ~> itree E :=
  fun _ e =>
    match e in (FlagE T) return (itree E T) with
    | SetFlag b => put b
    | GetFlag => get
    end.

  Definition interp_flag {E A} (t : itree (FlagE +' E) A) :
    stateT bool (itree E) A :=
  run_state (interp (bimap handle_flag (id_ E)) t).

  Definition handle_read {E: Type -> Type} `{stateE (Tape * Tape) -< E}: 
    ReadE ~> itree E :=
  fun _ e =>
    tapes <- get;;
    let (main, aux) := (tapes : Tape * Tape) in
    match e in (ReadE T) return (itree E T) with
    | ReadMain => 
      match main with
      | List.nil => ret None
      | List.cons x xs =>
        put (xs, aux) ;;
        ret (Some x)
      end
    | ReadAux => 
      match aux with
      | List.nil => ret None
      | List.cons x xs =>
        put (main, xs) ;;
        ret (Some x)
      end
    end.

  Definition interp_read {E A} (t : itree (ReadE +' E) A) :
    stateT (Tape * Tape) (itree E) A :=
  run_state (interp (bimap handle_read (id_ E)) t).

  Definition handle_instruction {E: Type -> Type} `{stateE Program -< E}: 
    InstructionE ~> itree E :=
  fun _ e =>
    match e in (InstructionE T) return (itree E T) with
    | ReadInst x => 
      prog <- get;;
      match List.nth_error prog x with
      (* """ If pc is not an integer in {0, . . . , L-1}, where L is 
            the number of instructions in [program], then the instruction
            answer 1 is fetched as default. """ *)
      | None => ret (InstructionEncode answer1)
      | Some x => ret x
      end
    end.

  Definition interp_instruction {E A} (t : itree (InstructionE +' E) A) :
    stateT Program (itree E) A :=
  run_state (interp (bimap handle_instruction (id_ E)) t).

  Definition MachineE: Type -> Type :=
    (InstructionE +' ReadE +' FlagE +' ProgramCounterE +' MemoryE +' RegisterE).

  Definition handle_machine {E: Type -> Type} 
      `{stateE Registers -< E}
      `{stateE Memory -< E}
      `{stateE Word -< E}
      `{stateE bool -< E}
      `{stateE (Tape * Tape) -< E}
      `{stateE Program -< E}:
    MachineE ~> itree E.
    intros T X.
    apply (Handler.case_ handle_instruction 
          (Handler.case_ handle_read 
          (Handler.case_ handle_flag
          (Handler.case_ handle_programCounter 
          (Handler.case_ handle_memory handle_registers))))).
    exact X.
  Defined.

  Definition itree_assoc_r {a b c} :
    itree ((a +' b) +' c) ~> itree (a +' b +' c).
    apply translate.
    apply (assoc_r (C := (fun x y => x ~> y))).
  Defined.

  Definition interp_machine_f {A}
    (p : Program * (Tape * Tape * (bool * (Word * (Memory * (Registers * A)))))):
    MachineState * A :=
  match p with
  | (p0, ((t0, t1), (f0, (pc0, (m0, (r0, a)))))) =>
    ({|
      programCounter := pc0;
      registers := r0;
      conditionFlag := f0;
      memory := m0;
      tapeMain := t0;
      tapeAux := t1;
      program := p0
     |}, a)
  end.

  Definition interp_machine {E A} (t : itree (MachineE +' E) A) :
    stateT MachineState (itree E) A.
    remember (interp (bimap handle_machine (id_ E)) t) as v; clear Heqv.
    intro m; destruct m.
    apply itree_assoc_r,
          (fun x => run_state x registers0),
          itree_assoc_r,
          (fun x => run_state x memory0),
          itree_assoc_r,
          (fun x => run_state x programCounter0),
          itree_assoc_r,
          (fun x => run_state x conditionFlag0),
          itree_assoc_r,
          (fun x => run_state x (tapeMain0, tapeAux0)),
          (fun x => run_state x program0) in v.
    exact (ITree.map interp_machine_f v).
  Defined.


  Definition machine_h {E}: (MachineE +' E ~> stateT MachineState (itree E)).
    intros T X.
    apply interp_machine.
    exact (trigger X).
  Defined.

  Definition eval_prog (s: Program) (t0 t1 : Tape) : itree void1 Word.
    remember ({|(*""" the initial state of the machine is as follows: """*)
              (*""" the contents of pc [...] are all 0; """*)
              programCounter := const b0 _;
              (*""" the contents of [...] all general-purpose registers [...] are all 0; """*)
              registers := const (const b0 _) _;
              (*""" the contents of [...] flag [...] are all 0; """*)
              conditionFlag := b0;
              (*""" the contents of [...] memory are all 0; """*)
              memory := const (const b0 _) _;
              tapeMain := t0;
              tapeAux := t1;
              program := s
            |}: MachineState) as init; clear Heqinit.
    exact (ITree.map snd (interp_machine run init)).
  Defined.

  Section InterpProperties.
    Context {E': Type -> Type}.
    Notation E := (MachineE +' E').

    Global Instance eutt_interp_machine {R}:
    Proper (@eutt E R R eq ==> eq ==> @eutt E' (prod MachineState R) (prod _ R) eq)
           interp_machine.
    Proof.
      repeat intro.
      repeat unfold interp_machine.
      rewrite H0.
      destruct y0.
      rewrite H.
      reflexivity.
    Qed.

    Lemma interp_machine_bind: forall {R S} (t: itree E R) (k: R -> itree E S) (g : MachineState),
      (interp_machine (ITree.bind t k) g)
    ≅ (ITree.bind (interp_machine t g) (fun '(g',  x) => interp_machine (k x) g')).
    Proof.
      intros.
      destruct g; simpl.
      rewrite interp_bind.
      unfold itree_assoc_r, run_state.
      repeat rewrite translate_bind, interp_state_bind.
      rewrite interp_state_bind, map_bind, bind_map.
      apply eqit_bind; [ reflexivity | ].
      red; intros [p0 [[t0 t1] [f0 [pc0 [m0 [r0 a]]]]]].
      reflexivity.
    Qed.

    Lemma interp_machine_ret:
      forall {R : Type} (s : MachineState) (r : R),
      interp_machine (Ret r: itree E R) s ≅ Ret (s, r).
    Proof.
      intros.
      unfold interp_machine.
      destruct s.
      rewrite interp_ret.
      unfold itree_assoc_r, run_state.
      repeat rewrite translate_ret, interp_state_ret.
      rewrite interp_state_ret, map_ret.
      reflexivity.
    Qed.

    Lemma interp_machine_tau:
      forall {F : Type -> Type} {T : Type} 
      (t : itree E T) (s : MachineState), 
      interp_machine (Tau t) s ≅ Tau (interp_machine t s).
    Proof.
      intros.
      unfold interp_machine.
      destruct s.
      rewrite interp_tau.
      unfold itree_assoc_r, run_state.
      repeat rewrite translate_tau, interp_state_tau.
      rewrite interp_state_tau, map_tau.
      reflexivity.
    Qed.

  End InterpProperties.
End TinyRAMHandlers.
