From Coq Require Import
  ZArith.Int VectorDef BinIntDef VectorEq.
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
Import BinInt.Z PeanoNat.Nat Monads MonadNotation VectorNotations.

Module TinyRAMHandlers (Params : TinyRAMParameters).
  Module TRDen := TinyRAMDenotations Params.
  Import TRDen.
  Export TRDen.

  Local Open Scope monad_scope.

  Definition Program : Type := list (Word * Word).
  Definition Tape : Type := list Word.
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
        registers : Vector.t Word registerCount;
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

  Definition handle_programCounter {E: Type -> Type} `{stateE nat -< E}: 
    ProgramCounterE ~> itree E :=
  fun _ e =>
    match e in (ProgramCounterE T) return (itree E T) with
    | SetPC v => put v
    | IncPC => pc <- get;;
               put (S pc)
    | GetPC => get
    end.

  Definition interp_programCounter {E A} (t : itree (ProgramCounterE +' E) A) :
    stateT nat (itree E) A :=
  run_state (interp (bimap handle_programCounter (id_ E)) t).

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

  Definition eval_prog (s: Program) (t1 t2 : Tape) : itree void1 Word :=
    let E : Type -> Type := void1 in 
    state <- ((run_state (run_state (run_state (run_state (run_state (run_state
              (interp
              (bimap handle_instruction (bimap handle_read (bimap handle_flag
              (bimap handle_programCounter (bimap handle_memory (bimap handle_registers
              (id_ E)))))))
              run) 
              s) (t1, t2)) b0) 0) (const (const b0 _) _)) (const (const b0 _) _))) ;;
    ret (snd (snd (snd (snd (snd (snd state)))))).

End TinyRAMHandlers.
