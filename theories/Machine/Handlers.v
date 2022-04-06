From Coq Require Import
  ZArith.Int VectorDef BinIntDef VectorEq.
From ExtLib Require Import
     Monad.
From ITree Require Import
     ITree Simple.
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

        tapeMain : list Word;
        tapeAux : list Word;

        program : list (Word * Word);
      }.

  Definition handle_registers R (e : RegisterE R) :
    Monads.stateT MachineState (itree void1) R := 
    fun m =>
    match e with
    | GetReg x => ret (m, nth (registers m) x)
    | SetReg x v => 
        match m with
        | {|
            programCounter := programCounter0;
            registers := registers0;
            conditionFlag := conditionFlag0;
            memory := memory0;
            tapeMain := tapeMain0;
            tapeAux := tapeAux0;
            program := program0
          |} =>
            ret ({|
              programCounter := programCounter0;
              registers := replace registers0 x v;
              conditionFlag := conditionFlag0;
              memory := memory0;
              tapeMain := tapeMain0;
              tapeAux := tapeAux0;
              program := program0
            |}, tt)
        end
    end.

  Definition handle_memory R (e : MemoryE R) :
    Monads.stateT MachineState (itree void1) R := 
    fun m =>
    match e with
    | LoadByte x => ret (m, nth (memory m) x)
    | StoreByte x v => 
        match m with
        | {|
            programCounter := programCounter0;
            registers := registers0;
            conditionFlag := conditionFlag0;
            memory := memory0;
            tapeMain := tapeMain0;
            tapeAux := tapeAux0;
            program := program0
          |} =>
            ret ({|
              programCounter := programCounter0;
              registers := registers0;
              conditionFlag := conditionFlag0;
              memory := replace memory0 x v;
              tapeMain := tapeMain0;
              tapeAux := tapeAux0;
              program := program0
            |}, tt)
        end
    | LoadWord x => ret (m, Memory_Word_Load (memory m) x)
    | StoreWord x v => 
        match m with
        | {|
            programCounter := programCounter0;
            registers := registers0;
            conditionFlag := conditionFlag0;
            memory := memory0;
            tapeMain := tapeMain0;
            tapeAux := tapeAux0;
            program := program0
          |} =>
            ret ({|
              programCounter := programCounter0;
              registers := registers0;
              conditionFlag := conditionFlag0;
              memory := Memory_Word_Store memory0 x v;
              tapeMain := tapeMain0;
              tapeAux := tapeAux0;
              program := program0
            |}, tt)
        end
    end.

  Definition handle_programCounter R (e : ProgramCounterE R) :
    Monads.stateT MachineState (itree void1) R := 
    fun m =>
    match e with
    | SetPC v => 
        match m with
        | {|
            programCounter := programCounter0;
            registers := registers0;
            conditionFlag := conditionFlag0;
            memory := memory0;
            tapeMain := tapeMain0;
            tapeAux := tapeAux0;
            program := program0
          |} =>
            ret ({|
              programCounter := v;
              registers := registers0;
              conditionFlag := conditionFlag0;
              memory := memory0;
              tapeMain := tapeMain0;
              tapeAux := tapeAux0;
              program := program0
            |}, tt)
        end
    | IncPC => 
        match m with
        | {|
            programCounter := programCounter0;
            registers := registers0;
            conditionFlag := conditionFlag0;
            memory := memory0;
            tapeMain := tapeMain0;
            tapeAux := tapeAux0;
            program := program0
          |} =>
            ret ({|
              programCounter := bv_incr 1 programCounter0;
              registers := registers0;
              conditionFlag := conditionFlag0;
              memory := memory0;
              tapeMain := tapeMain0;
              tapeAux := tapeAux0;
              program := program0
            |}, tt)
        end
    | GetPC => ret (m, programCounter m)
    end.

  Definition handle_opcode R (e : OpcodeE R) :
    Monads.stateT MachineState (itree void1) R := 
    fun m =>
    match e with
    | ReadOp x => ret (m, 
      match List.nth_error (program m) (bitvector_nat_big x) with
      (* """ If pc is not an integer in {0, . . . , L-1}, where L is 
            the number of instructions in [program], then the instruction
            answer 1 is fetched as default. """ *)
      | None => OpcodeEncode answer1
      | Some x => x
      end)
    end.


  Definition handle_flag R (e : FlagE R) :
    Monads.stateT MachineState (itree void1) R := 
    fun m =>
    match e with
    | SetFlag b => 
        match m with
        | {|
            programCounter := programCounter0;
            registers := registers0;
            conditionFlag := conditionFlag0;
            memory := memory0;
            tapeMain := tapeMain0;
            tapeAux := tapeAux0;
            program := program0
          |} =>
            ret ({|
              programCounter := programCounter0;
              registers := registers0;
              conditionFlag := b;
              memory := memory0;
              tapeMain := tapeMain0;
              tapeAux := tapeAux0;
              program := program0
            |}, tt)
        end
    | GetFlag => ret (m, conditionFlag m)
    end.

  Definition handle_read R (e : ReadE R) :
    Monads.stateT MachineState (itree void1) R := 
    fun m =>
    match m with
    | {|
        programCounter := programCounter0;
        registers := registers0;
        conditionFlag := conditionFlag0;
        memory := memory0;
        tapeMain := tapeMain0;
        tapeAux := tapeAux0;
        program := program0
      |} =>
      match e with
      | ReadMain => 
        match tapeMain0 with
        | List.nil => ret ({|
                      programCounter := programCounter0;
                      registers := registers0;
                      conditionFlag := conditionFlag0;
                      memory := memory0;
                      tapeMain := List.nil;
                      tapeAux := tapeAux0;
                      program := program0
                    |}, None)
        | List.cons x xs => ret ({|
                              programCounter := programCounter0;
                              registers := registers0;
                              conditionFlag := conditionFlag0;
                              memory := memory0;
                              tapeMain := xs;
                              tapeAux := tapeAux0;
                              program := program0
                            |}, Some x)
        end
      | ReadAux => 
        match tapeAux0 with
        | List.nil => ret ({|
                      programCounter := programCounter0;
                      registers := registers0;
                      conditionFlag := conditionFlag0;
                      memory := memory0;
                      tapeMain := tapeMain0;
                      tapeAux := List.nil;
                      program := program0
                    |}, None)
        | List.cons x xs => ret ({|
                              programCounter := programCounter0;
                              registers := registers0;
                              conditionFlag := conditionFlag0;
                              memory := memory0;
                              tapeMain := tapeMain0;
                              tapeAux := xs;
                              program := program0
                            |}, Some x)
        end
      end
    end.

End TinyRAMHandlers.
