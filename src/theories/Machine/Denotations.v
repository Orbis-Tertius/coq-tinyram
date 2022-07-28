From Coq Require Import
  ZArith.Int List VectorDef BinIntDef VectorEq.
From ExtLib Require Import
     Monad.
From ITree Require Import
     ITree
     Simple
     ITreeFacts
     ITreeMonad
     Basics.Category
     Basics.CategorySub.
From ITree.Basics Require Import
     CategorySub.
From TinyRAM.Machine Require Import
  Parameters Words Memory Coding.
From TinyRAM.Utils Require Import
  Fin BitVectors.
Import BinInt.Z PeanoNat.Nat Monads MonadNotation VectorNotations.

Module TinyRAMDenotations (Params : TinyRAMParameters).
  Module TRMem := TinyRAMMem Params.
  Import TRMem.
  Export TRMem.

  Definition traverse_ {A: Type} {M: Type -> Type} `{Monad M} (f: A -> M unit): list A -> M unit :=
    fix traverse__ l: M unit :=
      match l with
      | List.nil => ret tt
      | List.cons a l => (f a;; traverse__ l)%monad
      end.

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
  | IncPC : ProgramCounterE unit
  | GetPC : ProgramCounterE Word.

  Variant InstructionE : Type -> Type :=
  | ReadInst (a : nat) : InstructionE (Word * Word).

  Variant FlagE : Type -> Type :=
  | GetFlag : FlagE bool
  | SetFlag (b : bool) : FlagE unit.

  Variant ReadE : Type -> Type :=
  | ReadMain : ReadE (option Word)
  | ReadAux : ReadE (option Word).

  Section with_event.
    Local Open Scope monad_scope.

    Context {E : Type -> Type}.
    Context {HasRegister : RegisterE -< E}.
    Context {HasFlag : FlagE -< E}.
    Context {HasProgramCounter : ProgramCounterE -< E}.
    Context {HasMemory : MemoryE -< E}.
    Context {HasRead : ReadE -< E}.
    Context {HasInstruction : InstructionE -< E}.

    Definition denote_operand (o : operand) : itree E Word :=
      match o with
      | inl v => Ret v
      | inr v => trigger (GetReg v)
      end.

    Definition denote_instruction (o : Instruction) : itree E unit :=
      match o with
      | (o, op) => 
        A <- denote_operand op ;;
        match o with

        | andI ri rj =>
          regj <- trigger (GetReg rj) ;;
          (* """ compute bitwise AND of [rj] and [A] and store result in ri """ *)
          let res := bv_and regj A in
          trigger (SetReg ri res) ;;
          (* """ [flag:] result is 0_W """ *)
          trigger (SetFlag (bv_eq res (const b0 _))) ;;
          trigger IncPC

        | orI ri rj =>
          regj <- trigger (GetReg rj) ;;
          (* """ compute bitwise OR of [rj] and [A] and store result in ri """ *)
          let res := bv_or regj A in
          trigger (SetReg ri res) ;;
          (* """ [flag:] result is 0_W """ *)
          trigger (SetFlag (bv_eq res (const b0 _))) ;;
          trigger IncPC

        | xorI ri rj =>
          regj <- trigger (GetReg rj) ;;
          (* """ compute bitwise NOT of [A] and store result in ri """ *)
          let res := bv_xor regj A in
          trigger (SetReg ri res) ;;
          (* """ [flag:] result is 0_W """ *)
          trigger (SetFlag (bv_eq res (const b0 _))) ;;
          trigger IncPC

        | notI ri =>
          (* """ compute bitwise NOT of [A] and store result in ri """ *)
          let res := bv_not A in
          trigger (SetReg ri res) ;;
          (* """ [flag:] result is 0_W """ *)
          trigger (SetFlag (bv_eq res (const b0 _))) ;;
          trigger IncPC

        | addI ri rj =>
          regj <- trigger (GetReg rj) ;;
          (*""" stores in ri [...] the W least significant bits of G = [rj]u + [A]u. """ *)
          let res := bv_add regj A in
          trigger (SetReg ri (tl res)) ;;
          (*""" flag is set to [...] the MSB of G. """*)
          trigger (SetFlag (hd res)) ;;
          trigger IncPC

        | subI ri rj =>
          regj <- trigger (GetReg rj) ;;
          (*""" stores in ri [...] the W least significant bits of G = [rj]u + 2^W - [A]u. """ *)
          let res := bv_sub regj A in
          trigger (SetReg ri (tl res)) ;;
          (*""" flag is set to 1 - GW, where GW is the MSB of G [res]. """*)
          trigger (SetFlag (negb (hd res))) ;;
          trigger IncPC

        | mullI ri rj =>
          regj <- trigger (GetReg rj) ;;
          (*""" compute [rj]u * [A]u and store least significant bits of result in ri """ *)
          let res := splitat _ (bv_mul regj A) in
          let resh := fst res in
          let resl := snd res in
          trigger (SetReg ri resl) ;;
          (*""" flag is set to 1 if [rj]u * [A]u ∈ U_W and to 0 otherwise. """*)
          trigger (SetFlag (negb (bv_eq resh (const b0 _)))) ;;
          trigger IncPC

        | umulhI ri rj =>
          regj <- trigger (GetReg rj) ;;
          (*""" compute [rj]u * [A]u and store most significant bits of result in ri """ *)
          let resh := fst (splitat _ (bv_mul regj A)) in
          trigger (SetReg ri resh) ;;
          (*""" flag is set to 1 if [rj]u * [A]u ∈ U_W and to 0 otherwise. """*)
          trigger (SetFlag (negb (bv_eq resh (const b0 _)))) ;;
          trigger IncPC

        | smulhI ri rj =>
          regj <- trigger (GetReg rj) ;;
          let wA := wcast A in let wrej := wcast regj in
          (*"""compute [rj]s * [A]s and store most significant bits of result in ri"""*)
          let mjA := (twos_complement wrej * twos_complement wA)%Z in
          let sres := twos_complement_inv (pred wordSize + pred wordSize) mjA in
          let sign := hd sres in
          let resh := fst (splitat _ (bv_abs sres)) in
          trigger (SetReg ri (wuncast (sign :: resh))) ;;
          (*""" flag is set to 1 if [rj]s x [A]s ∈ [...] {-2^(W-1), ..., 0, 1, ..., 2^(W-1) - 1} """ *)
          trigger (SetFlag (negb (andb (- 2 ^ (of_nat wordSize - 1) <=? mjA) 
                                 (mjA <? 2 ^ (of_nat wordSize - 1)))%Z)) ;;
          trigger IncPC

        | udivI ri rj =>
          regj <- trigger (GetReg rj) ;;
          (*""" compute quotient of [rj]u/[A]u and store result in ri """ *)
          let res := bv_udiv regj A in
          trigger (SetReg ri res) ;;
          (*""" [flag:] [A]u = 0 """*)
          trigger (SetFlag (bv_eq A (const b0 _))) ;;
          trigger IncPC

        | umodI ri rj =>
          regj <- trigger (GetReg rj) ;;
          (*""" compute remainder of [rj]u/[A]u and store result in ri """ *)
          let res := bv_umod regj A in
          trigger (SetReg ri res) ;;
          (*""" [flag:] [A]u = 0 """*)
          trigger (SetFlag (bv_eq A (const b0 _))) ;;
          trigger IncPC

        | shlI ri rj =>
          regj <- trigger (GetReg rj) ;;
          (*""" shift [rj] by [A]u bits to the left and store result in ri """ *)
          let res := bv_shl (bitvector_nat_big A) regj in
          trigger (SetReg ri res) ;;
          (*""" [flag:] MSB of [rj] """*)
          trigger (SetFlag (hd (wcast regj))) ;;
          trigger IncPC

        | shrI ri rj =>
          regj <- trigger (GetReg rj) ;;
          (*""" shift [rj] by [A]u bits to the right and store result in ri """ *)
          let res := bv_shr (bitvector_nat_big A) regj in
          trigger (SetReg ri res) ;;
          (*""" [flag:] LSB of [rj] """*)
          trigger (SetFlag (last (wcast regj))) ;;
          trigger IncPC

        | cmpeI ri =>
          regi <- trigger (GetReg ri) ;;
          (*""" [flag:] [ri] = [A] """*)
          trigger (SetFlag (bv_eq regi A)) ;;
          trigger IncPC

        | cmpaI ri =>
          regi <- trigger (GetReg ri) ;;
          (*""" [flag:] [ri] > [A] """*)
          trigger (SetFlag (bv_lt A regi)) ;;
          trigger IncPC

        | cmpaeI ri =>
          regi <- trigger (GetReg ri) ;;
          (*""" [flag:] [ri] ≥ [A] """*)
          trigger (SetFlag (bv_le A regi)) ;;
          trigger IncPC

        | cmpgI ri =>
          regi <- trigger (GetReg ri) ;;
          (*""" [flag:] [ri]s > [A]s """*)
          trigger (SetFlag (twos_complement (wcast A) <? twos_complement (wcast regi))%Z) ;;
          trigger IncPC

        | cmpgeI ri =>
          regi <- trigger (GetReg ri) ;;
          (*""" [flag:] [ri]s >= [A]s """*)
          trigger (SetFlag (twos_complement (wcast A) <=? twos_complement (wcast regi))%Z) ;;
          trigger IncPC

        | movI ri =>
          regi <- trigger (GetReg ri) ;;
          (*""" store [A] in ri """*)
          trigger (SetReg ri A) ;;
          trigger IncPC

        | cmovI ri =>
          flag <- (trigger GetFlag) ;;
          (*""" if flag = 1, store [A] in ri """*)
          (if (flag : bool)
           then (regi <- trigger (GetReg ri) ;;
                trigger (SetReg ri A))
           else ret tt) ;;
          trigger IncPC

        | jmpI =>
          (*""" set pc to [A] """*)
          trigger (SetPC A)

        | cjmpI =>
          flag <- (trigger GetFlag : itree _ bool) ;;
          (*""" if flag = 1, set pc to [A] (else increment pc as usual) """*)
          if (flag : bool)
          then trigger (SetPC A)
          else trigger IncPC

        | cnjmpI =>
          flag <- (trigger GetFlag : itree _ bool) ;;
          (*""" if flag = 0, set pc to [A] (else increment pc as usual) """*)
          if (flag : bool)
          then trigger IncPC
          else trigger (SetPC A)

        | store_bI ri =>
          regi <- trigger (GetReg ri) ;;
          (*""" store the least-significant byte of [ri] at the [A]u-th byte in memory """*)
          trigger (StoreByte (bitvector_fin_big A) (snd (splitat _ (wbcast regi)))) ;;
          trigger IncPC

        | load_bI ri =>
          (*""" store into ri (with zero-padding in front) the [A]u-th byte in memory """*)
          Abyte <- trigger (LoadByte (bitvector_fin_big A)) ;;
          trigger (SetReg ri (wbuncast (const b0 _ ++ Abyte))) ;;
          trigger IncPC

        | store_wI ri =>
          regi <- trigger (GetReg ri) ;;
          (*""" store [ri] at the word in memory that is aligned to the [A]w-th byte """*)
          trigger (StoreWord (bitvector_fin_big A) regi) ;;
          trigger IncPC

        | load_wI ri =>
          (*""" store into ri the word in memory that is aligned to the [A]w-th byte """*)
          Aword <- trigger (LoadWord (bitvector_fin_big A)) ;;
          trigger (SetReg ri Aword) ;;
          trigger IncPC

        | readI ri =>
          (* """ stores in ri the next W-bit word on the [A]u-th tape [...]
                 and set flag = 0; """ *)
          (* """ if there are no remaining input words on the [A]u-th tape store
                 0_W in ri and set flag = 1. """ *)
          match bitvector_nat_big A with
          | 0 => mtWord <- trigger ReadMain ;;
                 match mtWord with
                 | None => trigger (SetReg ri (const b0 _)) ;;
                           trigger (SetFlag b1)
                 | (Some w) => trigger (SetReg ri w) ;;
                               trigger (SetFlag b0)
                 end
          | 1 => mtWord <- trigger ReadAux ;;
                 match mtWord with
                 | None => trigger (SetReg ri (const b0 _)) ;;
                           trigger (SetFlag b1)
                 | (Some w) => trigger (SetReg ri w) ;;
                               trigger (SetFlag b0)
                 end
          (* """ if [A]u is not 0 or 1, then we store 0_W in ri and set flag = 1. """ *)
          | _ => trigger (SetReg ri (const b0 _)) ;;
                 trigger (SetFlag b1)
          end
          ;; trigger IncPC

        | answerI =>
          (*""" The instruction answer A causes the machine to [...] halt """*)
          ret tt

        end
    end.

    Definition run_step : itree E (unit + Word) :=
      a <- trigger GetPC ;;
      w2code <- trigger (ReadInst (bitvector_nat_big a)) ;;
      let instr := uncurry InstructionDecode w2code in
      match instr with
      | (answerI, op) => (ITree.map inr (denote_operand op))
      | i => (ITree.map inl (denote_instruction i))
      end.

    Definition run : itree E Word :=
      ITree.iter (fun _ => run_step) tt.

    Definition run_step_lim (n : nat) : itree E (nat + option Word) :=
      match n with
      | 0 => ret (inr None)
      | S n => 
        a <- run_step ;;
        match a with
        | inl _ => ret (inl n)
        | inr x => ret (inr (Some x))
        end
      end.

    (* Run, but only for a specified number of instructions. *)
    Definition run_for : nat -> itree E (option Word) :=
      ITree.iter run_step_lim.

    (* programs *)

    Definition denote_program : list Instruction -> itree E unit :=
      traverse_ denote_instruction.

    Theorem denote_list_app:
    forall is1 is2,
      denote_program (is1 ++ is2) ≅ (denote_program is1;; denote_program is2).
    Proof.
      induction is1; intro.
      - cbn.
        rewrite bind_ret_l; reflexivity.
      - cbn.
        rewrite bind_bind.
        setoid_rewrite IHis1; reflexivity.
    Qed.


  End with_event.

End TinyRAMDenotations.
