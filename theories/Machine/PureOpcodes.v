From Coq Require Import
  Lia.
From TinyRAM.Utils Require Import
  Vectors.
From TinyRAM.Utils Require Import
  BitVectors.
From TinyRAM.Utils Require Import
  Fin.
From TinyRAM.Machine Require Import
  Parameters.
From TinyRAM.Machine Require Import
  Words.
From TinyRAM.Machine Require Import
  Memory.
Import PeanoNat.Nat.

Module TinyRAMState (Params : TinyRAMParameters).
  Module TRMem := TinyRAMMem Params.
  Import TRMem.
  Export TRMem.

  Record MachineState : Type :=
    mkMachineState {
        (*"""
        The program counter, denoted pc; it consists of [wordSize] bits.
        """*)
        programCounter : Word;
        (*"""
        [registerCount] general-purpose registers, [...]
        """*)
        registerValues : Vector.t Word registerCount;
        (*"""
        The (condition) flag [...]; it consists of a single bit.
        """*)
        conditionFlag : bool;
        memory : Memory;
      }.

  (* TODO: Verify basic properties of replace!!! *)

    (* All opcodes which operate purely on state. *)

  (*Template:
      intro ms; destruct ms; split.
      (* PC *)
      + [...]
      (* Registers *)
      + [...]
      (* Flag *)
      + [...]
      (* Memory *)
      + [...]
  *)

  (*"""
  compute bitwise AND of [rj] and [A] and store result in ri result is 0W
  """*)
  Definition pureOp_and (ri rj : fin registerCount) (A : Word) :
    MachineState -> MachineState.
  Admitted.

  (*"""
  compute bitwise OR of [rj] and [A] and store result in ri result is 0W
  """*)
  Definition pureOp_or (ri rj : fin registerCount) (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  compute bitwise XOR of [rj] and [A] and store result in ri result is 0W
  """*)
  Definition pureOp_xor (ri rj : fin registerCount) (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  compute bitwise NOT of [A] and store result in ri result is 0W
  """*)
  Definition pureOp_not (ri : fin registerCount) (A : Word) :
    MachineState -> MachineState.
  Admitted.

  (*"""
  compute [rj]u + [A]u and store result in ri overflow
  """*)
  Definition pureOp_add (ri rj : fin registerCount) (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  compute [rj]u − [A]u and store result in ri borrow
  """*)
  Definition pureOp_sub (ri rj : fin registerCount) (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  compute [rj]u × [A]u and store least significant bits of result in ri overflow
  """*)
  Definition pureOp_mull (ri rj : fin registerCount) (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  compute [rj]u × [A]u and store most significant bits of result in ri overflow
  """*)
  Definition pureOp_umulh (ri rj : fin registerCount) (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  compute [rj]s × [A]s and store most significant bits of result in ri over/underflow
  """*)
  Definition pureOp_smulh (ri rj : fin registerCount) (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  compute quotient of [rj]u/[A]u and store result in ri [A]u = 0
  """*)
  Definition pureOp_udiv (ri rj : fin registerCount) (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  compute remainder of [rj]u/[A]u and store result in ri [A]u = 0
  """*)
  Definition pureOp_umod (ri rj : fin registerCount) (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  shift [rj] by [A]u bits to the left and store result in ri MSB of [rj]
  """*)
  Definition pureOp_shl (ri rj : fin registerCount) (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  shift [rj] by [A]u bits to the right and store result in ri LSB of [rj]
  """*)
  Definition pureOp_shr (ri rj : fin registerCount) (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  “compare equal” [ri] = [A]
  """*)
  Definition pureOp_cmpe (ri : fin registerCount) (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  “compare above”, unsigned [ri]u > [A]u
  """*)
  Definition pureOp_cmpa (ri : fin registerCount) (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  “compare above or equal”, unsigned [ri]u ≥ [A]u
  """*)
  Definition pureOp_cmpae (ri : fin registerCount) (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  “compare greater”, signed [ri]s > [A]s
  """*)
  Definition pureOp_cmpg (ri : fin registerCount) (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  “compare greater or equal”, signed [ri]s ≥ [A]s
  """*)
  Definition pureOp_cmpge (ri : fin registerCount) (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  store [A] in ri
  """*)
  Definition pureOp_mov (ri : fin registerCount) (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  if flag = 1, store [A] in ri
  """*)
  Definition pureOp_cmov (ri : fin registerCount) (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  set pc to [A]
  """*)
  Definition pureOp_jmp (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  if flag = 1, set pc to [A] (else increment pc as usual)
  """*)
  Definition pureOp_cjmp (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  if flag = 0, set pc to [A] (else increment pc as usual)
  """*)
  Definition pureOp_cnjmp (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  store the least-significant byte of [ri] at the [A]u-th byte in memory
  """*)
  Definition pureOp_store_b (A : Word) (ri : fin registerCount) :
    MachineState -> MachineState.
    intro ms; destruct ms; split.
    (* PC *)
    + exact (bv_incr programCounter0 pcIncrement).
    (* Registers *)
    + exact registerValues0.
    (* Flag *)
    + exact conditionFlag0.
    (* Memory *)
    + apply (replace memory0).
      (*" at the [A]u-th byte "*)
      - apply bitvector_fin.
        exact A.
      (*" the least-significant byte of [ri] "*)
      - apply (fun x => nth x ri) in registerValues0 as regi.
        apply RegisterBytes in regi.
        apply (nth regi).
        exists 0.
        apply wordSizeEighthPos.
  Qed.


  (*"""
  store into ri (with zero-padding in front) the [A]u-th byte in memory
  """*)
  Definition pureOp_load_b (ri : fin registerCount) (A : Word) :
    MachineState -> MachineState.
    intro ms; destruct ms; split.
    (* PC *)
    + exact (bv_incr programCounter0 pcIncrement).
    (* Registers *)
    + apply (replace registerValues0 ri).
      apply BytesRegister.
      (*" (with zero-padding in front) "*)
      replace wordSizeEighth with (Nat.pred wordSizeEighth + 1).
      2: { assert (Nat.pred wordSizeEighth < wordSizeEighth).
          { apply Lt.lt_pred_n_n. apply wordSizeEighthPos. }
          lia. }
      apply Vector.append.
      (*" zero-padding "*)
      - apply (Vector.const zeroByte).
      (*" [A]u-th byte in memory "*)
      - apply (fun x => Vector.cons _ x _ (Vector.nil _)).
        apply (nth memory0).
        apply bitvector_fin.
        exact A.
    (* Flag *)
    + exact conditionFlag0.
    (* Memory *)
    + exact memory0.
  Defined.

  (*"""
  store [ri] at the word in memory that is aligned to the [A]w-th byte
  """*)
  Definition pureOp_store_w (ri : fin registerCount) (A : Word) :
    MachineState -> MachineState.
    intro ms; destruct ms; split.
    (* PC *)
    + exact (bv_incr programCounter0 pcIncrement).
    (* Registers *)
    + exact registerValues0.
    (* Flag *)
    + exact conditionFlag0.
    (* Memory *)
    + apply (Memory_Register_Store_from_Reg memory0).
      (*" at the word in memory that is aligned to the [A]w-th byte "*)
      - exact A. 
      (* store [ri] *)
      - exact (nth registerValues0 ri).
  Defined.


  (*"""
  store into ri the word in memory that is aligned to the [A]w-th byte
  """*)
  Definition pureOp_load_w (ri : fin registerCount) (A : Word) :
    MachineState -> MachineState.
    intro ms; destruct ms; split.
    (* PC *)
    + exact (bv_incr programCounter0 pcIncrement).
    (* Registers *)
    + apply (replace registerValues0 ri).
      apply (Memory_Register_Load_from_Reg memory0).
      exact A.
    (* Flag *)
    + exact conditionFlag0. 
    (* Memory *)
    + exact memory0.
  Defined.

End TinyRAMState.


