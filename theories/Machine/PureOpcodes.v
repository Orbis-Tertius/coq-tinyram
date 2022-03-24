From Coq Require Import
  Lia VectorDef.
Import VectorNotations.
From TinyRAM.Utils Require Import
  Vectors BitVectors Fin.
From TinyRAM.Machine Require Import
  Parameters Words Memory.
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
  compute bitwise AND of [rj] and [A] and store result in ri
  [flag:] result is 0W
  """*)
  Definition pureOp_and (ri rj : regId) (A : Word) :
    MachineState -> MachineState.
    intro ms; destruct ms.
    apply (nth registerValues0) in rj.
    remember (bv_and rj A) as res eqn:resDef.
    split.
    (* PC *)
    + exact (bv_incr pcIncrement programCounter0).
    (* Registers *)
    + exact (replace registerValues0 ri res).
    (* Flag *)
    + exact (bv_eq res (Vector.const false _)).
    (* Memory *)
    + exact memory0.
  Defined.

  (*"""
  compute bitwise OR of [rj] and [A] and store result in ri
  [flag:] result is 0W
  """*)
  Definition pureOp_or (ri rj : regId) (A : Word) :
    MachineState -> MachineState.
    intro ms; destruct ms.
    apply (nth registerValues0) in rj.
    remember (bv_or rj A) as res eqn:resDef.
    split.
    (* PC *)
    + exact (bv_incr pcIncrement programCounter0).
    (* Registers *)
    + exact (replace registerValues0 ri res).
    (* Flag *)
    + exact (bv_eq res (Vector.const false _)).
    (* Memory *)
    + exact memory0.
  Defined.


  (*"""
  compute bitwise XOR of [rj] and [A] and store result in ri
  [flag:] result is 0W
  """*)
  Definition pureOp_xor (ri rj : regId) (A : Word) :
    MachineState -> MachineState.
    intro ms; destruct ms.
    apply (nth registerValues0) in rj.
    remember (bv_xor rj A) as res eqn:resDef.
    split.
    (* PC *)
    + exact (bv_incr pcIncrement programCounter0).
    (* Registers *)
    + exact (replace registerValues0 ri res).
    (* Flag *)
    + exact (bv_eq res (Vector.const false _)).
    (* Memory *)
    + exact memory0.
  Defined.

  (*"""
  compute bitwise NOT of [A] and store result in ri
  [flag:] result is 0W
  """*)
  Definition pureOp_not (ri : regId) (A : Word) :
    MachineState -> MachineState.
    intro ms; destruct ms.
    remember (bv_not A) as res eqn:resDef.
    split.
    (* PC *)
    + exact (bv_incr pcIncrement programCounter0).
    (* Registers *)
    + exact (replace registerValues0 ri res).
    (* Flag *)
    + exact (bv_eq res (Vector.const false _)).
    (* Memory *)
    + exact memory0.
  Defined.

  (*"""
  The instruction add ri rj A stores in ri the W-bit string
  a_{W-1}...a_0 obtained as follows:
  a_{W-1}...a_0 are the W least significant bits of G = [rj]u + [A]u.
  Moreover, flag is set to GW , where GW is the MSB of G.
  """*)
  Definition pureOp_add (ri rj : regId) (A : Word) :
    MachineState -> MachineState.
    intro ms; destruct ms.
    apply (nth registerValues0) in rj.
    remember (bv_add rj A) as res eqn:resDef.
    split.
    (* PC *)
    + exact (bv_incr pcIncrement programCounter0).
    (* Registers *)
    + exact (replace registerValues0 ri (tl res)).
    (* Flag *)
    + exact (hd res).
    (* Memory *)
    + exact memory0.
  Defined.


  (*"""
  compute [rj]u - [A]u and store result in ri
  
  flag is set to 1 - GW , where GW is the MSB of G [res].
  """*)
  Definition pureOp_sub (ri rj : regId) (A : Word) :
    MachineState -> MachineState.
    intro ms; destruct ms.
    apply (nth registerValues0) in rj.
    remember (bv_sub rj A) as res.
    split.
    (* PC *)
    + exact (bv_incr pcIncrement programCounter0).
    (* Registers *)
    + exact (replace registerValues0 ri (tl res)).
    (* Flag *)
    + exact (negb (hd res)).
    (* Memory *)
    + exact memory0.
  Defined.


  (*"""
  compute [rj]u * [A]u and store least significant bits of result in ri
 
  flag is set to 1 if [rj]u * [A]u ∈ U_W and to 0 otherwise.
  """*)
  Definition pureOp_mull (ri rj : regId) (A : Word) :
    MachineState -> MachineState.
    intro ms; destruct ms.
    apply (nth registerValues0) in rj.
    destruct (bv_mul_flags rj A) as [[[of _] _] res].
    split.
    (* PC *)
    + exact (bv_incr pcIncrement programCounter0).
    (* Registers *)
    + exact (replace registerValues0 ri res).
    (* Flag *)
    + exact (negb of).
    (* Memory *)
    + exact memory0.
  Defined.

  (*"""
  compute [rj]u * [A]u and store most significant bits of result in ri
 
  flag is set to 1 if [rj]u * [A]u ∈ U_W and to 0 otherwise.
  """*)
  Definition pureOp_umulh (ri rj : regId) (A : Word) :
    MachineState -> MachineState.
    intro ms; destruct ms.
    apply (nth registerValues0) in rj.
    destruct (bv_mul_flags rj A) as [[[of _] res] _].
    split.
    (* PC *)
    + exact (bv_incr pcIncrement programCounter0).
    (* Registers *)
    + exact (replace registerValues0 ri res).
    (* Flag *)
    + exact (negb of).
    (* Memory *)
    + exact memory0.
  Defined.

  (*"""
  compute [rj]s * [A]s and store most significant bits of result in ri
  [flag:] over/underflow
  """*)
  Definition pureOp_smulh (ri rj : regId) (A : Word) :
    MachineState -> MachineState.
    intro ms; destruct ms.
    apply (nth registerValues0) in rj.
    unfold Word in rj, A.
    replace wordSize with (S (pred wordSize)) in rj, A.
    2: { apply succ_pred_pos; apply wordSizePos. } 
    destruct (bv_smulh rj A) as [of res].
    replace (S (pred wordSize)) with wordSize in res.
    2: { symmetry; apply succ_pred_pos; apply wordSizePos. } 
    split.
    (* PC *)
    + exact (bv_incr pcIncrement programCounter0).
    (* Registers *)
    + exact (replace registerValues0 ri res).
    (* Flag *)
    + exact (negb of).
    (* Memory *)
    + exact memory0.
  Defined.

  (*"""
  compute quotient of [rj]u/[A]u and store result in ri
  [flag:] [A]u = 0
  """*)
  Definition pureOp_udiv (ri rj : regId) (A : Word) :
    MachineState -> MachineState.
    intro ms; destruct ms.
    apply (nth registerValues0) in rj.
    destruct (bv_udiv rj A) as [zf res].
    split.
    (* PC *)
    + exact (bv_incr pcIncrement programCounter0).
    (* Registers *)
    + exact (replace registerValues0 ri res).
    (* Flag *)
    + exact zf.
    (* Memory *)
    + exact memory0.
  Defined.


  (*"""
  compute remainder of [rj]u/[A]u and store result in ri
  [flag:] [A]u = 0
  """*)
  Definition pureOp_umod (ri rj : regId) (A : Word) :
    MachineState -> MachineState.
    intro ms; destruct ms.
    apply (nth registerValues0) in rj.
    destruct (bv_umod rj A) as [zf res].
    split.
    (* PC *)
    + exact (bv_incr pcIncrement programCounter0).
    (* Registers *)
    + exact (replace registerValues0 ri res).
    (* Flag *)
    + exact zf.
    (* Memory *)
    + exact memory0.
  Defined.


  (*"""
  shift [rj] by [A]u bits to the left and store result in ri
  [flag:] MSB of [rj]
  """*)
  Definition pureOp_shl (ri rj : regId) (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  shift [rj] by [A]u bits to the right and store result in ri
  [flag:] LSB of [rj]
  """*)
  Definition pureOp_shr (ri rj : regId) (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  “compare equal”
  [flag:] [ri] = [A]
  """*)
  Definition pureOp_cmpe (ri : regId) (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  “compare above”, unsigned
  [flag:] [ri]u > [A]u
  """*)
  Definition pureOp_cmpa (ri : regId) (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  “compare above or equal”, unsigned
  [flag:] [ri]u ≥ [A]u
  """*)
  Definition pureOp_cmpae (ri : regId) (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  “compare greater”, signed
  [flag:] [ri]s > [A]s
  """*)
  Definition pureOp_cmpg (ri : regId) (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  “compare greater or equal”, signed
  [flag:] [ri]s ≥ [A]s
  """*)
  Definition pureOp_cmpge (ri : regId) (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  store [A] in ri
  """*)
  Definition pureOp_mov (ri : regId) (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  if flag = 1, store [A] in ri
  """*)
  Definition pureOp_cmov (ri : regId) (A : Word) :
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
  Definition pureOp_store_b (A : Word) (ri : regId) :
    MachineState -> MachineState.
    intro ms; destruct ms; split.
    (* PC *)
    + exact (bv_incr pcIncrement programCounter0).
    (* Registers *)
    + exact registerValues0.
    (* Flag *)
    + exact conditionFlag0.
    (* Memory *)
    + apply (replace memory0).
      (*" at the [A]u-th byte "*)
      - apply bitvector_fin_big.
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
  Definition pureOp_load_b (ri : regId) (A : Word) :
    MachineState -> MachineState.
    intro ms; destruct ms; split.
    (* PC *)
    + exact (bv_incr pcIncrement programCounter0).
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
        apply bitvector_fin_big.
        exact A.
    (* Flag *)
    + exact conditionFlag0.
    (* Memory *)
    + exact memory0.
  Defined.

  (*"""
  store [ri] at the word in memory that is aligned to the [A]w-th byte
  """*)
  Definition pureOp_store_w (ri : regId) (A : Word) :
    MachineState -> MachineState.
    intro ms; destruct ms; split.
    (* PC *)
    + exact (bv_incr pcIncrement programCounter0).
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
  Definition pureOp_load_w (ri : regId) (A : Word) :
    MachineState -> MachineState.
    intro ms; destruct ms; split.
    (* PC *)
    + exact (bv_incr pcIncrement programCounter0).
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


