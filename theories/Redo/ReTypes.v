From Coq Require Import
  Lia.
From TinyRAM.Redo Require Import
  Vectors.
From TinyRAM.Utils Require Import
  Fin.
Import PeanoNat.Nat.

(* 
  Note: Text between triple quotes are
  direct quotes from the TinyRAM 2.000 spec.
*)

Module Type TinyRAMParameters.
  (*"""  
  TinyRAM [...] is parametrized by two integers: the word size [...]
  and the number of registers [...]
  """*)
  Parameter (wordSize registerCount : nat).

  (*"""  
  the word size [is] required to be a power of 2 and divisible by 8.
  """*)
  Parameter (wordSizeLength wordSizeEighth : nat).
  Axiom wordSizeDiv8 : wordSize = wordSizeEighth * 8.
  Axiom wordSizePow2 : wordSize = 2 ^ wordSizeLength.

  (* ??? *)
  Axiom wordSizePos : 0 < wordSize. (* for MSB *)

  (*Axiom (H0 : exists k, wordSize = 4 * k).
  Axiom H1 : 6 + 2 * Nat.log2 registerCount <= wordSize.
  Definition memorySize : nat := 2 ^ wordSize.
  Definition incrAmount : nat := Nat.div wordSize 4.*)
End TinyRAMParameters.

Module TinyRAMTypes (Params : TinyRAMParameters).
  Import Params.
  Export Params.

  (*"""
  each Word consists of [wordSize] bits
  """*)
  Definition Word := Vector.t bool wordSize.

  Definition Byte := Vector.t bool 8.

  Definition zeroByte : Byte :=
    Vector.const false 8.

  Definition oneByte : Byte :=
    Vector.const true 8.

  Definition zeroRegister : Word := 
    Vector.const false _.

  Definition oneRegister : Word := 
    Vector.const true _.

  (*Registers can be cleanly split into bytes.*) 
  Definition RegisterBytes (r : Word) : 
    Vector.t Byte wordSizeEighth :=
    vector_unconcat (vector_length_coerce wordSizeDiv8 r).

  Theorem RegisterBytesConserv :
    forall (r : Word), 
    vector_length_coerce (eq_sym wordSizeDiv8)
      (vector_concat (RegisterBytes r)) = r.
  Proof.
    intros r.
    unfold RegisterBytes.
    rewrite vector_concat_inv1.
    rewrite vector_length_coerce_inv.
    reflexivity.
  Qed.

  (*"""
  Memory, which is a linear array of 2^[wordSize] bytes.
  """*)
  Definition Memory := Vector.t Byte (2 ^ wordSize).

  Definition lt_sub:
  forall {n m}, n < m -> {p : nat | m = p + n /\ 0 < p}.
  Proof.  
    intros n m.
    generalize dependent n.
    induction m as [|m IHm]; intros n lnm. 
    - destruct (nlt_0_r _ lnm).
    - destruct n as [|n].
      + exists (S m).
        lia.
      + apply Lt.lt_S_n in lnm.
        destruct (IHm n lnm).
        exists x.
        lia.
  Defined.

  Definition le_sub:
  forall {n m}, n <= m -> {p : nat | m = p + n /\ 0 <= p}.
  Proof.  
    intros n m.
    generalize dependent n.
    induction m as [|m IHm]; intros n lnm. 
    - exists 0.
      lia.
    - destruct n as [|n].
      + exists (S m).
        lia.
      + apply Le.le_S_n in lnm.
        destruct (IHm n lnm).
        exists x.
        lia.
  Defined.

  (*
  If we have memory of size memsz and are looking at
  a block of size blksz starting at idx, then we can
  reformat memsz into
    1. idx + blksz + tl 
       if there is no overflow
    2. blk1 + idx' + blk2
       where blk1 + blk2 = blksz
         and idx' = idx - blk1
       if there is an overflow
  *)

  Definition Memory_Block_Lem : forall idx blksz memsz,
    (idx < memsz) -> (blksz < memsz) ->
    { tl | memsz = idx + blksz + tl } + 
    { blk1 & { blk2 & { idx2 |
      blk1 + blk2 = blksz /\
      blk1 + idx2 = idx /\
      memsz = blk1 + idx2 + blk2 }}}.
    intros idx blksz memsz lim lbm.
    remember (memsz <? idx + blksz) as lm_ib.
    destruct lm_ib.
    - symmetry in Heqlm_ib.
      rewrite ltb_lt in Heqlm_ib.
      destruct (lt_sub Heqlm_ib) as [blk1 [Heq1 l0blk1]].
      right.
      exists blk1.
      destruct (lt_sub lim) as [blk2 [Heq2 l0blk2]].
      exists blk2.
      assert (blk1 < idx) as lb1_i.
      { lia. }
      destruct (lt_sub lb1_i) as [idx2 [Heqi l0idx2]].
      exists idx2.
      lia.
    - left.
      assert (not (memsz < idx + blksz)).
      { intro. rewrite <- ltb_lt in H.
        rewrite H in Heqlm_ib. discriminate Heqlm_ib. }
      clear Heqlm_ib.
      assert (memsz >= idx + blksz).
      { apply Compare_dec.not_lt. assumption. }
      destruct (le_sub H0) as [tl [Heq leotl]].
      exists tl.
      lia.
  Defined.

  (*"""
  When storing or loading blocks of multiple bytes,
  we use the little-endian convention 
  (i.e., the least-significant byte is at the lowest address). 

  We say that a block is aligned to the A-th byte if its
  least-significant byte is at address A.
  """*)
  Definition Memory_Block_Load_Store : forall
    (m : Memory)
    (idx blksz: fin (2 ^ wordSize))
    (block : Vector.t Byte (proj1_sig blksz)),
    Vector.t Byte (proj1_sig blksz) * Memory.
  intros m [idx lip] [blksz lbp] block.
  unfold Memory in m.
  unfold Memory.
  destruct (Memory_Block_Lem _ _ _ lip lbp) as 
    [[tl eq]|[blk1[blk2[idx2[eq1 [eq2 eq3]]]]]].
  - rewrite eq in m.
    destruct (Vector.splitat _ m) as [m' m3].
    destruct (Vector.splitat _ m') as [m1 m2].
    split.
    { exact m2. }
    rewrite eq.
    exact (Vector.append (Vector.append m1 block) m3).
  - rewrite eq3 in m.
    destruct (Vector.splitat _ m) as [m' m3].
    destruct (Vector.splitat _ m') as [m1 m2].
    split.
    + apply (vector_length_coerce eq1).
      (* Note: m1 is an overflow, so it's
              bits are more significant than m3. *)
      rewrite add_comm.
      apply (Vector.append m3 m1).
    + rewrite <- eq1 in block.
      destruct (Vector.splitat _ block) as [block1 block2].
      rewrite eq3.
      (* Note: The overflow means block2 should go at
              the begining of memory, and block 1 at the end. *)
      assert (blk1 + idx2 + blk2 = blk2 + idx2 + blk1) as OvrEq.
      { lia. }
      rewrite OvrEq.
      exact (Vector.append (Vector.append block2 m2) block1).
  Defined.

  Definition Memory_Block_Load
    (m : Memory)
    (idx blksz : fin (2 ^ wordSize)) :
    Vector.t Byte (proj1_sig blksz) :=
  fst (Memory_Block_Load_Store m idx blksz (Vector.const zeroByte _)).

(* Memory_Block_Load w/o rebuilding memory. *)
Definition Memory_Block_Load_2 : forall
    (m : Memory)
    (idx blksz: fin (2 ^ wordSize)),
    Vector.t Byte (proj1_sig blksz).
  intros m [idx lip] [blksz lbp].
  unfold Memory in m.
  destruct (Memory_Block_Lem _ _ _ lip lbp) as 
    [[tl eq]|[blk1[blk2[idx2[eq1 [eq2 eq3]]]]]].
  - rewrite eq in m.
    destruct (Vector.splitat _ m) as [m' _].
    destruct (Vector.splitat _ m') as [_ m2].
    exact m2.
  - rewrite eq3 in m.
    destruct (Vector.splitat _ m) as [m' m3].
    destruct (Vector.splitat _ m') as [m1 _].
    apply (vector_length_coerce eq1).
    (* Note: m1 is an overflow, so it's
              bits are more significant than m3. *)
    rewrite add_comm.
    apply (Vector.append m3 m1).
  Defined.

  Definition Memory_Block_Store 
    (m : Memory)
    (idx blksz : fin (2 ^ wordSize))
    (block : Vector.t Byte (proj1_sig blksz)) :
    Memory :=
  snd (Memory_Block_Load_Store m idx blksz block).

  Definition wordSizeEighthFin : fin (2 ^ wordSize).
    exists wordSizeEighth.
    assert (0 < wordSizeEighth * 8).
    { rewrite <- wordSizeDiv8. apply wordSizePos. }
    transitivity (wordSizeEighth * 8).
    { lia. }
    rewrite <- wordSizeDiv8.
    apply pow_gt_lin_r.
    lia.
  Defined.

  (* Since a Word is a memory block, it can be loaded as well. *)
  Definition Memory_Register_Load
    (m : Memory)
    (idx : fin (2 ^ wordSize)) :
    Word.
  unfold Word.
  rewrite wordSizeDiv8.
  apply vector_concat.
  apply (Memory_Block_Load_2 m idx wordSizeEighthFin).
  Defined.

  (* Since a Word is a memory block, it can be stored as well. *)
  Definition Memory_Register_Store 
    (m : Memory)
    (idx : fin (2 ^ wordSize))
    (reg : Word) :
    Memory.
    apply (Memory_Block_Store m idx wordSizeEighthFin).
    apply vector_unconcat.
    simpl.
    rewrite <- wordSizeDiv8.
    apply reg.
  Defined.

  Definition Register_Index (w : Word) : fin (2 ^ wordSize) :=
    bitvector_fin w.

  Definition Memory_Register_Load_from_Reg 
    (m : Memory) (idx : Word) : Word :=
    Memory_Register_Load m (Register_Index idx).

  Definition Memory_Register_Store_from_Reg 
    (m : Memory) (idx reg : Word) : Memory :=
    Memory_Register_Store m (Register_Index idx) reg.


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

  (* All opcodes which operate putely on state. *)

  (*"""
  and ri rj A compute bitwise AND of [rj] and [A] and store result in ri result is 0W
  """*)
  Definition pureOp_and (ri rj : fin registerCount) (A : Word) :
    MachineState -> MachineState.
  Admitted.

  (*"""
  or ri rj A compute bitwise OR of [rj] and [A] and store result in ri result is 0W
  """*)
  Definition pureOp_or (ri rj : fin registerCount) (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  xor ri rj A compute bitwise XOR of [rj] and [A] and store result in ri result is 0W
  """*)
  Definition pureOp_xor (ri rj : fin registerCount) (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  not ri A compute bitwise NOT of [A] and store result in ri result is 0W
  """*)
  Definition pureOp_not (ri : fin registerCount) (A : Word) :
    MachineState -> MachineState.
  Admitted.

  (*"""
  add ri rj A compute [rj]u + [A]u and store result in ri overflow
  """*)
  Definition pureOp_add (ri rj : fin registerCount) (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  sub ri rj A compute [rj]u − [A]u and store result in ri borrow
  """*)
  Definition pureOp_sub (ri rj : fin registerCount) (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  mull ri rj A compute [rj]u × [A]u and store least significant bits of result in ri overflow
  """*)
  Definition pureOp_mull (ri rj : fin registerCount) (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  umulh ri rj A compute [rj]u × [A]u and store most significant bits of result in ri overflow
  """*)
  Definition pureOp_umulh (ri rj : fin registerCount) (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  smulh ri rj A compute [rj]s × [A]s and store most significant bits of result in ri over/underflow
  """*)
  Definition pureOp_smulh (ri rj : fin registerCount) (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  udiv ri rj A compute quotient of [rj]u/[A]u and store result in ri [A]u = 0
  """*)
  Definition pureOp_udiv (ri rj : fin registerCount) (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  umod ri rj A compute remainder of [rj]u/[A]u and store result in ri [A]u = 0
  """*)
  Definition pureOp_umod (ri rj : fin registerCount) (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  shl ri rj A shift [rj] by [A]u bits to the left and store result in ri MSB of [rj]
  """*)
  Definition pureOp_shl (ri rj : fin registerCount) (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  shr ri rj A shift [rj] by [A]u bits to the right and store result in ri LSB of [rj]
  """*)
  Definition pureOp_shr (ri rj : fin registerCount) (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  cmpe ri A none (“compare equal”) [ri] = [A]
  """*)
  Definition pureOp_cmpe (ri : fin registerCount) (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  cmpa ri A none (“compare above”, unsigned) [ri]u > [A]u
  """*)
  Definition pureOp_cmpa (ri : fin registerCount) (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  cmpae ri A none (“compare above or equal”, unsigned) [ri]u ≥ [A]u
  """*)
  Definition pureOp_cmpae (ri : fin registerCount) (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  cmpg ri A none (“compare greater”, signed) [ri]s > [A]s
  """*)
  Definition pureOp_cmpg (ri : fin registerCount) (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  cmpge ri A none (“compare greater or equal”, signed) [ri]s ≥ [A]s
  """*)
  Definition pureOp_cmpge (ri : fin registerCount) (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  mov ri A store [A] in ri
  """*)
  Definition pureOp_mov (ri : fin registerCount) (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  cmov ri A if flag = 1, store [A] in ri
  """*)
  Definition pureOp_cmov (ri : fin registerCount) (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  jmp A set pc to [A]
  """*)
  Definition pureOp_jmp (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  cjmp A if flag = 1, set pc to [A] (else increment pc as usual)
  """*)
  Definition pureOp_cjmp (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  cnjmp A if flag = 0, set pc to [A] (else increment pc as usual)
  """*)
  Definition pureOp_cnjmp (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  store.b A ri store the least-significant byte of [ri] at the [A]u-th byte in memory
  """*)
  Definition pureOp_store_b (A : Word) (ri : fin registerCount) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  load.b ri A store into ri (with zero-padding in front) the [A]u-th byte in memory
  """*)
  Definition pureOp_load_b (ri : fin registerCount) (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  store.w A ri store [ri] at the word in memory that is aligned to the [A]w-th byte
  """*)
  Definition pureOp_store_w (ri : fin registerCount) (A : Word) :
    MachineState -> MachineState.
  Admitted.


  (*"""
  load.w ri A store into ri the word in memory that is aligned to the [A]w-th byte
  """*)
  Definition pureOp_load_w (ri : fin registerCount) (A : Word) :
    MachineState -> MachineState.
  Admitted.



End TinyRAMTypes.


