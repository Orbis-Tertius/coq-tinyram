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
  Definition RegisterBytes :
    forall (r:Word), 
    { v : Vector.t Byte wordSizeEighth | 
    vector_length_coerce wordSizeDiv8 r = vector_concat v }.
  intros r.
  remember (vector_length_coerce wordSizeDiv8 r) as r8.
  exists (vector_unconcat r8).
  rewrite vector_concat_inv1.
  reflexivity.
  Defined.

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
  Definition Memory_Block_Load_Store
    (m : Memory)
    (idx : nat) (lip : idx < 2 ^ wordSize)
    (blksz : nat) (lbp : blksz < 2 ^ wordSize)
    (block : Vector.t Byte blksz) :
    Vector.t Byte blksz * Memory.
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
    (idx : nat) (lip : idx < 2 ^ wordSize)
    (blksz : nat) (lbp : blksz < 2 ^ wordSize) :
    Vector.t Byte blksz :=
  fst (Memory_Block_Load_Store m _ lip _ lbp (Vector.const zeroByte _)).
   
  Definition Memory_Block_Store 
    (m : Memory)
    (idx : nat) (lip : idx < 2 ^ wordSize)
    (blksz : nat) (lbp : blksz < 2 ^ wordSize)
    (block : Vector.t Byte blksz) :
    Memory :=
  snd (Memory_Block_Load_Store m _ lip _ lbp block).

  (* Since a Word is a memory block, it can be stored as well. *)
  Definition Memory_Register_Store 
    (m : Memory)
    (idx : nat) (lip : idx < 2 ^ wordSize)
    (reg : Word) :
    Memory.
  destruct (RegisterBytes reg) as [block eq].
  assert (0 < wordSizeEighth * 8).
  { rewrite <- wordSizeDiv8. apply wordSizePos. }
  assert (0 < wordSizeEighth).
  { lia. }   
  apply (Memory_Block_Store m idx lip wordSizeEighth).
  2: { exact block. }
  rewrite wordSizeDiv8.
  transitivity (wordSizeEighth * 8).
  { lia. }
  apply pow_gt_lin_r.
  lia.
  Defined.

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
      (* Note: Input tapes are READ IN. 
         They are NOT part of the state. *)


        (*primaryInput : InputTape primary;*)
        (*auxiliaryInput : InputTape auxiliary;*)

End TinyRAMTypes.


