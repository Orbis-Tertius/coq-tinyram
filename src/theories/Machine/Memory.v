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
  Coding.
Import PeanoNat.Nat.

Module TinyRAMMem (Params : TinyRAMParameters).
  Module TRCod := TinyRAMCoding Params.
  Import TRCod.
  Export TRCod.

  (*"""
  Memory, which is a linear array of 2^[wordSize] bytes.
  """*)
  Definition Memory := VectorDef.t Byte (2 ^ wordSize).

  (*"""
  We say that a block is aligned to the A-th byte if its
  least-significant byte is at address A.
  """*)

  (*"""
  When storing or loading blocks of multiple bytes, 
  [...] the least-significant byte is at the lowest address.
  """*)
  Definition Memory_Block_Load
    (m : Memory)
    (idx blksz : fin (2 ^ wordSize)) :
    VectorDef.t Byte (proj1_sig blksz) :=
    VectorDef.rev (Block_Load m idx blksz).

  (*"""
  When storing or loading blocks of multiple bytes, 
  [...] the least-significant byte is at the lowest address.
  """*)
  Definition Memory_Block_Store 
    (m : Memory)
    (idx blksz : fin (2 ^ wordSize))
    (block : VectorDef.t Byte (proj1_sig blksz)) :
    Memory :=
    Block_Store m idx blksz (VectorDef.rev block).

  (* Since a Word is a memory block, it can be loaded as well. *)
  Definition Memory_Word_Load
    (m : Memory)
    (idx : fin (2 ^ wordSize)) :
    Word.
    unfold Word.
    apply vector_concat.
    apply (Memory_Block_Load m idx wordSizeEighthFin).
  Defined.

  (* Since a Word is a memory block, it can be stored as well. *)
  Definition Memory_Word_Store 
    (m : Memory)
    (idx : fin (2 ^ wordSize))
    (reg : Word) :
    Memory.
    apply (Memory_Block_Store m idx wordSizeEighthFin).
    apply vector_unconcat, reg.
  Defined.

  Definition Register_Index (w : Word) : fin (2 ^ wordSize) :=
    bitvector_fin_big w.

  Definition Memory_Word_Load_from_Reg 
    (m : Memory) (idx : Word) : Word :=
    Memory_Word_Load m (Register_Index idx).

  Definition Memory_Word_Store_from_Reg 
    (m : Memory) (idx reg : Word) : Memory :=
    Memory_Word_Store m (Register_Index idx) reg.


Theorem Memory_Word_Store_Load_from_Reg: forall
    (m : Memory)
    (idx reg : Word),
    Memory_Word_Load_from_Reg 
      (Memory_Word_Store_from_Reg m idx reg)
      idx
    = reg.
Proof.
  intros.
  unfold Memory_Word_Store_from_Reg, Memory_Word_Load_from_Reg.
  unfold Memory_Word_Store, Memory_Word_Load.
  unfold Memory_Block_Load, Memory_Block_Store.
  rewrite Block_Store_Load, vector_rev_rev_id, vector_concat_inv1.
  reflexivity.
Qed.

Theorem Memory_Word_Store_Store_from_Reg: forall
    (m : Memory)
    (idx reg1 reg2 : Word),
    Memory_Word_Store_from_Reg 
      (Memory_Word_Store_from_Reg m idx reg1)
      idx reg2
    = Memory_Word_Store_from_Reg m idx reg2.
Proof.
  intros.
  unfold Memory_Word_Store_from_Reg, Memory_Word_Load_from_Reg.
  unfold Memory_Word_Store, Memory_Word_Load.
  unfold Memory_Block_Load, Memory_Block_Store.
  rewrite Block_Store_Store; reflexivity.
Qed.

Theorem Memory_Word_Store_Load_from_Reg_Irr : forall
    (m : Memory)
    (idx1 idx2 block: Word),
    (*  |----------------|
          |--|      |--|
          1  1+     2  2+   *)
    (((bitvector_nat_big idx1 + wordSizeEighth <= bitvector_nat_big idx2) /\
      (bitvector_nat_big idx2 + wordSizeEighth < 2 ^ wordSize)) \/
    (*  |----------------|
          |--|      |--|
          2  2+     1  1+   *)
     ((bitvector_nat_big idx2 + wordSizeEighth <= bitvector_nat_big idx1) /\
      (bitvector_nat_big idx1 + wordSizeEighth < 2 ^ wordSize)) \/
    (*  |----------------|
        -|    |--|      |-
         2+   1  1+     2   *)
     ((bitvector_nat_big idx1 + wordSizeEighth <= bitvector_nat_big idx2) /\
      ((bitvector_nat_big idx2 + wordSizeEighth) mod 2 ^ wordSize <= bitvector_nat_big idx1) /\
      (2 ^ wordSize < bitvector_nat_big idx2 + wordSizeEighth)) \/
    (*  |----------------|
        -|    |--|      |-
         1+   2  2+     1   *)
     ((bitvector_nat_big idx2 + wordSizeEighth <= bitvector_nat_big idx1) /\
      ((bitvector_nat_big idx1 + wordSizeEighth) mod 2 ^ wordSize <= bitvector_nat_big idx2)/\
      (2 ^ wordSize < bitvector_nat_big idx1   + wordSizeEighth))) ->
    Memory_Word_Load_from_Reg 
      (Memory_Word_Store_from_Reg m idx1 block)
      idx2
    = Memory_Word_Load_from_Reg m idx2.
Proof.
  intros.
  unfold Memory_Word_Store_from_Reg, Memory_Word_Load_from_Reg.
  unfold Memory_Word_Store, Memory_Word_Load.
  unfold Memory_Block_Load, Memory_Block_Store.
  rewrite Block_Store_Load_Irr;[reflexivity|assumption].
Qed.

Theorem Memory_Word_Store_Store_from_Reg_Swap : forall
    (m : Memory)
    (idx1 idx2 block block': Word),
    (*  |----------------|
          |--|      |--|
          1  1+     2  2+   *)
    (((bitvector_nat_big idx1  + wordSizeEighth <= bitvector_nat_big idx2) /\
      (bitvector_nat_big idx2  + wordSizeEighth < 2 ^ wordSize)) \/
    (*  |----------------|
          |--|      |--|
          2  2+     1  1+   *)
     ((bitvector_nat_big idx2  + wordSizeEighth <= bitvector_nat_big idx1) /\
      (bitvector_nat_big idx1  + wordSizeEighth < 2 ^ wordSize)) \/
    (*  |----------------|
        -|    |--|      |-
         2+   1  1+     2   *)
     ((bitvector_nat_big idx1  + wordSizeEighth <= bitvector_nat_big idx2) /\
      ((bitvector_nat_big idx2  + wordSizeEighth) mod 2 ^ wordSize <= bitvector_nat_big idx1) /\
      (2 ^ wordSize < bitvector_nat_big idx2  + wordSizeEighth)) \/
    (*  |----------------|
        -|    |--|      |-
         1+   2  2+     1   *)
     ((bitvector_nat_big idx2  + wordSizeEighth <= bitvector_nat_big idx1) /\
      ((bitvector_nat_big idx1  + wordSizeEighth) mod 2 ^ wordSize <= bitvector_nat_big idx2)/\
      (2 ^ wordSize < bitvector_nat_big idx1  + wordSizeEighth))) ->
    Memory_Word_Store_from_Reg 
      (Memory_Word_Store_from_Reg m idx1 block)
      idx2 block'
    = Memory_Word_Store_from_Reg 
        (Memory_Word_Store_from_Reg m idx2 block')
        idx1 block.
Proof.
  intros.
  unfold Memory_Word_Store_from_Reg, Memory_Word_Load_from_Reg.
  unfold Memory_Word_Store, Memory_Word_Load.
  unfold Memory_Block_Load, Memory_Block_Store.
  rewrite Block_Store_Store_Swap;[reflexivity|assumption].
Qed.

Theorem Memory_Word_Load_from_Reg_const : forall 
  (idx : Word)
  (val : Byte),
  Memory_Word_Load_from_Reg (VectorDef.const val _) idx
  = vector_concat (VectorDef.const val _).
Proof.
  intros.
  unfold Memory_Word_Load_from_Reg, Memory_Word_Load, Memory_Block_Load.
  rewrite Block_Load_const.
  rewrite rev_const; reflexivity.
Qed.

End TinyRAMMem.


