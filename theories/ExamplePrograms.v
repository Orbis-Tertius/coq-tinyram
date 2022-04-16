From Coq Require Import
     Lia VectorDef VectorEq List ZArith ProofIrrelevance.
From TinyRAM.Utils Require Import
     Fin Vectors BitVectors.
From TinyRAM.Machine Require Import
     Parameters InstructionTheorems.
Import PeanoNat.Nat VectorNotations.

From ITree Require Import
     ITree
     ITreeFacts
     Events.State
     Events.StateFacts.

Definition mk_fin {m} : forall n, n < m -> fin m.
  intros; exists n; assumption. Defined.

Theorem replace_unfold : forall {A n} (l : Vector.t A n) h f x
  (lt : S f < S n),
  replace (h :: l) (mk_fin (S f) lt) x
  = h :: replace l (mk_fin f (Lt.lt_S_n _ _ lt)) x.
Proof.
  intros.
  simpl. repeat f_equal.
  apply subset_eq_compat.
  reflexivity.
Qed.

Theorem replace_replace : forall {A n} (l : Vector.t A n) f x y,
  replace (replace l f x) f y = replace l f y.
Proof.
  induction l; [ reflexivity | ].
  intros [f flt] x y.
  destruct f; [ reflexivity | ].
  simpl.
  rewrite IHl.
  reflexivity.
Qed.

Theorem replace_swap : forall {A n} (l : Vector.t A n) f g x y,
  proj1_sig f <> proj1_sig g ->
  replace (replace l f x) g y = replace (replace l  g y) f x.
Proof.
  induction l; [ intros [f lt]; lia | ].
  intros [f flt] [g glt] x y neq; simpl in neq.
  destruct f.
  - destruct g; [ contradiction | reflexivity ].
  - destruct g; [ reflexivity | ].
    simpl; rewrite IHl; [ reflexivity |  simpl; lia].
Qed.

Theorem replace_nth_irr : forall {A n} (l : Vector.t A n) f g x,
  proj1_sig f <> proj1_sig g ->
  nth (replace l f x) g = nth l g.
Proof.
  induction l; [ reflexivity | ].
  intros [f flt] [g glt] x neq; simpl in neq.
  destruct f.
  - destruct g; [ contradiction | reflexivity ].
  - destruct g; [ reflexivity | simpl; rewrite IHl; auto ].
Qed.

Theorem bv_eq_big_conv : forall k n m,
  n < 2 ^ k -> m < 2 ^ k ->
  bv_eq (nat_bitvector_big k n)
        (nat_bitvector_big k m) =
  (n =? m).
Proof.
  intros.
  destruct (n =? m) eqn:nqVal.
  - rewrite eqb_eq in nqVal.
    rewrite nqVal, bv_eq_equiv.
    rewrite nat_bitvector_big_inj; auto.
  - destruct (bv_eq _ _) eqn:bvVal.
    + rewrite bv_eq_equiv in bvVal.
      rewrite nat_bitvector_big_inj in bvVal; try assumption.
      rewrite bvVal, eqb_refl in nqVal.
      discriminate nqVal.
    + reflexivity.
Qed.

Theorem bv_incr_fold : forall k n m,
  n + m < 2 ^ k ->
  bv_incr n (nat_bitvector_big k m) =
  nat_bitvector_big k (n + m).
Proof.
  intros k n m lt.
  unfold bv_incr.
  rewrite nat_bitvector_big_inv; [ | lia ].
  rewrite mod_small; auto.
Qed.


Theorem bv_sub_correct_pos : 
  forall k n m,
  n < 2 ^ k -> m < 2 ^ k -> m <= n ->
  Vector.tl (bv_sub (nat_bitvector_big k n)
            (nat_bitvector_big k m))
  = nat_bitvector_big k (n - m).
  intros k n m nlt mlt le.
  rewrite bv_sub_correct_1.
  unfold nat_bitvector_big; fold nat_bitvector_big.
  simpl; f_equal.
  repeat rewrite nat_bitvector_big_inv; try assumption.
  rewrite add_sub_swap; [ | assumption ].
  rewrite <- add_mod_idemp_r; [| apply pow_nonzero; lia].
  rewrite mod_same; [| apply pow_nonzero; lia].
  rewrite add_0_r.
  rewrite mod_small; lia.
Qed.

Theorem bv_add_correct_mod :
  forall {n : nat} (n1 n2 : nat),
  n1 < 2 ^ n ->
  n2 < 2 ^ n ->
  (n1 + n2) mod 2 ^ n =
  bitvector_nat_big
	(VectorDef.tl (bv_add (nat_bitvector_big n n1) (nat_bitvector_big n n2))).
Proof.
  intros.
  rewrite bv_add_correct_1.
  rewrite nat_bitvector_big_inv;[|assumption].
  rewrite nat_bitvector_big_inv;[|assumption].
  unfold nat_bitvector_big.
  simpl VectorDef.tl.
  fold nat_bitvector_big.
  rewrite nat_bitvector_big_inv;[reflexivity|].
  apply mod_upper_bound; lia.
Qed.

Theorem bv_add_correct_mod_2 :
  forall {n : nat} (n1 n2 : nat),
  n1 < 2 ^ n ->
  n2 < 2 ^ n ->
  nat_bitvector_big _ ((n1 + n2) mod 2 ^ n) =
	VectorDef.tl (bv_add (nat_bitvector_big n n1) (nat_bitvector_big n n2)).
Proof.
  intros.
  apply nat_bitvector_big_inj;try (apply mod_upper_bound; lia).
  rewrite nat_bitvector_big_inv;[|assumption].
  rewrite nat_bitvector_big_inv;[|assumption].
  reflexivity.
Qed.

(* Storing then loading a block at the same address gives the same block back. *)
Theorem Block_Store_Load : forall {B memsz}
    (m : Vector.t B memsz)
    (idx blksz: fin memsz)
    (block : Vector.t B (proj1_sig blksz)),
    Block_Load 
      (Block_Store m idx blksz block)
      idx blksz
    = block.
Proof.
  intros B memsz m [idx idxLT] [blksz blkszLT] block.
  simpl in block.
  unfold Block_Store, Block_Load.
  destruct (Block_Lem idx blksz memsz idxLT blkszLT) as 
    [[tl eq]|[blk2[blk1[idx2[eq1 [eq2 eq3]]]]]].
  - destruct (splitat _ (eq_rect _ _ m _ eq)) as [v12 v3] eqn:speq;
    apply VectorSpec.append_splitat in speq.
    destruct (splitat idx v12) as [v1 v2] eqn:speq2;
    apply VectorSpec.append_splitat in speq2.
    rewrite speq2 in speq; clear speq2 v12.
    unfold eq_rect_r; repeat rewrite <- cast_rew.
    rewrite cast_trans, cast_id.
    destruct (splitat _ ) as [v12 v3'] eqn:speq2;
    apply VectorSpec.append_splitat in speq2.
    destruct (splitat _ ) as [v1' v2'] eqn:speq3;
    apply VectorSpec.append_splitat in speq3.
    rewrite speq3 in speq2; clear speq3 v12.
    apply app_eq_l, app_eq_r in speq2.
    symmetry; assumption.
  - destruct (splitat _ (eq_rect _ _ m _ _)) as [v12 v3] eqn:speq;
    apply VectorSpec.append_splitat in speq.
    unfold eq_rect_r; repeat rewrite <- cast_rew; rewrite cast_trans.
    destruct (splitat blk1 _) as [block1 block2] eqn:speq2;
    apply VectorSpec.append_splitat in speq2.
    destruct (splitat blk2 _) as [v1 v2] eqn:speq3;
    apply VectorSpec.append_splitat in speq3.
    rewrite <- cast_rew, cast_trans, cast_id.
    destruct (splitat _ _) as [v12' v3'] eqn:speq4;
    apply VectorSpec.append_splitat in speq4.
    destruct (splitat blk2 _) as [v1' v2'] eqn:speq5;
    apply VectorSpec.append_splitat in speq5.
    rewrite <- cast_rew, cast_trans.
    rewrite speq5 in speq4; clear speq5 v12'.
    assert (block2 = v1'); [repeat apply app_eq_l in speq4; assumption|].
    apply app_eq_r in speq4.
    rewrite <- speq4, <- H.
    clear H speq4 v1' v3' v2' speq3 v1 v2 speq v3 v12.
    rewrite <- speq2.
    rewrite cast_trans, cast_id; reflexivity.
Qed.

(*Storing twice at the same place is the same as storing once.*)
Theorem Block_Store_Store : forall {B memsz}
    (m : Vector.t B memsz)
    (idx blksz: fin memsz)
    (block block' : Vector.t B (proj1_sig blksz)),
    Block_Store 
      (Block_Store m idx blksz block)
      idx blksz block'
    = Block_Store m idx blksz block'.
Proof.
  intros B memsz m [idx idxLT] [blksz blkszLT] block block'.
  simpl in block, block'.
  unfold Block_Store.
  destruct (Block_Lem idx blksz memsz idxLT blkszLT) as 
    [[tl eq]|[blk2[blk1[idx2[eq1 [eq2 eq3]]]]]].
  - destruct (splitat _ (eq_rect _ _ m _ eq)) as [v12 v3] eqn:speq;
    apply VectorSpec.append_splitat in speq.
    destruct (splitat idx v12) as [v1 v2] eqn:speq2;
    apply VectorSpec.append_splitat in speq2.
    rewrite speq2 in speq; clear speq2 v12.
    unfold eq_rect_r; repeat rewrite <- cast_rew.
    rewrite cast_trans, cast_id.
    destruct (splitat _ ) as [v12 v3'] eqn:speq2;
    apply VectorSpec.append_splitat in speq2.
    destruct (splitat _ ) as [v1' v2'] eqn:speq3;
    apply VectorSpec.append_splitat in speq3.
    rewrite speq3 in speq2; clear speq3 v12.
    rewrite <- cast_rew.
    symmetry; repeat f_equal.
    + repeat apply app_eq_l in speq2; assumption.
    + apply app_eq_r in speq2; assumption.
  - destruct (splitat _ (eq_rect _ _ m _ _)) as [v12 v3] eqn:speq;
    apply VectorSpec.append_splitat in speq.
    unfold eq_rect_r; repeat rewrite <- cast_rew; rewrite cast_trans.
    destruct (splitat blk1 _) as [block1 block2] eqn:speq2;
    apply VectorSpec.append_splitat in speq2.
    destruct (splitat blk2 _) as [v1 v2] eqn:speq3;
    apply VectorSpec.append_splitat in speq3.
    rewrite <- cast_rew, cast_trans, cast_id.
    destruct (splitat _ _) as [v12' v3'] eqn:speq4;
    apply VectorSpec.append_splitat in speq4.
    destruct (splitat blk2 _) as [v1' v2'] eqn:speq5;
    apply VectorSpec.append_splitat in speq5.
    rewrite cast_trans.
    destruct (splitat blk1 _) as [block1' block2'] eqn:speq6;
    apply VectorSpec.append_splitat in speq6.
    rewrite speq5 in speq4; clear speq5 v12'.
    apply app_eq_l, app_eq_r in speq4.
    rewrite speq4; reflexivity.
Qed.

Theorem cast_swap : forall {A n m} (v : Vector.t A n) (u : Vector.t A m)
  (eq : n = m),
  cast v eq = u <-> v = cast u (eq_sym eq).
Proof.
  intros.
  split.
  - intros; rewrite <- H, cast_trans, cast_id; reflexivity.
  - intros; rewrite H, cast_trans, cast_id; reflexivity.
Qed.

Theorem cast_f_apply: forall {A n m} (v u : Vector.t A n) (eq : n = m),
  v = u <-> cast v eq = cast u eq.
Proof.
  intros.
  split.
  - intro H; rewrite H; reflexivity.
  - apply cast_inj.
Qed.

(*If searching for a block in a memory after a different block was
  stored, we can ignore that storage. *)
Theorem Block_Store_Load_Irr : forall {B memsz}
    (m : Vector.t B memsz)
    (idx1 idx2 blksz: fin memsz)
    (block : Vector.t B (proj1_sig blksz)),
    (*  |----------------|
          |--|      |--|
          1  1+     2  2+   *)
    (((proj1_sig idx1 + proj1_sig blksz) <= proj1_sig idx2 /\
      (proj1_sig idx2 + proj1_sig blksz) < memsz) \/
    (*  |----------------|
          |--|      |--|
          2  2+     1  1+   *)
     ((proj1_sig idx2 + proj1_sig blksz) <= proj1_sig idx1 /\
      (proj1_sig idx1 + proj1_sig blksz) < memsz) \/
    (*  |----------------|
        -|    |--|      |-
         2+   1  1+     2   *)
     ((proj1_sig idx1 + proj1_sig blksz) <= proj1_sig idx2 /\
      (proj1_sig idx2 + proj1_sig blksz) mod memsz <= proj1_sig idx1 /\
      memsz < proj1_sig idx2 + proj1_sig blksz) \/
    (*  |----------------|
        -|    |--|      |-
         1+   2  2+     1   *)
     ((proj1_sig idx2 + proj1_sig blksz) <= proj1_sig idx1 /\
      (proj1_sig idx1 + proj1_sig blksz) mod memsz <= proj1_sig idx2/\
      memsz < proj1_sig idx1 + proj1_sig blksz)) ->
    Block_Load 
      (Block_Store m idx1 blksz block)
      idx2 blksz
    = Block_Load m idx2 blksz.
Proof.
  intros B memsz m [idx idxLT] [idx2 idx2LT] 
         [blksz blkszLT] block H.
  simpl in H, block.
  unfold Block_Store, Block_Load.
  destruct (Block_Lem idx blksz memsz idxLT blkszLT) as 
    [[tl1 eq1]|[blk21[blk11[idx21[eq11 [eq21 eq31]]]]]];
  destruct (Block_Lem idx2 blksz memsz idx2LT blkszLT) as 
    [[tl2 eq2]|[blk22[blk12[idx22[eq12 [eq22 eq32]]]]]]; try lia.
  - destruct (splitat _ (eq_rect _ _ m _ eq1)) as [v12 v3] eqn:speq;
    apply VectorSpec.append_splitat in speq;
    rewrite <- cast_rew, cast_swap in speq.
    destruct (splitat idx v12) as [v1 v2] eqn:speq2;
    apply VectorSpec.append_splitat in speq2.
    rewrite speq2 in speq; clear speq2 v12.
    unfold eq_rect_r; repeat rewrite <- cast_rew.
    destruct (splitat _ _) as [v12 v3'] eqn:speq2;
    apply VectorSpec.append_splitat in speq2.
    destruct (splitat _ _) as [v1' v2'] eqn:speq3;
    apply VectorSpec.append_splitat in speq3.
    rewrite speq3 in speq2; clear speq3 v12.
    destruct (splitat _ _) as [v4 v5] eqn:speq3;
    apply VectorSpec.append_splitat in speq3.
    rewrite cast_swap in speq3.
    rewrite speq3 in speq; clear speq3 m.
    destruct (splitat _ _) as [v6 v7] eqn:speq4;
    apply VectorSpec.append_splitat in speq4.
    rewrite speq4 in speq; clear speq4 v4.
    destruct H as [[H0 H1]|[[H0 H1]|[[H0[H1 H2]]|[H0[H1 H2]]]]]; try lia.
    * (*  idx|---| idx2|---|
        |--------idx2--|blk|-tl2|
        |-idx|blk|----tl1-------| *)
      assert (tl1 = (idx2 - blksz - idx) + blksz + tl2);[lia|].
      destruct (splitat _ (cast v3 H)) as [v8 v9] eqn:speq4;
      apply VectorSpec.append_splitat in speq4.
      destruct (splitat _ v8) as [v10 v11] eqn:speq5;
      apply VectorSpec.append_splitat in speq5.
      rewrite speq5, cast_swap in speq4; clear speq5 v8.
      rewrite speq4, cast_app_left, <- cast_app_assoc_2 in speq2.
      rewrite <- cast_app_assoc_2, cast_app_right in speq2.
      repeat rewrite cast_trans in speq2.
      rewrite cast_app_r, cast_app_r in speq2.
      apply app_eq_l, app_eq_r in speq2.
      rewrite speq2 in speq4; clear speq2.
      symmetry in speq; rewrite cast_swap, cast_trans in speq.
      assert (idx + blksz + tl1 = idx + blksz + idx2 - blksz - idx + blksz + tl2);[lia|].
      rewrite (cast_f_apply _ _ H2) in speq.
      rewrite speq4 in speq; clear speq4.
      rewrite cast_app_left, <- cast_app_assoc_2,
              <- cast_app_assoc_2, cast_app_right in speq.
      repeat rewrite cast_trans in speq.
      repeat rewrite cast_app_r in speq.
      apply app_eq_l, app_eq_r in speq; assumption.
    * (* idx2|---|  idx|---|
        |---------idx--|blk|-tl1|
        |idx2|blk|----tl2-------| *)
      assert (idx = idx2 + blksz + (tl2 - blksz - tl1));[lia|].
      destruct (splitat _ (cast v1 H)) as [v8 v9] eqn:speq4;
      apply VectorSpec.append_splitat in speq4.
      destruct (splitat _ v8) as [v10 v11] eqn:speq5;
      apply VectorSpec.append_splitat in speq5;
      rewrite speq5 in speq4; clear speq5 v8.
      rewrite cast_swap in speq4.
      rewrite <- cast_app_assoc_1 in speq2.
      rewrite speq4, cast_app_right in speq2.
      rewrite <- cast_app_assoc_1 in speq2.
      repeat rewrite cast_trans in speq2.
      rewrite cast_app_l in speq2.
      apply app_eq_l, app_eq_r in speq2.
      rewrite speq2 in speq4; clear speq2.
      symmetry in speq; rewrite cast_swap in speq.
      rewrite cast_trans in speq.
      assert ((idx + blksz) + tl1 = (idx2 + blksz) + ((tl2 - blksz - tl1) + blksz + tl1));[lia|].
      rewrite (cast_f_apply _ _ H2) in speq.
      rewrite speq4 in speq; clear speq4.
      rewrite cast_app_right, <- cast_app_assoc_1 in speq.
      repeat rewrite cast_app_right in speq.
      rewrite <- cast_app_assoc_1 in speq.
      repeat rewrite cast_trans in speq.
      repeat rewrite cast_app_l in speq.
      apply app_eq_l, app_eq_r in speq; assumption.
  - repeat rewrite <- cast_rew.
    destruct (splitat _ (cast m _)) as [v12 v3] eqn:speq;
    apply VectorSpec.append_splitat in speq.
    rewrite cast_swap in speq.
    destruct (splitat idx _) as [v4 v5] eqn:speq2;
    apply VectorSpec.append_splitat in speq2.
    unfold eq_rect_r; repeat rewrite <- cast_rew; rewrite cast_trans.
    destruct (splitat _ _) as [v8 v9] eqn:speq3;
    apply VectorSpec.append_splitat in speq3.
    destruct (splitat blk22 _) as [block12 block22] eqn:speq4;
    apply VectorSpec.append_splitat in speq4.
    unfold eq_rect_r; rewrite <- cast_rew, cast_trans.
    destruct (splitat (_ + _) _) as [v10 v11] eqn:speq5;
    apply VectorSpec.append_splitat in speq5.
    rewrite cast_swap in speq5; rewrite speq5 in speq; clear speq5.
    destruct (splitat blk22 v10) as [block12' block22'] eqn:speq6;
    apply VectorSpec.append_splitat in speq6.
    unfold eq_rect_r; rewrite <- cast_rew, cast_trans.
    f_equal.
    rewrite speq6 in speq; clear speq6 v10.
    rewrite speq4 in speq3; clear speq4 v8.
    rewrite speq2 in speq; clear speq2 v12.
    destruct H as [[H0 H1]|[[H0 H1]|[[H0[H1 H2]]|[H0[H1 H2]]]]]; try lia.
    (* ----|  idx|---|  idx2|----
       |---idx---|bks|---tl1----|
       |b22|-----idx22------|b12| *)
    assert (blk22 = (idx2 + blksz) mod memsz);[
    rewrite PeanoNat.Nat.mod_eq; try rewrite Arith.div_bet_1; lia|].
    assert (idx22 = (idx - blk22) + blksz + (tl1 - blk12));[lia|].
    destruct (splitat _ (cast block22 H3)) as [vAB vC] eqn:speq5;
    apply VectorSpec.append_splitat in speq5; rewrite cast_swap in speq5.
    destruct (splitat _ vAB) as [vA vB] eqn:speq6;
    apply VectorSpec.append_splitat in speq6;
    rewrite speq6 in speq5; clear speq6 vAB.
    destruct (splitat _ (cast block22' H3)) as [vXY vZ] eqn:speq6;
    apply VectorSpec.append_splitat in speq6; rewrite cast_swap in speq6.
    destruct (splitat _ vXY) as [vX vY] eqn:speq7;
    apply VectorSpec.append_splitat in speq7;
    rewrite speq7 in speq6; clear speq7 vXY.
    assert (idx = blk22 + (idx22 - (blksz + (tl1 - blk12))));[lia|].
    destruct (splitat _ (cast v4 H4)) as [v1 v2] eqn:speq2;
    apply VectorSpec.append_splitat in speq2; rewrite cast_swap in speq2.
    assert (tl1 = idx22 - ((idx - blk22) + blksz) + blk12);[lia|].
    destruct (splitat _ (cast v3 H5)) as [v6 v7] eqn:speq4;
    apply VectorSpec.append_splitat in speq4; rewrite cast_swap in speq4.
    rewrite speq4 in speq3, speq; clear speq4 v3.
    rewrite speq2 in speq3, speq; clear speq2 v4.
    rewrite speq5 in speq3; clear speq5 block22.
    rewrite speq6 in speq; clear speq6 block22'.
    f_equal.
    + repeat (rewrite <- cast_app_assoc_2 in speq||rewrite cast_app_left in speq||rewrite cast_app_right in speq);
      repeat rewrite cast_trans in speq.
      repeat (rewrite <- cast_app_assoc_2 in speq3||rewrite cast_app_left in speq3||rewrite cast_app_right in speq3);
      repeat rewrite cast_trans in speq3.
      rewrite cast_swap, cast_trans in speq.
      rewrite cast_swap, cast_trans in speq3.
      rewrite cast_app_r in speq; apply app_eq_r in speq.
      rewrite cast_app_r in speq3; apply app_eq_r in speq3.
      rewrite speq, speq3; reflexivity.      
    + repeat (rewrite <- cast_app_assoc_1 in speq||rewrite cast_app_left in speq||rewrite cast_app_right in speq);
      repeat rewrite cast_trans in speq.
      repeat (rewrite <- cast_app_assoc_1 in speq3||rewrite cast_app_left in speq3||rewrite cast_app_right in speq3);
      repeat rewrite cast_trans in speq3.
      rewrite cast_swap, cast_trans in speq.
      rewrite cast_swap, cast_trans in speq3.
      rewrite cast_app_l in speq; apply app_eq_l in speq.
      rewrite cast_app_l in speq3; apply app_eq_l in speq3.
      rewrite speq, speq3; reflexivity.
  - repeat rewrite <- cast_rew.
    destruct (splitat _ (cast m _)) as [v12 v3] eqn:speq;
    apply VectorSpec.append_splitat in speq.
    rewrite cast_swap in speq.
    destruct (splitat blk21 _) as [v4 v5] eqn:speq2;
    apply VectorSpec.append_splitat in speq2.
    unfold eq_rect_r; repeat rewrite <- cast_rew; rewrite cast_trans.
    destruct (splitat blk11 _) as [v8 v9] eqn:speq3;
    apply VectorSpec.append_splitat in speq3.
    rewrite <- cast_rew, cast_trans.
    destruct (splitat _ _) as [v6 v7] eqn:speq4;
    apply VectorSpec.append_splitat in speq4.
    destruct (splitat idx2 _) as [v10 v11] eqn:speq5;
    apply VectorSpec.append_splitat in speq5.
    destruct (splitat _ _) as [v13 v14] eqn:speq6;
    apply VectorSpec.append_splitat in speq6.
    destruct (splitat idx2 _) as [v15 v16] eqn:speq7;
    apply VectorSpec.append_splitat in speq7.
    rewrite cast_swap in speq6; rewrite speq6 in speq; clear speq6 m.
    rewrite speq5 in speq4; clear speq5 v6.
    rewrite speq7 in speq; clear speq7 v13.
    rewrite speq2 in speq; clear speq2 v12.
    destruct H as [[H0 H1]|[[H0 H1]|[[H0[H1 H2]]|[H0[H1 H2]]]]]; try lia.
    (* ----| idx2|---|   idx|----
       |---idx2--|bks|---tl2----|
       |b21|-----idx21------|b11| *)
    assert (blk21 = (idx + blksz) mod memsz);[
    rewrite PeanoNat.Nat.mod_eq; try rewrite Arith.div_bet_1; lia|].
    assert (idx21 = (idx2 - blk21) + blksz + (tl2 - blk11));[lia|].
    destruct (splitat _ (cast v5 H3)) as [vAB vC] eqn:speq2;
    apply VectorSpec.append_splitat in speq2; rewrite cast_swap in speq2.
    destruct (splitat _ vAB) as [vA vB] eqn:speq6;
    apply VectorSpec.append_splitat in speq6;
    rewrite speq6 in speq2; clear speq6 vAB.
    assert (tl2 = (idx21 - (idx2 - blk21) - blksz) + blk11);[lia|].
    destruct (splitat _ (cast v7 H4)) as [v20 v21] eqn:speq6;
    apply VectorSpec.append_splitat in speq6; rewrite cast_swap in speq6.
    destruct (splitat _ (cast v14 H4)) as [v22 v23] eqn:speq7;
    apply VectorSpec.append_splitat in speq7; rewrite cast_swap in speq7.
    assert (idx2 = blk21 + (idx21 - blksz - (tl2 - blk11)));[lia|].
    destruct (splitat _ (cast v10 H5)) as [v30 v31] eqn:speq8;
    apply VectorSpec.append_splitat in speq8; rewrite cast_swap in speq8.
    destruct (splitat _ (cast v15 H5)) as [v32 v33] eqn:speq9;
    apply VectorSpec.append_splitat in speq9; rewrite cast_swap in speq9.
    rewrite speq2 in speq, speq4; clear speq2 v5.
    rewrite speq6 in speq4; clear speq6 v7.
    rewrite speq7 in speq; clear speq7 v14.
    rewrite speq8 in speq4; clear speq8 v10.
    rewrite speq9 in speq; clear speq9 v15.
    repeat (rewrite <- cast_app_assoc_2 in speq||rewrite cast_app_left in speq||rewrite cast_app_right in speq);
    repeat rewrite cast_trans in speq.
    rewrite cast_swap, cast_trans in speq.
    rewrite cast_app_r in speq.
    apply app_eq_l in speq.
    repeat (rewrite <- cast_app_assoc_1 in speq||rewrite cast_app_left in speq||rewrite cast_app_right in speq);
    repeat rewrite cast_trans in speq.
    rewrite cast_swap, cast_trans in speq.
    rewrite cast_app_l in speq.
    apply app_eq_r in speq.
    remember (plus_reg_l _ _ _ _) as cool eqn:cool2; clear cool2.
    repeat (rewrite <- cast_app_assoc_2 in speq4||rewrite cast_app_left in speq4||rewrite cast_app_right in speq4);
    repeat rewrite cast_trans in speq4.
    rewrite cast_swap, cast_trans in speq4.
    rewrite cast_app_r in speq4.
    apply app_eq_l in speq4.
    repeat (rewrite <- cast_app_assoc_1 in speq4||rewrite cast_app_left in speq4||rewrite cast_app_right in speq4);
    repeat rewrite cast_trans in speq4.
    rewrite cast_swap, cast_trans in speq4.
    rewrite cast_app_l in speq4.
    apply app_eq_r in speq4.
    remember (plus_reg_l _ _ _ _) as cool2 eqn:cool3; clear cool3.
    rewrite speq4, cast_trans in speq; clear speq4 vA vB vC.
    repeat rewrite cast_app_l in speq.
    apply app_eq_r, app_eq_l in speq.
    symmetry; exact speq.
Qed.

Theorem cast_app_distribute : forall {A n m k l} {eq : n + m = k + l}
  {v : Vector.t A n} {u : Vector.t A m} (eq1 : n = k) (eq2 : m = l),
  cast (v ++ u) eq = cast v eq1 ++ cast u eq2.
Proof.
  intros; destruct eq1, eq2.
  repeat rewrite cast_id.
  reflexivity.
Qed.

Ltac shake_vect_eq speq :=
  repeat (rewrite <- cast_app_assoc_1 in speq||rewrite cast_app_left in speq||rewrite cast_app_right in speq);
  repeat rewrite cast_trans in speq; rewrite cast_swap, cast_trans in speq;
  repeat rewrite cast_app_l in speq;
  repeat (
    match goal with
    | [ speq : ?x ++ ?r = ?y ++ ?s |- _ ]  =>
      assert (x = y) as coolH;[apply app_eq_l in speq; assumption|]; apply app_eq_r in speq;
      destruct coolH
    end);
  repeat (rewrite <- cast_app_assoc_2 in speq||rewrite cast_app_left in speq||rewrite cast_app_right in speq);
  repeat rewrite cast_trans in speq; rewrite cast_swap, cast_trans in speq;
  repeat rewrite cast_app_r in speq;
  repeat (
    match goal with
    | [ speq : ?r ++ ?x = ?s ++ ?y |- _ ]  =>
      assert (x = y) as coolH;[apply app_eq_r in speq; assumption|]; apply app_eq_l in speq;
      destruct coolH
    end).

(*If storing a block in a memory after a different block was
  stored, we can ignore the order of storage. *)
Theorem Block_Store_Store_Swap : forall {B memsz}
    (m : Vector.t B memsz)
    (idx1 idx2 blksz: fin memsz)
    (block block' : Vector.t B (proj1_sig blksz)),
    (*  |----------------|
          |--|      |--|
          1  1+     2  2+   *)
    (((proj1_sig idx1 + proj1_sig blksz) <= proj1_sig idx2 /\
      (proj1_sig idx2 + proj1_sig blksz) < memsz) \/
    (*  |----------------|
          |--|      |--|
          2  2+     1  1+   *)
     ((proj1_sig idx2 + proj1_sig blksz) <= proj1_sig idx1 /\
      (proj1_sig idx1 + proj1_sig blksz) < memsz) \/
    (*  |----------------|
        -|    |--|      |-
         2+   1  1+     2   *)
     ((proj1_sig idx1 + proj1_sig blksz) <= proj1_sig idx2 /\
      (proj1_sig idx2 + proj1_sig blksz) mod memsz <= proj1_sig idx1 /\
      memsz < proj1_sig idx2 + proj1_sig blksz) \/
    (*  |----------------|
        -|    |--|      |-
         1+   2  2+     1   *)
     ((proj1_sig idx2 + proj1_sig blksz) <= proj1_sig idx1 /\
      (proj1_sig idx1 + proj1_sig blksz) mod memsz <= proj1_sig idx2/\
      memsz < proj1_sig idx1 + proj1_sig blksz)) ->
    Block_Store 
      (Block_Store m idx1 blksz block)
      idx2 blksz block'
    = Block_Store 
        (Block_Store m idx2 blksz block')
        idx1 blksz block.
Proof.
  intros B memsz m [idx idxLT] [idx2 idx2LT] 
         [blksz blkszLT] block block' H.
  simpl in H, block.
  unfold Block_Store.
  destruct (Block_Lem idx blksz memsz idxLT blkszLT) as 
    [[tl1 eq1]|[blk21[blk11[idx21[eq11 [eq21 eq31]]]]]];
  destruct (Block_Lem idx2 blksz memsz idx2LT blkszLT) as 
    [[tl2 eq2]|[blk22[blk12[idx22[eq12 [eq22 eq32]]]]]]; try lia.
  - destruct (splitat _ (eq_rect _ _ m _ eq1)) as [v12 v3] eqn:speq;
    apply VectorSpec.append_splitat in speq;
    rewrite <- cast_rew, cast_swap in speq.
    destruct (splitat idx v12) as [v1 v2] eqn:speq2;
    apply VectorSpec.append_splitat in speq2.
    rewrite speq2 in speq; clear speq2 v12.
    unfold eq_rect_r; repeat rewrite <- cast_rew.
    destruct (splitat _ _) as [v12 v3'] eqn:speq2;
    apply VectorSpec.append_splitat in speq2.
    destruct (splitat _ _) as [v1' v2'] eqn:speq3;
    apply VectorSpec.append_splitat in speq3.
    rewrite speq3 in speq2; clear speq3 v12.
    destruct (splitat (_ + _) (cast m _)) as [v4 v5] eqn:speq3;
    apply VectorSpec.append_splitat in speq3.
    destruct (splitat idx2 _) as [v10 v11] eqn:speq8;
    apply VectorSpec.append_splitat in speq8.
    repeat rewrite <- cast_rew; rewrite cast_trans.
    destruct (splitat (_ + _) _) as [v13 v14] eqn:speq9;
    apply VectorSpec.append_splitat in speq9.
    destruct (splitat idx _) as [v6 v7] eqn:speq4;
    apply VectorSpec.append_splitat in speq4.
    repeat rewrite <- cast_rew.
    destruct H as [[H0 H1]|[[H0 H1]|[[H0[H1 H2]]|[H0[H1 H2]]]]]; try lia.
    * (*  idx|---| idx2|---|
        |--------idx2--|blk|-tl2|
        |-idx|blk|----tl1-------| *)
      assert (tl1 = (idx2 - blksz - idx) + blksz + tl2);[lia|].
      destruct (splitat _ (cast v3 H)) as [v8 v9] eqn:speq5;
      apply VectorSpec.append_splitat in speq5.
      destruct (splitat _ v8) as [v15 v16] eqn:speq6;
      apply VectorSpec.append_splitat in speq6.
      rewrite speq6, cast_swap in speq5; clear speq6 v8.
      destruct (splitat _ (cast v14 H)) as [v8' v9'] eqn:speq5';
      apply VectorSpec.append_splitat in speq5'.
      destruct (splitat _ v8') as [v15' v16'] eqn:speq6';
      apply VectorSpec.append_splitat in speq6'.
      assert (idx2 = idx + blksz + (tl1 - blksz - tl2));[lia|].
      destruct (splitat _ (cast v1' H2)) as [v28 v29] eqn:speq25;
      apply VectorSpec.append_splitat in speq25.
      destruct (splitat _ v28) as [v25 v26] eqn:speq26;
      apply VectorSpec.append_splitat in speq26.
      rewrite speq26, cast_swap in speq25; clear speq26 v28.
      destruct (splitat _ (cast v10 H2)) as [v38 v39] eqn:speq35;
      apply VectorSpec.append_splitat in speq35.
      destruct (splitat _ v38) as [v35 v36] eqn:speq36;
      apply VectorSpec.append_splitat in speq36.
      rewrite speq36, cast_swap in speq35; clear speq36 v38.
      rewrite speq6', cast_swap in speq5'; clear speq6' v8'.
      rewrite speq5'; rewrite speq5' in speq9; clear speq5' v14.
      rewrite speq5 in speq, speq2; clear speq5 v3.
      rewrite speq4 in speq9; clear speq4 v13.
      rewrite speq8 in speq3; clear speq8 v4.
      rewrite speq35 in speq9, speq3; clear speq35 v10.
      rewrite speq25; rewrite speq25 in speq2; clear speq25 v1'.
      rewrite cast_swap in speq3; rewrite speq3 in speq; clear speq3 m.
      shake_vect_eq speq.
      remember (Arith.plus_reg_r _ _ _ _) as cool0 eqn:cool1; clear cool1.
      rewrite speq in speq9; clear speq v39.
      shake_vect_eq speq2.
      remember (Arith.plus_reg_r _ _ _ _) as cool1 eqn:cool2; clear cool2.
      rewrite speq2 in speq9; clear speq2 v15.
      shake_vect_eq speq9.
      remember (Arith.plus_reg_r _ _ _ _) as cool2 eqn:cool3; clear cool3 cool0 cool1.
      rewrite speq9; clear speq9 v29.
      vector_simp; f_equal; apply proof_irrelevance.
    * (* idx2|---|  idx|---|
        |---------idx--|blk|-tl1|
        |idx2|blk|----tl2-------| *)
      assert (idx = idx2 + blksz + (tl2 - blksz - tl1));[lia|].
      destruct (splitat _ (cast v1 H)) as [v8 v9] eqn:speq5;
      apply VectorSpec.append_splitat in speq5.
      destruct (splitat _ v8) as [v15 v16] eqn:speq6;
      apply VectorSpec.append_splitat in speq6.
      rewrite speq6, cast_swap in speq5; clear speq6 v8.
      destruct (splitat _ (cast v6 H)) as [v8' v9'] eqn:speq5';
      apply VectorSpec.append_splitat in speq5'.
      destruct (splitat _ v8') as [v15' v16'] eqn:speq6';
      apply VectorSpec.append_splitat in speq6'.
      assert (tl2 = (idx - idx2 - blksz) + blksz + tl1);[lia|].
      destruct (splitat _ (cast v3' H2)) as [v18 v19] eqn:speq15;
      apply VectorSpec.append_splitat in speq15.
      destruct (splitat _ v18) as [v20 v21] eqn:speq16;
      apply VectorSpec.append_splitat in speq16.
      rewrite speq16, cast_swap in speq15; clear speq16 v18.
      destruct (splitat _ (cast v5 H2)) as [v18' v19'] eqn:speq15';
      apply VectorSpec.append_splitat in speq15'.
      destruct (splitat _ v18') as [v25' v26'] eqn:speq16';
      apply VectorSpec.append_splitat in speq16'.
      rewrite speq16', cast_swap in speq15'; clear speq16' v18'.
      rewrite speq6', cast_swap in speq5'; clear speq6' v8'.
      rewrite speq5' in speq4; rewrite speq5'; clear speq5' v6.
      rewrite speq5 in speq2, speq; clear speq5 v1.
      rewrite speq4 in speq9; clear speq4 v13.
      rewrite speq in speq3; clear speq m.
      rewrite speq15' in speq3, speq9; clear speq15' v5.
      rewrite speq15; rewrite speq15 in speq2; clear speq15 v3'.
      rewrite speq8 in speq3; clear speq8 v4.
      shake_vect_eq speq9.
      remember (Arith.plus_reg_r _ _ _ _) as cool0 eqn:cool1; clear cool1.
      rewrite speq9 in speq3; clear speq9 v25'.
      shake_vect_eq speq2.
      remember (Arith.plus_reg_r _ _ _ _) as cool1 eqn:cool2; clear cool2.
      rewrite speq2 in speq3; clear speq2 v9.
      shake_vect_eq speq3.
      remember (Arith.plus_reg_r _ _ _ _) as cool2 eqn:cool3; clear cool3 cool1 cool0.
      rewrite speq3; clear speq3 v20.
      vector_simp; f_equal; apply proof_irrelevance.
  - repeat rewrite <- cast_rew.
    destruct (splitat _ (cast m _)) as [v12 v3] eqn:speq;
    apply VectorSpec.append_splitat in speq.
    rewrite cast_swap in speq.
    destruct (splitat idx _) as [v4 v5] eqn:speq2;
    apply VectorSpec.append_splitat in speq2.
    unfold eq_rect_r; repeat rewrite <- cast_rew; rewrite cast_trans.
    destruct (splitat _ _) as [v8 v9] eqn:speq3;
    apply VectorSpec.append_splitat in speq3.
    destruct (splitat blk22 _) as [block12 block22] eqn:speq4;
    apply VectorSpec.append_splitat in speq4.
    rewrite cast_trans.
    destruct (splitat blk12 _) as [v10 v11] eqn:speq5;
    apply VectorSpec.append_splitat in speq5.
    rewrite <- cast_rew.
    destruct (splitat (_ + _) (cast m _)) as [v13 v14] eqn:speq6;
    apply VectorSpec.append_splitat in speq6.
    destruct (splitat blk22 _) as [v15 v16] eqn:speq7;
    apply VectorSpec.append_splitat in speq7.
    rewrite <- cast_rew, cast_trans.
    destruct (splitat (_ + _) _) as [v17 v18] eqn:speq8;
    apply VectorSpec.append_splitat in speq8.
    destruct (splitat idx _) as [v19 v20] eqn:speq9;
    apply VectorSpec.append_splitat in speq9.
    rewrite <- cast_rew.
    destruct H as [[H0 H1]|[[H0 H1]|[[H0[H1 H2]]|[H0[H1 H2]]]]]; try lia.
    (* ----|  idx|---|  idx2|----
       |---idx---|bks|---tl1----|
       |b22|-----idx22------|b12| *)
    assert (blk22 = (idx2 + blksz) mod memsz);[
    rewrite PeanoNat.Nat.mod_eq; try rewrite Arith.div_bet_1; lia|].
    assert (idx22 = (idx - blk22) + blksz + (tl1 - blk12));[lia|].
    destruct (splitat _ (cast block22 H3)) as [vAB vC] eqn:speq15;
    apply VectorSpec.append_splitat in speq15; rewrite cast_swap in speq15.
    destruct (splitat _ vAB) as [vA vB] eqn:speq16;
    apply VectorSpec.append_splitat in speq16;
    rewrite speq16 in speq15; clear speq16 vAB.
    destruct (splitat _ (cast v16 H3)) as [vXY vZ] eqn:speq16;
    apply VectorSpec.append_splitat in speq16; rewrite cast_swap in speq16.
    destruct (splitat _ vXY) as [vX vY] eqn:speq17;
    apply VectorSpec.append_splitat in speq17;
    rewrite speq17 in speq16; clear speq17 vXY.
    assert (idx = blk22 + (idx22 - (blksz + (tl1 - blk12))));[lia|].
    destruct (splitat _ (cast v4 H4)) as [v1 v2] eqn:speq12;
    apply VectorSpec.append_splitat in speq12; rewrite cast_swap in speq12.
    destruct (splitat _ (cast v19 H4)) as [v31 v32] eqn:speq32;
    apply VectorSpec.append_splitat in speq32; rewrite cast_swap in speq32.
    assert (tl1 = idx22 - ((idx - blk22) + blksz) + blk12);[lia|].
    destruct (splitat _ (cast v18 H5)) as [v6 v7] eqn:speq14;
    apply VectorSpec.append_splitat in speq14; rewrite cast_swap in speq14.
    destruct (splitat _ (cast v3 H5)) as [v36 v37] eqn:speq34;
    apply VectorSpec.append_splitat in speq34; rewrite cast_swap in speq34.
    rewrite speq34 in speq, speq3; clear speq34 v3.
    rewrite speq14; rewrite speq14 in speq8; clear speq14 v18.
    rewrite speq32; rewrite speq32 in speq9; clear speq32 v19.
    rewrite speq in speq6; clear speq m.
    rewrite speq16 in speq8, speq7; clear speq16 v16.
    rewrite speq12 in speq2, speq3; clear speq12 v4.
    rewrite speq15; rewrite speq15 in speq4; clear speq15 block22.
    rewrite speq9 in speq8; clear speq9 v17.
    rewrite speq7 in speq6; clear speq7 v13.
    rewrite speq4 in speq3; clear speq4 v8.
    rewrite speq2 in speq6; clear speq2 v12.
    clear speq5 block'.
    shake_vect_eq speq3;
    remember (Arith.plus_reg_r _ _ _ _) as coolG eqn:fdsaf; clear fdsaf.
    simpl in coolG.
    assert (idx - blk22 + blksz = idx22 - (blksz + (tl1 - blk12)) + blksz);[lia|].
    assert (tl1 - blk12 = idx22 - (idx - blk22 + blksz));[lia|].
    rewrite (cast_app_distribute H6 H7) in speq3.
    assert (idx - blk22 = idx22 - (blksz + (tl1 - blk12)));[lia|].
    rewrite (cast_app_distribute H8 (eq_refl _)) in speq3.
    rewrite cast_id in speq3.
    assert (v36 = cast vC H7);[apply app_eq_r in speq3; assumption|].
    apply app_eq_l in speq3.
    assert (block = vB);[apply app_eq_r in speq3; assumption|].
    apply app_eq_l in speq3.
    rewrite speq3 in speq6; clear speq3 v2.
    rewrite H9 in speq6; clear H9 v36.
    rewrite H10; clear H10 block.
    shake_vect_eq speq8.
    clear coolG; remember (Arith.plus_reg_r _ _ _ _) as coolG eqn:fdsaf; clear fdsaf.
    rewrite (cast_app_distribute (eq_sym H6) (eq_sym H7)) in speq8.
    rewrite (cast_app_distribute (eq_sym H8) (eq_refl _)) in speq8.
    rewrite cast_id in speq8.
    assert (vZ = cast v6 (eq_sym H7));[apply app_eq_r in speq8; assumption|].
    apply app_eq_l in speq8.
    assert (vY = v20);[apply app_eq_r in speq8; assumption|].
    apply app_eq_l in speq8.
    rewrite H10 in speq6; clear H10 vY.
    rewrite H9 in speq6; clear H9 vZ.
    rewrite speq8 in speq6; clear speq8 vX.
    shake_vect_eq speq6.
    clear coolG; remember (Arith.plus_reg_r _ _ _ _) as coolG eqn:fdsaf; clear fdsaf.
    rewrite (cast_app_distribute (eq_sym H6) (eq_sym H7)) in speq6.
    rewrite (cast_app_distribute (eq_sym H8) (eq_refl _)) in speq6.
    rewrite cast_id in speq6.
    assert (vC = cast v6 (eq_sym H7));[apply app_eq_r in speq6; assumption|].
    apply app_eq_l in speq6.
    assert (v5 = v20);[apply app_eq_r in speq6; assumption|].
    apply app_eq_l in speq6.
    rewrite speq6; clear speq6 vA.
    rewrite H9; clear H9 vC.
    destruct H10.
    vector_simp; f_equal; apply proof_irrelevance.
  - repeat rewrite <- cast_rew.
    destruct (splitat _ (cast m _)) as [v12 v3] eqn:speq;
    apply VectorSpec.append_splitat in speq.
    rewrite cast_swap in speq.
    destruct (splitat blk21 _) as [v4 v5] eqn:speq2;
    apply VectorSpec.append_splitat in speq2.
    unfold eq_rect_r; repeat rewrite <- cast_rew; rewrite cast_trans.
    destruct (splitat blk11 _) as [v8 v9] eqn:speq3;
    apply VectorSpec.append_splitat in speq3.
    rewrite <- cast_rew, cast_trans.
    destruct (splitat _ _) as [v6 v7] eqn:speq4;
    apply VectorSpec.append_splitat in speq4.
    destruct (splitat idx2 _) as [v10 v11] eqn:speq5;
    apply VectorSpec.append_splitat in speq5.
    destruct (splitat _ (cast m _)) as [v15 v16] eqn:speq7;
    apply VectorSpec.append_splitat in speq7.
    destruct (splitat idx2 _) as [v25 v26] eqn:speq27;
    apply VectorSpec.append_splitat in speq27.
    repeat rewrite <- cast_rew; rewrite cast_trans.
    destruct (splitat _ _) as [v13 v14] eqn:speq6;
    apply VectorSpec.append_splitat in speq6.
    destruct (splitat blk21 _) as [v23 v24] eqn:speq26;
    apply VectorSpec.append_splitat in speq26.
    repeat rewrite <- cast_rew.
    rewrite speq5 in speq4; clear speq5 v6.
    rewrite speq26 in speq6; clear speq26 v13.
    rewrite speq27 in speq7; clear speq27 v15.
    rewrite speq in speq7; clear speq m.
    rewrite speq2 in speq7; clear speq2 v12.
    destruct H as [[H0 H1]|[[H0 H1]|[[H0[H1 H2]]|[H0[H1 H2]]]]]; try lia.
    (* ----| idx2|---|   idx|----
       |---idx2--|bks|---tl2----|
       |b21|-----idx21------|b11| *)
    assert (blk21 = (idx + blksz) mod memsz);[
    rewrite PeanoNat.Nat.mod_eq; try rewrite Arith.div_bet_1; lia|].
    assert (idx21 = (idx2 - blk21) + blksz + (tl2 - blk11));[lia|].
    destruct (splitat _ (cast v5 H3)) as [vAB vC] eqn:speq2;
    apply VectorSpec.append_splitat in speq2; rewrite cast_swap in speq2.
    destruct (splitat _ vAB) as [vA vB] eqn:speq36;
    apply VectorSpec.append_splitat in speq36;
    rewrite speq36 in speq2; clear speq36 vAB.
    destruct (splitat _ (cast v24 H3)) as [vXY vZ] eqn:speq23;
    apply VectorSpec.append_splitat in speq23; rewrite cast_swap in speq23.
    destruct (splitat _ vXY) as [vX vY] eqn:speq37;
    apply VectorSpec.append_splitat in speq37;
    rewrite speq37 in speq23; clear speq37 vXY.
    assert (tl2 = (idx21 - (idx2 - blk21) - blksz) + blk11);[lia|].
    destruct (splitat _ (cast v7 H4)) as [v20 v21] eqn:speq86;
    apply VectorSpec.append_splitat in speq86; rewrite cast_swap in speq86.
    destruct (splitat _ (cast v16 H4)) as [v32 v33] eqn:speq87;
    apply VectorSpec.append_splitat in speq87; rewrite cast_swap in speq87.
    assert (idx2 = blk21 + (idx21 - blksz - (tl2 - blk11)));[lia|].
    destruct (splitat _ (cast v10 H5)) as [v30 v31] eqn:speq8;
    apply VectorSpec.append_splitat in speq8; rewrite cast_swap in speq8.
    destruct (splitat _ (cast v25 H5)) as [v37 v38] eqn:speq9;
    apply VectorSpec.append_splitat in speq9; rewrite cast_swap in speq9.
    rewrite speq9 in speq6, speq7; clear speq9 v25.
    rewrite speq8; rewrite speq8 in speq4; clear speq8 v10.
    rewrite speq87 in speq6, speq7; clear speq87 v16. 
    rewrite speq23; rewrite speq23 in speq6; clear speq23 v24.
    rewrite speq86; rewrite speq86 in speq4; clear speq86 v7.
    rewrite speq2 in speq4, speq7; clear speq2 v5.
    shake_vect_eq speq4.
    remember (Arith.plus_reg_r _ _ _ _) as coolG eqn:fdsvd; clear fdsvd.
    assert (idx21 - blksz - (tl2 - blk11) + blksz = idx2 - blk21 + blksz);[lia|].
    assert (idx21 - (idx2 - blk21) - blksz = tl2 - blk11);[lia|].
    rewrite (cast_app_distribute H6 H7) in speq4.
    assert (idx21 - blksz - (tl2 - blk11) = idx2 - blk21);[lia|].
    rewrite (cast_app_distribute H8 (eq_refl _)) in speq4.
    rewrite cast_id in speq4.
    assert (vC = cast v20 H7);[apply app_eq_r in speq4; assumption|].
    apply app_eq_l in speq4.
    assert (vB = v11);[apply app_eq_r in speq4; assumption|].
    apply app_eq_l in speq4.
    rewrite speq4 in speq7; clear speq4 vA.
    rewrite H9 in speq7; clear H9 vC.
    destruct H10.
    shake_vect_eq speq6.
    clear coolG; remember (Arith.plus_reg_r _ _ _ _) as coolG eqn:fdsvd; clear fdsvd.
    rewrite (cast_app_distribute (eq_sym H6) (eq_sym H7)) in speq6.
    rewrite (cast_app_distribute (eq_sym H8) (eq_refl _)) in speq6.
    rewrite cast_id in speq6. 
    assert (v32 = cast vZ (eq_sym H7));[apply app_eq_r in speq6; assumption|].
    apply app_eq_l in speq6.
    assert (block' = vY);[apply app_eq_r in speq6; assumption|].
    apply app_eq_l in speq6.
    rewrite speq6 in speq7; clear speq6 v38.
    rewrite H9 in speq7; clear H9 v32.
    rewrite H10; clear H10 block'.
    shake_vect_eq speq7.
    clear coolG; remember (Arith.plus_reg_r _ _ _ _) as coolG eqn:fdsvd; clear fdsvd.
    rewrite (cast_app_distribute (eq_sym H6) (eq_sym H7)) in speq7.
    rewrite (cast_app_distribute (eq_sym H8) (eq_refl _)) in speq7.
    rewrite cast_id in speq7.
    assert (v20 = cast vZ (eq_sym H7));[apply app_eq_r in speq7; assumption|].
    apply app_eq_l in speq7.
    assert (vB = v26);[apply app_eq_r in speq7; assumption|].
    apply app_eq_l in speq7.
    rewrite speq7; clear speq7 v31.
    rewrite H9; clear H9 v20.
    clear H10 vB.
    vector_simp; f_equal; apply proof_irrelevance.
Qed.

Theorem const_cons_snoc: forall {B} {b : B} {n},
  b :: const b n = cast  (const b n ++ [b]) (add_comm n 1).
Proof.
  intros.
  induction n;[reflexivity|].
  simpl.
  replace (cast _ _)
     with (cast (const b n ++ [b]) (add_comm n 1)).
  - rewrite <- IHn; reflexivity.
  - f_equal; apply proof_irrelevance.
Qed.

Theorem rev_const: forall {B} {b : B} {n},
  Vector.rev (const b n) = const b n.
Proof.
  intros.
  induction n.
  - simpl; apply vector_rev_nil_nil.
  - simpl.
    rewrite rev_snoc.
    rewrite IHn.
    rewrite const_cons_snoc; reflexivity.
Qed.

Theorem const_split: forall {B} {b : B} {n m},
  const b (n + m) = const b n ++ const b m.
Proof.
  intros.
  induction n; intros; [reflexivity|].
  simpl.
  rewrite IHn; reflexivity.
Qed.

Theorem const_cast_split: forall {B} {b : B} {n k m}
  (eq : k = n + m),
  cast (const b k) eq = const b n ++ const b m.
Proof.
  intros.
  rewrite eq0, cast_id.
  apply const_split.
Qed.

Theorem Block_Load_const : forall {B memsz}
    (idx blksz: fin memsz)
    (val : B),
    Block_Load (const val _) idx blksz
    = (const val _).
Proof.
  intros B memsz [idx idxLT] [blksz blkszLT] val.
  unfold proj1_sig.
  unfold Block_Load.
  destruct (Block_Lem idx blksz memsz idxLT blkszLT) as 
    [[tl eq]|[blk2[blk1[idx2[eq1 [eq2 eq3]]]]]].
  - rewrite <- cast_rew.
    rewrite (const_cast_split eq), const_split, vector_append_inv2, vector_append_inv2.
    reflexivity.
  - rewrite <- cast_rew.
    rewrite (const_cast_split eq3), const_split, vector_append_inv2, vector_append_inv2.
    unfold eq_rect_r; rewrite <- cast_rew.
    rewrite cast_trans, cast_swap.
    rewrite (const_cast_split _).
    reflexivity.
Qed.

(* This file contains the implementation and formal verification of 
   a TinyRAM implementation of the Fibonacci function. *)

(* As a preamble, we first define an obviously correct implementation
   to be used as a specification. *)

Fixpoint fib (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n =>
    match n with
    | 0 => 1
    | S n' => fib n' + fib n
    end
  end.

(* Our implementation is going to use modular arithmetic since
   the output comes in the form of a fixed-length bitvector.

   We also generalize the base arguments to aid in reasoining about
   the main loop later.

   We relate fib to its moded version.
*)

Fixpoint mfib (i j m n : nat) : nat :=
  match n with
  | 0 => i
  | S n =>
    match n with
    | 0 => j
    | S n' => (mfib i j m n' + mfib i j m n) mod m
    end
  end.

Theorem mfib_mod : forall m n, 1 < m ->
  mfib 0 1 m n = fib n mod m.
Proof.
  intros m n lt.
  assert ( (mfib 0 1 m n, mfib 0 1 m (S n))
         = (fib n mod m, fib (S n) mod m) ).
  { induction n.
    - simpl.
      rewrite mod_0_l, mod_small; try lia; reflexivity.
    - change (mfib 0 1 m (S (S n))) 
        with ((mfib 0 1 m n + mfib 0 1 m (S n)) mod m).
      change (fib (S (S n))) 
        with (fib n + fib (S n)).
      f_equal.
      + injection IHn; auto.
      + rewrite (add_mod (fib n)); [|lia].
        injection IHn; auto. }
  rewrite pair_equal_spec in H; destruct H.
  assumption.
Qed.

Theorem mfib_upper_bound: forall i j m n, 
  i < m -> j < m -> m <> 0 ->
  mfib i j m n < m.
Proof.
  intros i j m n.
  destruct n.
  - unfold mfib; auto.
  - destruct n; unfold mfib; fold mfib.
    + auto.
    + intros; apply mod_upper_bound; auto.
Qed.

Theorem mfib_rebase: forall i j m n, 
  mfib i j m (S n) = mfib (mfib i j m 1) (mfib i j m 2) m n.
Proof.
  intros i j m n.
  assert ( (mfib i j m (S n), mfib i j m (S (S n)))
         = (mfib (mfib i j m 1) (mfib i j m 2) m n
           ,mfib (mfib i j m 1) (mfib i j m 2) m (S n))).
  { induction n.
    - reflexivity.
    - change (mfib i j m (S (S (S n))))
        with ((mfib i j m (S n) + mfib i j m (S (S n))) mod m).
      rewrite pair_equal_spec in IHn; destruct IHn.
      rewrite H, H0; clear H H0.
      reflexivity. }
  rewrite pair_equal_spec in H; destruct H.
  assumption.
Qed.

(* An accumulator-passing style implementation of the same function.
   This is closer in spirit to the assembly code, making it a better
   target for comparison. *)
Fixpoint fib_acc' (n : nat) : nat * nat :=
  match n with
  | 0 => (0, 1)
  | S n => 
    match fib_acc' n with
    | (a, b) => (b, a + b)
    end
  end.

Definition fib_acc n := fst (fib_acc' n).

(* A proof that both are the same function. *)
Theorem fib_acc_eq' : forall n, (fib n, fib (S n)) = fib_acc' n.
Proof.
  intros n; induction n; [ reflexivity | ].
  unfold fib_acc'; fold fib_acc'.
  destruct (fib_acc' n).
  change (fib (S (S n))) with (fib n + fib (S n)).
  injection IHn; auto.
Qed.

Theorem fib_acc_eq : forall n, fib n = fib_acc n.
Proof. intro; unfold fib_acc; rewrite <- fib_acc_eq'; reflexivity. Qed.

(* Example archetecture with 4 registers and a wordsize of 16 bits. *)
Module SixteenFour <: TinyRAMParameters.
  Definition wordSizeEighth : nat := 2.
  Definition registerCount : nat := 4.
  Definition wordSize := wordSizeEighth * 8.
  Definition wordSizeLength : nat := 4.
  Theorem wordSizePow2 : wordSize = 2 ^ wordSizeLength.
  Proof. unfold wordSize. simpl. reflexivity. Qed.
  Theorem encodingAxiom : 6 + 2 * log2_up registerCount <= wordSize.
  Proof. unfold registerCount. unfold wordSize. simpl. lia. Qed.
End SixteenFour.

Module TR := TinyRAMInstThm SixteenFour.
Import TR.

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
  Memory_Word_Load_from_Reg (const val _) idx
  = vector_concat (const val _).
Proof.
  intros.
  unfold Memory_Word_Load_from_Reg, Memory_Word_Load, Memory_Block_Load.
  rewrite Block_Load_const.
  rewrite rev_const; reflexivity.
Qed.

Theorem registers_pureOp_cjmp : forall v m,
  registers (pureOp_cjmp v m) = registers m.
Proof. intros; destruct m; reflexivity. Qed.

Theorem registers_pureOp_cmpe : forall v1 v2 m,
  registers (pureOp_cmpe v1 v2 m) = registers m.
Proof. intros; destruct m; reflexivity. Qed.

Theorem memory_pureOp_cjmp : forall v m,
  memory (pureOp_cjmp v m) = memory m.
Proof. intros; destruct m; reflexivity. Qed.

Theorem memory_pureOp_cmpe : forall v1 v2 m,
  memory (pureOp_cmpe v1 v2 m) = memory m.
Proof. intros; destruct m; reflexivity. Qed.

(* We can create the actual assembly program now. 
   
   The program begins by doing the folloing;
     the input, n, is read from the main tape into register 00.
     the address blocks starting at 0 and 2 are set to 0 and 1.

   Over the course of the program, fib n will be stored at block
   0 and fib (S n) will be stored at block 2.

   During each loop, block 0 is set to the value of block 2 and
   block 2 is set to the value of block 0 plus block 2.

   during this procedure, the value of block 0 (e.g. fib n) will
   be stored in register 10 while block 2 (e.g. fib (S n)) will
   be stored in register 01.

   Each loop begins by seeing if [00] is 0.
   If it is, halt and give [10] as output.
   If it is not, then continue through the loop.
   At the end of the loop [00] is decremented before the PC is
   reset to the begining of the loop.
*)

(*The actual assembly program.*)
Definition FibProgram : Program.
  apply (List.map InstructionEncode).

  (* This works by manipulating the values at addresses 0 and 2 *)
  (* n is sored in register 00, and is decremented every loop until 0 *)

  (* Initialization *)
  (* Store 1 into address 0010 *)
    (*0: Store 1 into register 00 *)
  apply (cons (movI (bitvector_fin_big [b0; b0]), inl (nat_bitvector_big _ 1))).
    (*1: Store [00] at address 2 *)
  apply (cons (store_wI (bitvector_fin_big [b0; b0]), inl (nat_bitvector_big _ wordSizeEighth))).

  (*2: Read input from main tape into register 00. *)
  apply (cons (readI (bitvector_fin_big [b0; b0]), inl (nat_bitvector_big _ 0))).

  (* Main Loop *)
  (*3: Check if 00 is 0*)
  apply (cons (cmpeI (bitvector_fin_big [b0; b0]), inl (nat_bitvector_big _ 0))).

  (*4: If flag is set, jump.*)
  apply (cons (cjmpI, inl (nat_bitvector_big _ 12))).

  (* Read two addresses into registers *)
  (*5: read address 0 into 01 *)
  apply (cons (load_wI (bitvector_fin_big [b0; b1]), inl (nat_bitvector_big _ 0))).
  (*6: read address 2 into 10  *)
  apply (cons (load_wI (bitvector_fin_big [b1; b0]), inl (nat_bitvector_big _ wordSizeEighth))).

  (*7: add two registers together; [01] := [01] + [10] *)
  apply (cons (addI (bitvector_fin_big [b0; b1]) (bitvector_fin_big [b0; b1]),
                    (inr (bitvector_fin_big [b1; b0])))).

  (* Store both registers *)
  (*8: store [10] into adress 0 *)
  apply (cons (store_wI (bitvector_fin_big [b1; b0]), inl (nat_bitvector_big _ 0))).
  (*9: store [01] into adress 2 *)
  apply (cons (store_wI (bitvector_fin_big [b0; b1]), inl (nat_bitvector_big _ wordSizeEighth))).

  (*10: decriment [00] *)
  apply (cons (subI (bitvector_fin_big [b0; b0]) (bitvector_fin_big [b0; b0]),
                    (inl (nat_bitvector_big _ 1)))).

  (*11: jump back to 0 check. *)
  apply (cons (jmpI, inl (nat_bitvector_big _ 3))).

  (*12: Return *)
  apply (cons (answerI, inr (bitvector_fin_big [b1; b0]))).

  apply nil.
Defined.

(* The program proper is the following. *)
Definition fib_asm (n : nat) : itree void1 Word :=
  interp_program FibProgram (nat_bitvector_big _ n :: nil)%list nil.

(* However, reasoning about this directly is not practical. Instead,
   we divierge a bit to describe some functions which perform the
   same state manipulations. This will factor out the itrees giving
   making things simpler.
*)

(*Firstly, we want to describe the sequence of pure state manipulations.*)
(*initialize 1 into address 2 and read tape into reg 0.*)
Definition fib_init (m : MachineState) : MachineState :=
  (pureOp_read (bitvector_fin_big [b0; b0]) (nat_bitvector_big _ 0) 
  (pureOp_store_w (bitvector_fin_big [b0; b0]) (nat_bitvector_big _ 2) 
  (pureOp_mov (bitvector_fin_big [b0; b0]) (nat_bitvector_big _ 1)
  m))).

(*The recursive step of the fib function*)
Definition fib_step (m : MachineState) : MachineState :=
  let m0 := 
      (pureOp_load_w (bitvector_fin_big [b1; b0]) (nat_bitvector_big _ 2)
      (pureOp_load_w (bitvector_fin_big [b0; b1]) (nat_bitvector_big _ 0)
      (pureOp_cjmp (nat_bitvector_big _ 12)
      (pureOp_cmpe (bitvector_fin_big [b0; b0]) (nat_bitvector_big _ 0)
      m)))) in
    (pureOp_jmp (nat_bitvector_big _ 3)
    (pureOp_sub (bitvector_fin_big [b0; b0]) (bitvector_fin_big [b0; b0])
                (nat_bitvector_big _ 1)
    (pureOp_store_w (bitvector_fin_big [b0; b1]) (nat_bitvector_big _ 2) 
    (pureOp_store_w (bitvector_fin_big [b1; b0]) (nat_bitvector_big _ 0) 
    (pureOp_add (bitvector_fin_big [b0; b1]) (bitvector_fin_big [b0; b1])
                (nth (registers m0) (bitvector_fin_big [b1; b0]))
    m0))))).

Definition fib_finish (m : MachineState) : MachineState :=
  (pureOp_cjmp (nat_bitvector_big _ 12)
  (pureOp_cmpe (bitvector_fin_big [b0; b0]) (nat_bitvector_big _ 0)
  m)).

Fixpoint fib_step_r (n : nat) (m : MachineState) : MachineState :=
  match n with
  | 0 => m
  | S n => fib_step_r n (fib_step m)
  end.

Definition fib_full (m : MachineState) : MachineState :=
  let m0 := fib_init m in
  let m1 := fib_step_r (bitvector_nat_big (nth (registers m0) (bitvector_fin_big [b0; b0]))) m0 in
  fib_finish m1.

(* We can verify that these functions do, in fact, do the same thing 
   as out program. *)

(* Note: the strategies used here are essentially automatic. They 
   can definitely be turned into tactics, but that's for the future. *)

Lemma program_fib_init : 
  forall m, (program (fib_init m)) = program m.
Proof. destruct m; reflexivity. Qed.

Lemma program_fib_step : 
  forall m, (program (fib_step m)) = program m.
Proof. destruct m; reflexivity. Qed.

Lemma program_fib_step_r : 
  forall n m, (program (fib_step_r n m)) = program m.
Proof. 
  induction n; destruct m; [ reflexivity | ].
  unfold fib_step_r; fold fib_step_r.
  rewrite IHn, program_fib_step.
  reflexivity.
Qed.

Lemma program_fib_finish : 
  forall m, (program (fib_finish m)) = program m.
Proof. destruct m; reflexivity. Qed.

Lemma program_fib_full : 
  forall m, (program (fib_full m)) = program m.
Proof. 
  intro.
  unfold fib_full. 
  rewrite program_fib_finish, program_fib_step_r, program_fib_init.
  reflexivity.
Qed.

Lemma programCounter_fib_init : 
  forall m, 
  (programCounter m) = (nat_bitvector_big _ 0) ->
  (programCounter (fib_init m)) = 
  (nat_bitvector_big _ 3).
Proof.
  destruct m; intro H; unfold programCounter in H; rewrite H; reflexivity.
Qed.

Lemma programCounter_fib_step : 
  forall m, (programCounter (fib_step m)) = 
  (nat_bitvector_big _ 3).
Proof. destruct m; reflexivity. Qed.

Lemma fib_step_r_unfold_out : forall n m,
  fib_step_r (S n) m = fib_step (fib_step_r n m).
Proof. 
  induction n;[destruct m;reflexivity|intro].
  unfold fib_step_r at 2; fold fib_step_r.
  change (fib_step_r (S (S n)) m)
     with (fib_step_r (S n) (fib_step m)).
  rewrite IHn.
  reflexivity.
Qed.

Lemma programCounter_fib_step_r : 
  forall m n, (programCounter (fib_step_r (S n) m)) = 
  (nat_bitvector_big _ 3).
Proof.
  intros.
  rewrite fib_step_r_unfold_out, programCounter_fib_step.
  reflexivity.
Qed.

Lemma programCounter_fib_finish : forall m,
  nth (registers m) (bitvector_fin_big [b0; b0])
  = (nat_bitvector_big wordSize 0) ->
  (programCounter (fib_finish m)) = 
  (nat_bitvector_big _ 12).
Proof.
  intros m H.
  destruct m.
  unfold fib_finish, pureOp_cmpe, pureOp_cjmp.
  unfold registers in H; rewrite H.
  reflexivity.
Qed.

(* fib_step decrements register 00 *)
Lemma fib_step_index_dec : forall m,
  nth (registers (fib_step m)) (bitvector_fin_big [b0; b0])
  = Vector.tl (bv_sub (nth (registers m) (bitvector_fin_big [b0; b0]))
                      (nat_bitvector_big _ 1)).
Proof.
  destruct m.
  unfold fib_step.
  unfold registers.
  unfold pureOp_cmpe, pureOp_cjmp, pureOp_load_w.
  unfold pureOp_add, pureOp_store_w, pureOp_sub, pureOp_jmp.
  repeat (rewrite replace_swap; [ | simpl; lia ];
          rewrite replace_nth_irr; [ | simpl; lia ]).
  rewrite nth_replace.
  reflexivity.
Qed.

(*fib_step_r will always make register 00 0. 
  (precondition for assembly always halting)*)
Lemma fib_step_r_halt_lem : 
  forall n m,
  n < 2 ^ wordSize ->
  nth (registers m) (bitvector_fin_big [b0; b0]) = (nat_bitvector_big _ n) ->
  nth (registers (fib_step_r n m)) (bitvector_fin_big [b0; b0]) 
  = (nat_bitvector_big _ 0).
Proof.
  induction n; destruct m; intros lt Eq; unfold registers in Eq.
  - unfold fib_step_r, fib_finish, pureOp_cmpe, pureOp_cjmp, programCounter.
    assumption.
  - unfold fib_step_r; fold fib_step_r.
    assert (n < 2 ^ wordSize); [lia|].
    rewrite (IHn _ H); [ reflexivity | ].
    rewrite fib_step_index_dec.
    unfold registers.
    rewrite Eq.
    rewrite bv_sub_correct_pos; try lia.
    f_equal; lia.
Qed.

(* The assembly produced by FibProgram starts with fib_init *)
Lemma fib_runs_init : forall n, 
  (interp_machine (E := void1) run
     (initialState FibProgram
        (nat_bitvector_big wordSize n :: nil)%list nil))
  ≈ (interp_machine (E := void1) run
      (fib_init (initialState FibProgram
        (nat_bitvector_big wordSize n :: nil)%list nil))).
Proof.
  intro n.
  unfold initialState.
  rewrite interp_machine_run_step;
  [|reflexivity|apply encode_decode_id|intro HAH; discriminate HAH].
  rewrite pureOp_mov_interp_imm; unfold pureOp_mov.
  rewrite interp_machine_run_step;
  [|change (bitvector_nat_big _) with 1;reflexivity|apply encode_decode_id|intro HAH; discriminate HAH].
  rewrite pureOp_store_w_interp_imm; unfold pureOp_store_w.
  rewrite interp_machine_run_step;
  [|change (bitvector_nat_big _) with 2;reflexivity|apply encode_decode_id|intro HAH; discriminate HAH].
  rewrite pureOp_read_interp_imm.
  reflexivity.
Qed.

(* After initialization, the assembly produced by FibProgram's main
   loop corresponds to fib_step *)
Lemma fib_runs_step : forall n m,
  S n < 2 ^ wordSize ->
  programCounter m = nat_bitvector_big _ 3 ->
  nth (registers m) (bitvector_fin_big [b0; b0]) = nat_bitvector_big _ (S n) ->
  program m = FibProgram ->
  interp_machine (E := void1) run m
  ≈ interp_machine (E := void1) run (fib_step m).
Proof.
  intros n m lt eq1 eq2 eq3; destruct m.
  unfold registers in eq2.
  unfold programCounter in eq1; rewrite eq1.
  unfold program in eq3; rewrite eq3.
  unfold fib_step.
  rewrite interp_machine_run_step;
  [|change (bitvector_nat_big _) with 3;reflexivity|apply encode_decode_id|intro HAH; discriminate HAH].
  rewrite pureOp_cmpe_interp_imm; unfold pureOp_cmpe.
  replace (bv_eq _ _) with b0; [|
  rewrite eq2, bv_eq_big_conv; [reflexivity|assumption|apply Arith.zero2pow]].
  rewrite interp_machine_run_step;
  [|change (bitvector_nat_big _) with 4;reflexivity|apply encode_decode_id|intro HAH; discriminate HAH].
  rewrite pureOp_cjmp_interp_imm; unfold pureOp_cjmp.
  change (if b0 then _ else ?y) with y.
  rewrite interp_machine_run_step;
  [|change (bitvector_nat_big _) with 5;reflexivity|apply encode_decode_id|intro HAH; discriminate HAH].
  rewrite pureOp_load_w_interp_imm; unfold pureOp_load_w.
  unfold registers.
  rewrite interp_machine_run_step;
  [|change (bitvector_nat_big _) with 6;reflexivity|apply encode_decode_id|intro HAH; discriminate HAH].
  rewrite pureOp_load_w_interp_imm; unfold pureOp_load_w.
  rewrite interp_machine_run_step;
  [|change (bitvector_nat_big _) with 7;reflexivity|apply encode_decode_id|intro HAH; discriminate HAH].
  rewrite pureOp_add_interp_reg; unfold pureOp_add.
  unfold registers.
  rewrite interp_machine_run_step;
  [|change (bitvector_nat_big _) with 8;reflexivity|apply encode_decode_id|intro HAH; discriminate HAH].
  rewrite pureOp_store_w_interp_imm.
  rewrite interp_machine_run_step;
  [|change (bitvector_nat_big _) with 9;reflexivity|apply encode_decode_id|intro HAH; discriminate HAH].
  rewrite pureOp_store_w_interp_imm; unfold pureOp_store_w.
  rewrite interp_machine_run_step;
  [|change (bitvector_nat_big _) with 10;reflexivity|apply encode_decode_id|intro HAH; discriminate HAH].
  rewrite pureOp_sub_interp_imm; unfold pureOp_sub.
  rewrite interp_machine_run_step;
  [|change (bitvector_nat_big _) with 11;reflexivity|apply encode_decode_id|intro HAH; discriminate HAH].
  rewrite pureOp_jmp_interp_imm; unfold pureOp_jmp.
  reflexivity.
Qed.

Lemma fib_runs_step_r : forall n m,
  n < 2 ^ wordSize ->
  programCounter m = nat_bitvector_big _ 3 ->
  nth (registers m) (bitvector_fin_big [b0; b0]) = nat_bitvector_big _ n ->
  program m = FibProgram ->
  interp_machine (E := void1) run m
  ≈ interp_machine (E := void1) run (fib_step_r n m).
Proof.
  induction n; destruct m; intros;
  unfold programCounter in H0;
  unfold registers in H1;
  unfold program in H2;
  rewrite H0, H2;
  unfold fib_step_r;[reflexivity|].
  fold fib_step_r.
  rewrite fib_runs_step; [|exact H|reflexivity|exact H1|reflexivity].
  rewrite IHn; try reflexivity; [lia|].
  rewrite fib_step_index_dec; unfold registers.
  rewrite H1.
  rewrite bv_sub_correct_pos;[f_equal;lia|assumption|
  exact pureOp_read_correct_lem|lia].
Qed.

Lemma fib_runs_finish : forall m,
  programCounter m = nat_bitvector_big _ 3 ->
  nth (registers m) (bitvector_fin_big [b0; b0]) = nat_bitvector_big _ 0 ->
  program m = FibProgram ->
  interp_machine (E := void1) run m
  ≈ interp_machine (E := void1) run (fib_finish m).
Proof.
  destruct m; unfold programCounter, registers, program; intros.
  unfold fib_finish.
  rewrite H, H1; clear H H1.
  rewrite interp_machine_run_step;
  [|change (bitvector_nat_big _) with 3;reflexivity|apply encode_decode_id|intro HAH; discriminate HAH].
  rewrite pureOp_cmpe_interp_imm; unfold pureOp_cmpe.
  rewrite H0; change (bv_eq _ _) with b1.
  rewrite interp_machine_run_step;
  [|change (bitvector_nat_big _) with 4;reflexivity|apply encode_decode_id|intro HAH; discriminate HAH].
  rewrite pureOp_cjmp_interp_imm.
  reflexivity.
Qed.

(* The state manipulations produced by FibProgram is the same as that
   produced by fib_full. *)
Lemma fib_runs_full : forall n, 
  n < 2 ^ wordSize ->
  (interp_machine (E := void1) run (initialState FibProgram
        (nat_bitvector_big wordSize n :: nil)%list nil))
  ≈ (interp_machine (E := void1) run (fib_full (initialState FibProgram
        (nat_bitvector_big wordSize n :: nil)%list nil))).
Proof.
  intros n lt.
  rewrite fib_runs_init, fib_runs_step_r, fib_runs_finish;
  unfold fib_full;
  unfold initialState, fib_init, pureOp_mov, pureOp_store_w, pureOp_read.    
  - reflexivity.
  - unfold registers.
    rewrite nat_bitvector_big_inv;[|apply Arith.zero2pow ].
    rewrite nth_replace.
    rewrite nat_bitvector_big_inv;[|assumption].
    destruct n;[reflexivity|].
    apply programCounter_fib_step_r.
  - unfold registers at 2.
    rewrite nat_bitvector_big_inv;[|apply Arith.zero2pow ].
    rewrite nth_replace.
    rewrite nat_bitvector_big_inv;[|assumption].
    apply fib_step_r_halt_lem;[assumption|].
    unfold registers.
    apply nth_replace.
  - rewrite program_fib_step_r; reflexivity.
  - unfold registers.
    rewrite nth_replace.
    rewrite nat_bitvector_big_inv;[|apply Arith.zero2pow ].
    rewrite nat_bitvector_big_inv;assumption.
  - unfold programCounter; reflexivity.
  - unfold registers.
    rewrite nth_replace. 
    rewrite nat_bitvector_big_inv;[|apply Arith.zero2pow ].
    rewrite nat_bitvector_big_inv;[reflexivity|assumption ].
  - reflexivity.
Qed.

(* After running fib_full, the PC is at an answer instruction. *)
Lemma fib_full_answer : forall n, n < 2 ^ wordSize ->
  (List.nth_error (program (fib_full (initialState FibProgram
                                     (nat_bitvector_big wordSize n :: nil)%list nil)))
                  (bitvector_nat_big (programCounter (fib_full (initialState FibProgram
                                     (nat_bitvector_big wordSize n :: nil)%list nil)))))
  = Some (InstructionEncode (answerI, inr (bitvector_fin_big [b1; b0]))).
Proof.
  intros n nlt.
  remember (fib_full _) as intr.
  unfold initialState, fib_full, fib_init, pureOp_mov, pureOp_store_w, pureOp_read, registers in Heqintr.
  rewrite nat_bitvector_big_inv, nth_replace, nat_bitvector_big_inv in Heqintr;
  [ | assumption | apply Arith.zero2pow ].
  rewrite nth_replace, replace_replace in Heqintr.
  change (bv_incr _ _) with (nat_bitvector_big wordSize 3) in Heqintr.
  rewrite Heqintr; clear Heqintr intr.
  rewrite program_fib_finish, program_fib_step_r.
  unfold program.
  rewrite programCounter_fib_finish;[reflexivity|].
  rewrite fib_step_r_halt_lem;[reflexivity|assumption|].
  unfold registers.
  rewrite nth_replace.
  reflexivity.
Qed.

(* the word at 0 contains the first intiial value of the mfib function. *)
Lemma fib_init_vals_1 : forall m,
  Memory_Word_Load_from_Reg 
    (memory (fib_init m))
    (nat_bitvector_big _ 0)
  = Memory_Word_Load_from_Reg 
    (memory m)
    (nat_bitvector_big _ 0).
Proof.
  assert (4 < 2 ^ wordSize);[
    rewrite pureOp_store_b_lem;
    rewrite add_comm;
    change (2 ^ (8 + (wordSize - 8)))
      with (2 * (2 * (2 * 2 ^ (5 + (wordSize - 8)))));
    assert (0 < 2 ^ (5 + (wordSize - 8)));[apply Arith.zero2pow|lia]|].
  intro m; destruct m.
  unfold fib_init, pureOp_mov, pureOp_store_w, pureOp_read, memory.
  rewrite nth_replace.
  rewrite Memory_Word_Store_Load_from_Reg_Irr;[|
    change wordSizeEighth with 2;
    repeat rewrite nat_bitvector_big_inv;[lia|apply Arith.zero2pow|lia]].
  reflexivity.
Qed.

(* the word at 2 contains the second intiial value of the mfib function. *)
Lemma fib_init_vals_2_gen : forall m, 
  Memory_Word_Load_from_Reg 
    (memory (fib_init m))
    (nat_bitvector_big _ 2)
  = nat_bitvector_big _ 1.
Proof.
  intro m; destruct m.
  unfold initialState, fib_init, pureOp_mov, pureOp_store_w, pureOp_read, memory.
  rewrite nth_replace.
  rewrite Memory_Word_Store_Load_from_Reg. 
  reflexivity.
Qed.

(*fib_step computes subsequent fib values.*)
Lemma fib_step_vals_1 : forall i j m n,
  Memory_Word_Load_from_Reg (memory m) (nat_bitvector_big _ 2)
    = nat_bitvector_big _ (mfib i j (2 ^ wordSize) (S n)) -> 
  Memory_Word_Load_from_Reg (memory (fib_step m)) (nat_bitvector_big _ 0)
    = nat_bitvector_big _ (mfib i j (2 ^ wordSize) (S n)).
Proof.
  assert (4 < 2 ^ wordSize);[
    rewrite pureOp_store_b_lem;
    rewrite add_comm;
    change (2 ^ (8 + (wordSize - 8)))
      with (2 * (2 * (2 * 2 ^ (5 + (wordSize - 8)))));
    assert (0 < 2 ^ (5 + (wordSize - 8)));[apply Arith.zero2pow|lia]|].
  intros i j m n.
  destruct m; unfold memory.
  intros.
  unfold fib_step.
  unfold pureOp_cmpe, pureOp_cjmp, pureOp_load_w.
  unfold pureOp_add, pureOp_store_w, pureOp_sub, pureOp_jmp.
  unfold registers.
  rewrite H0; clear H0.
  repeat rewrite (replace_swap _ (bitvector_fin_big [b0; b1]) (bitvector_fin_big [b1; b0])).
  repeat rewrite (replace_nth_irr _ (bitvector_fin_big [b0; b1]) (bitvector_fin_big [b1; b0])).
  repeat rewrite (replace_swap _ (bitvector_fin_big [b1; b0]) (bitvector_fin_big [b0; b1])).
  repeat rewrite (replace_nth_irr _ (bitvector_fin_big [b1; b0]) (bitvector_fin_big [b0; b1])).
  repeat rewrite replace_replace.
  repeat rewrite nth_replace.
  rewrite Memory_Word_Store_Load_from_Reg_Irr.
  rewrite Memory_Word_Store_Load_from_Reg.
  reflexivity.
  repeat rewrite nat_bitvector_big_inv; change wordSizeEighth with 2; lia.
  all: simpl; lia.
Qed.

(*fib_step computes subsequent fib values.*)
Lemma fib_step_vals_2 : forall i j m n,
  i < 2 ^ wordSize -> j < 2 ^ wordSize ->
  Memory_Word_Load_from_Reg (memory m) (nat_bitvector_big _ 0)
    = nat_bitvector_big _ (mfib i j (2 ^ wordSize) n) -> 
  Memory_Word_Load_from_Reg (memory m) (nat_bitvector_big _ 2)
    = nat_bitvector_big _ (mfib i j (2 ^ wordSize) (S n)) -> 
  Memory_Word_Load_from_Reg (memory (fib_step m)) (nat_bitvector_big _ 2)
    = nat_bitvector_big _ (mfib i j (2 ^ wordSize) (S (S n))).
Proof.
  assert (4 < 2 ^ wordSize);[
    rewrite pureOp_store_b_lem;
    rewrite add_comm;
    change (2 ^ (8 + (wordSize - 8)))
      with (2 * (2 * (2 * 2 ^ (5 + (wordSize - 8)))));
    assert (0 < 2 ^ (5 + (wordSize - 8)));[apply Arith.zero2pow|lia]|].
  intros i j m n iLT jLT.
  destruct m; unfold memory.
  intros.
  unfold fib_step.
  unfold pureOp_cmpe, pureOp_cjmp, pureOp_load_w.
  unfold pureOp_add, pureOp_store_w, pureOp_sub, pureOp_jmp.
  unfold registers.
  rewrite H0, H1; clear H0 H1.
  repeat rewrite (replace_swap _ (bitvector_fin_big [b0; b1]) (bitvector_fin_big [b1; b0])).
  repeat rewrite (replace_nth_irr _ (bitvector_fin_big [b0; b1]) (bitvector_fin_big [b1; b0])).
  repeat rewrite (replace_swap _ (bitvector_fin_big [b1; b0]) (bitvector_fin_big [b0; b1])).
  repeat rewrite (replace_nth_irr _ (bitvector_fin_big [b1; b0]) (bitvector_fin_big [b0; b1])).
  repeat rewrite nth_replace.
  rewrite Memory_Word_Store_Store_from_Reg_Swap.
  rewrite Memory_Word_Store_Load_from_Reg_Irr.
  rewrite Memory_Word_Store_Load_from_Reg.
  rewrite <- bv_add_correct_mod_2.
  reflexivity.
  apply mfib_upper_bound;[assumption|assumption|apply pow_nonzero;lia].
  apply mfib_upper_bound;[assumption|assumption|apply pow_nonzero;lia].
  repeat rewrite nat_bitvector_big_inv; change wordSizeEighth with 2; lia.
  repeat rewrite nat_bitvector_big_inv; change wordSizeEighth with 2; lia.
  all: simpl; lia.
Qed.

Lemma fib_step_r_vals : forall n m,
  n < 2 ^ wordSize ->
  nth (registers m) (bitvector_fin_big [b0;b0]) 
    = (nat_bitvector_big _ n) ->
  Memory_Word_Load_from_Reg (memory (fib_step_r n m)) (nat_bitvector_big _ 0)
  = nat_bitvector_big _ 
      (mfib (bitvector_nat_big (Memory_Word_Load_from_Reg (memory m) (nat_bitvector_big _ 0)))
            (bitvector_nat_big (Memory_Word_Load_from_Reg (memory m) (nat_bitvector_big _ 2)))
            (2 ^ wordSize) n).
Proof.
  induction n; intros; destruct m; unfold registers in H0.
  - unfold fib_step_r.
    unfold memory.
    unfold mfib.
    repeat rewrite bitvector_nat_big_inv.
    reflexivity.
  - unfold fib_step_r; fold fib_step_r.
    rewrite IHn; clear IHn.
    + repeat unfold memory at 3.
      rewrite mfib_rebase.
      f_equal; f_equal.
      --  rewrite (fib_step_vals_1 (bitvector_nat_big
                    (Memory_Word_Load_from_Reg memory0
                        (nat_bitvector_big wordSize 0))) (bitvector_nat_big
                    (Memory_Word_Load_from_Reg memory0
                        (nat_bitvector_big wordSize 2))) _ 0).
          rewrite nat_bitvector_big_inv;[reflexivity|].
          apply mfib_upper_bound.
          all: try apply bitvector_nat_big_lt_2pow.
          apply pow_nonzero; lia.
          unfold memory.
          unfold mfib.
          rewrite bitvector_nat_big_inv; reflexivity.
      --  rewrite (fib_step_vals_2 (bitvector_nat_big
                    (Memory_Word_Load_from_Reg memory0
                        (nat_bitvector_big wordSize 0))) (bitvector_nat_big
                    (Memory_Word_Load_from_Reg memory0
                        (nat_bitvector_big wordSize 2))) _ 0).
          rewrite nat_bitvector_big_inv;[reflexivity|].
          apply mfib_upper_bound.
          all: try apply bitvector_nat_big_lt_2pow.
          apply pow_nonzero; lia.
          all: unfold memory, mfib; rewrite bitvector_nat_big_inv; reflexivity.
    + lia.
    + rewrite fib_step_index_dec.
      unfold registers; rewrite H0.
      rewrite bv_sub_correct_pos.
      f_equal.
      all: lia.
Qed.

(* register 00 has the same value as address 0 after each step. *)
Lemma fib_step_copy: forall m,
  nth (registers (fib_step m)) (bitvector_fin_big [b1; b0])
  = Memory_Word_Load_from_Reg (memory (fib_step m)) (nat_bitvector_big _ 0).
Proof.
  assert (4 < 2 ^ wordSize);[
    rewrite pureOp_store_b_lem;
    rewrite add_comm;
    change (2 ^ (8 + (wordSize - 8)))
      with (2 * (2 * (2 * 2 ^ (5 + (wordSize - 8)))));
    assert (0 < 2 ^ (5 + (wordSize - 8)));[apply Arith.zero2pow|lia]|].
  destruct m.
  unfold fib_step.
  unfold pureOp_cmpe, pureOp_cjmp, pureOp_load_w.
  repeat unfold registers at 2.
  unfold pureOp_add, pureOp_store_w, pureOp_sub, pureOp_jmp.
  unfold registers, memory.
  repeat rewrite (replace_swap _ (bitvector_fin_big [b1; b0]) (bitvector_fin_big [b0; b1])).
  repeat rewrite nth_replace.
  repeat rewrite replace_replace.
  repeat rewrite (replace_swap _ (bitvector_fin_big [b0; b1]) (bitvector_fin_big [b1; b0])).
  repeat rewrite nth_replace.
  Check replace_nth_irr.
  rewrite (replace_nth_irr _ _ (bitvector_fin_big [b1; b0])).
  rewrite (replace_nth_irr _ _ (bitvector_fin_big [b1; b0])).
  rewrite nth_replace.
  rewrite Memory_Word_Store_Load_from_Reg_Irr. 
  rewrite Memory_Word_Store_Load_from_Reg; reflexivity.
  repeat rewrite nat_bitvector_big_inv;change wordSizeEighth with 2;lia.
  all: simpl; lia.
Qed.

(* register 00 has the same value as address 0 after each step_r. *)
Lemma fib_step_r_copy: forall n m,
  nth (registers (fib_step_r m (fib_init (initialState FibProgram
        (nat_bitvector_big wordSize n :: nil)%list nil)))) (bitvector_fin_big [b1; b0])
  = Memory_Word_Load_from_Reg (memory (fib_step_r m (fib_init (initialState FibProgram
        (nat_bitvector_big wordSize n :: nil)%list nil)))) (nat_bitvector_big _ 0).
Proof.
  assert (4 < 2 ^ wordSize);[
    rewrite pureOp_store_b_lem;
    rewrite add_comm;
    change (2 ^ (8 + (wordSize - 8)))
      with (2 * (2 * (2 * 2 ^ (5 + (wordSize - 8)))));
    assert (0 < 2 ^ (5 + (wordSize - 8)));[apply Arith.zero2pow|lia]|].
  intro n.
  destruct m.
  - unfold fib_step_r.
    unfold initialState, fib_init, pureOp_mov, pureOp_store_w, pureOp_read, registers.
    unfold memory.
    rewrite nat_bitvector_big_inv;[|apply Arith.zero2pow].
    rewrite nth_replace.
    repeat rewrite replace_nth_irr.
    rewrite Memory_Word_Store_Load_from_Reg_Irr.
    rewrite Memory_Word_Load_from_Reg_const.
    reflexivity.
    repeat rewrite nat_bitvector_big_inv;change wordSizeEighth with 2;lia.
    all: simpl; lia.
  - rewrite fib_step_r_unfold_out.
    apply fib_step_copy.
Qed.

(* After running fib_full instructions, reg 10 contains the appropriate value *)
Lemma fib_full_vals : forall n, 
  n < 2 ^ wordSize ->
  nth (registers (fib_full (initialState FibProgram
        (nat_bitvector_big wordSize n :: nil)%list nil)))
      (bitvector_fin_big [b1; b0])
  = nat_bitvector_big _ (fib n mod (2 ^ wordSize)).
Proof.
  assert (4 < 2 ^ wordSize);[
    rewrite pureOp_store_b_lem;
    rewrite add_comm;
    change (2 ^ (8 + (wordSize - 8)))
      with (2 * (2 * (2 * 2 ^ (5 + (wordSize - 8)))));
    assert (0 < 2 ^ (5 + (wordSize - 8)));[apply Arith.zero2pow|lia]|].
  intros n nLT.
  unfold fib_full, fib_finish.
  rewrite registers_pureOp_cjmp, registers_pureOp_cmpe.
  rewrite <- mfib_mod;[|exact pureOp_read_correct_lem].
  rewrite fib_step_r_copy.
  rewrite fib_step_r_vals.
  unfold initialState, fib_init, pureOp_mov, pureOp_store_w, pureOp_read, registers.
  unfold memory.
  repeat rewrite nth_replace.
  rewrite Memory_Word_Store_Load_from_Reg_Irr.
  rewrite Memory_Word_Load_from_Reg_const.
  rewrite Memory_Word_Store_Load_from_Reg.
  rewrite nat_bitvector_big_inv;[|exact pureOp_read_correct_lem].
  rewrite nat_bitvector_big_inv;[|apply Arith.zero2pow].
  rewrite nat_bitvector_big_inv;[|assumption].
  reflexivity.
  repeat rewrite nat_bitvector_big_inv;change wordSizeEighth with 2;lia.
  apply bitvector_nat_big_lt_2pow.
  rewrite bitvector_nat_big_inv; reflexivity.
Qed.

(* We can compose our previous lines of proof together to observe 
  that the state is correctly calculated by fib_full and the value
  is correctly calculated by (fib n mod (2 ^ wordSize) *)
Lemma fib_ret_state_val : forall n, 
  n < 2 ^ wordSize ->
  (interp_machine (E := void1) run
     (initialState FibProgram
        (nat_bitvector_big wordSize n :: nil)%list nil))
  ≈ Ret (fib_full (initialState FibProgram
                   (nat_bitvector_big wordSize n :: nil)%list nil),
         nat_bitvector_big _ (fib n mod (2 ^ wordSize))).
Proof.
  intros n lt. rewrite fib_runs_full;[|assumption].
  rewrite interp_machine_run_halt_reg;
  [ rewrite fib_full_vals;[reflexivity|assumption]
  | rewrite fib_full_answer;[reflexivity|assumption]
  | apply encode_decode_id ].
Qed.

(*And, finally, we have our main theorem, that our assembly
  program correctly calculates the fibonacci numbers within
  the bounds of mow 2 ^ wordSize. *)
Theorem fib_correct : forall n,
  n < 2 ^ wordSize ->
  fib_asm n ≈ Ret (nat_bitvector_big _ (fib n mod (2 ^ wordSize))).
Proof.
  intros n lt.
  unfold fib_asm, interp_program.
  rewrite fib_ret_state_val;[|assumption].
  unfold ITree.map.
  rewrite bind_ret_l.
  reflexivity.
Qed.
