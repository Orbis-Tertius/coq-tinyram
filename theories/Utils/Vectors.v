From Coq Require Import
  Lia.
From TinyRAM.Utils Require Import
  Fin.
From TinyRAM.Utils Require Import
  Arith.
Import PeanoNat.Nat.
Require Import ProofIrrelevance.
Require Import VectorDef.
Import VectorNotations.

Definition vector_length_coerce : forall {A n m},
    n = m ->
    Vector.t A n ->
    Vector.t A m.
  intros A n m eq v. rewrite <- eq. assumption. Defined.

Theorem vector_length_coerce_trans : forall {A n m o}
    (eq1 : n = m) (eq2 : m = o) (v : Vector.t A n),
    (vector_length_coerce eq2 (vector_length_coerce eq1 v))
    = (vector_length_coerce (eq_trans eq1 eq2) v).
Proof.
  intros A n m o eq1 eq2 v.
  destruct eq1, eq2.
  reflexivity.
Qed.

Theorem vector_length_coerce_id : forall {A n}
    (eq : n = n) (v : Vector.t A n),
    (vector_length_coerce eq v)
    = v.
Proof.
  intros A n eq v.
  replace eq with (eq_refl n).
  - reflexivity.
  - apply proof_irrelevance.
Qed.

Theorem vector_length_coerce_inv : forall {A n m}
    (eq : n = m) (v : Vector.t A n),
    (vector_length_coerce (eq_sym eq) (vector_length_coerce eq v)) = v.
Proof.
  intros A n m eq v.
  destruct eq.
  reflexivity.
Qed.

Theorem vector_length_coerce_inv2 : forall {A n m}
  (eq : m = n) (v : Vector.t A n),
  (vector_length_coerce eq (vector_length_coerce (eq_sym eq) v)) = v.
Proof.
  intros A n m eq v.
  destruct eq.
  reflexivity.
Qed.

Theorem vector_length_coerce_cons : forall {A n m}
  (h : A) (vn : Vector.t A n) (eq : S n = S m),
  vector_length_coerce eq (h :: vn)
  = h :: vector_length_coerce (succ_inj _ _ eq) vn.
Proof.
  intros A n m h vn eq.
  destruct (succ_inj n m eq).
  replace eq with (eq_refl (S n)).
  2: { apply proof_irrelevance. }
  simpl; f_equal.
Qed.

Theorem vector_length_coerce_app_l : forall {A n m o}
  (vn : Vector.t A n) (vm : Vector.t A m) (eq : n + m = n + o),
  vector_length_coerce eq (vn ++ vm)
  = vn ++ vector_length_coerce (Plus.plus_reg_l _ _ _ eq) vm.
Proof.
  intros A n m o vn vm eq.
  destruct (Plus.plus_reg_l _ _ _ eq).
  replace eq with (eq_refl (n + m)).
  2: { apply proof_irrelevance. }
  simpl; f_equal.
Qed.

Theorem vector_length_coerce_app_r : forall {A n m o}
  (vn : Vector.t A n) (vm : Vector.t A m) (eq : n + m = o + m),
  vector_length_coerce eq (vn ++ vm)
  = vector_length_coerce (plus_reg_r _ _ _ eq) vn ++ vm.
Proof.
  intros A n m o vn vm eq.
  destruct (plus_reg_r _ _ _ eq).
  replace eq with (eq_refl (n + m)).
  2: { apply proof_irrelevance. }
  simpl; f_equal.
Qed.

Theorem vector_length_coerce_app_funct : forall {A n1 n2 m1 m2}
  (neq : n1 = n2) (meq : m1 = m2)
  (vn : Vector.t A n1) (vm : Vector.t A m1),
  vector_length_coerce neq vn ++ vector_length_coerce meq vm
  = vector_length_coerce (f_equal2_plus _ _ _ _ neq meq) (vn ++ vm).
Proof.
  intros A n1 n2 m1 m2 neq meq vn vm.
  destruct neq, meq.
  replace (f_equal2_plus _ _ _ _ _ _) with (eq_refl (n1 + m1)).
  { reflexivity. }
  apply proof_irrelevance.
Qed.

Theorem vector_length_coerce_app_assoc_1 : forall {A n m o}
  (vn : Vector.t A n) (vm : Vector.t A m) (vo : Vector.t A o),
  vector_length_coerce (add_assoc n m o) (vn ++ (vm ++ vo))
  = (vn ++ vm) ++ vo.
Proof.
  intros A n m o vn vm vo.
  induction vn.
  - simpl.
    replace (add_assoc 0 m o) with (eq_refl (m + o)).
    + reflexivity.
    + apply proof_irrelevance.
  - simpl.
    rewrite vector_length_coerce_cons.
    f_equal.
    rewrite <- IHvn.
    f_equal.
    apply proof_irrelevance.
Qed.

Theorem vector_length_coerce_app_assoc_2 : forall {A n m o}
  (vn : Vector.t A n) (vm : Vector.t A m) (vo : Vector.t A o),
  vector_length_coerce (eq_sym (add_assoc n m o)) ((vn ++ vm) ++ vo)
  = vn ++ (vm ++ vo).
Proof.
  intros A n m o vn vm vo.
  induction vn.
  - simpl.
    replace (add_assoc 0 m o) with (eq_refl (m + o)).
    + reflexivity.
    + apply proof_irrelevance.
  - simpl.
    rewrite vector_length_coerce_cons.
    f_equal.
    rewrite <- IHvn.
    f_equal.
    apply proof_irrelevance.
Qed.

Definition vector_cons_split : forall {A n}
  (v : Vector.t A (S n)), 
  { x : A & { vtl : Vector.t A n | v = Vector.cons A x n vtl } }.
  intros A n v.
  exists (Vector.hd v), (Vector.tl v). apply Vector.eta.
Defined.

Definition replace :
  forall {A n} (v : Vector.t A n) (p: fin n) (a : A), Vector.t A n.
  intros A n; induction n as [|n IHn]; intros v [p pprp] a.
  - apply Vector.nil.
  - destruct (vector_cons_split v) as [vhd [vtl _]].
    destruct p.
    + apply Vector.cons.
      * exact a.
      * exact vtl.
    + apply Vector.cons.
      * exact vhd.
      * apply (fun x => IHn vtl x a).
        exists p.
        lia.
Defined. 

Definition nth :
  forall {A n} (v : Vector.t A n) (p: fin n), A.
  intros A n; induction n as [|n IHn]; intros v [p pprp].
  - destruct (nlt_0_r _ pprp).
  - destruct (vector_cons_split v) as [vhd [vtl _]].
    destruct p.
    + exact vhd.
    + apply (IHn vtl).
      exists p.
      lia.
Defined.

Definition bitvector_fin_double_S : forall {n},
  fin n -> fin (2 * n).
  intros n a.
  destruct a as [a afin].
  exists (S (2 * a)).
  lia.
Defined.

Definition bitvector_fin_double : forall {n},
  fin n -> fin (2 * n).
  intros n a.
  destruct a as [a afin].
  exists (2 * a).
  lia.
Defined.

Definition bitvector_fin : forall {n},
  Vector.t bool n -> fin (2 ^ n).
  intros n v.
  induction v.
  - exists 0.
    simpl.
    lia.
  - destruct h eqn:hdef.
    + apply (bitvector_fin_double_S IHv).
    + apply (bitvector_fin_double IHv).
Defined.

Definition fin_mod : forall n m,
  n <> 0 -> fin (m * n) -> fin n.
  intros n m meq f.
  destruct f as [f fprp].
  exists (f mod n).
  apply mod_upper_bound.
  assumption.
Defined.

Fixpoint fin_bitvector_fun (n m : nat) : Vector.t bool n :=
  match n with
  | 0 => Vector.nil bool
  | S n => 
    Vector.cons _ (negb (m mod 2 =? 0)) _ (fin_bitvector_fun n (m / 2))
  end.

Definition fin_bitvector : forall {n},
  fin (2 ^ n) -> Vector.t bool n.
  intros n [f _].
  apply (fin_bitvector_fun n f).
Defined.

Theorem bitvector_fin_inv_lem_true : forall {n} (f : fin (2 ^ n)),
  fin_bitvector (bitvector_fin_double_S f : fin (2 ^ (S n))) =
  Vector.cons _ true _ (fin_bitvector f).
Proof.
  intros n.
  destruct n as [|n]; intros [f fprp].
  - rewrite unique_f0 at 1.
    reflexivity.
  - simpl bitvector_fin_double_S.
    unfold fin_bitvector.
    unfold fin_bitvector_fun.
    replace (S (f + (f + 0))) with (1 + f * 2).
    2: { lia. }
    replace (((1 + f * 2)) mod 2) with 1.
    2: { rewrite mod_add. { reflexivity. } { lia. } }
    replace ((1 + f * 2) / 2) with f.
    2: { rewrite div_add. { reflexivity. } { lia. } }
    reflexivity.
Qed.

Theorem bitvector_fin_inv_lem_false : forall {n} (f : fin (2 ^ n)),
  fin_bitvector (bitvector_fin_double f : fin (2 ^ (S n))) =
  Vector.cons bool false _ (fin_bitvector f).
Proof.
  intros n.
  destruct n as [|n]; intros [f fprp].
  - rewrite unique_f0 at 1.
    reflexivity.
  - simpl bitvector_fin_double.
    unfold fin_bitvector.
    unfold fin_bitvector_fun.
    replace (f + (f + 0)) with (f * 2).
    2: { lia. }
    replace (f * 2 / 2) with f.
    2: { rewrite div_mul. { reflexivity. } { lia. } }
    replace ((f * 2) mod 2) with 0.
    2: { symmetry. rewrite mod_mul. { reflexivity. } { lia. } } 
    reflexivity.
Qed.

Theorem bitvector_fin_inv : forall {n} (v : Vector.t bool n),
  fin_bitvector (bitvector_fin v) = v.
Proof.
  intros n v.
  induction v.
  - reflexivity.
  - destruct h; simpl bitvector_fin.
    + rewrite bitvector_fin_inv_lem_true.
      rewrite IHv.
      reflexivity.
    + rewrite bitvector_fin_inv_lem_false.
      rewrite IHv.
      reflexivity.
Qed.

Theorem mod_2_0or1 : forall n, (n mod 2 = 0) \/ (n mod 2 = 1).
Proof.
  intro.
  induction n as [|n IHn].
  - auto.
  - replace (S n) with (1 + n). 2: { reflexivity. }
    rewrite add_mod. 2: { lia. }
    destruct IHn.
    + right.
      rewrite H.
      reflexivity.
    + left.
      rewrite H.
      reflexivity.
Qed.

Theorem fin_bitvector_inv : forall {n} (f : fin (2 ^ n)),
  bitvector_fin (fin_bitvector f) = f.
  intro n.
  induction n as [|n IHn]; intros [f fprp].
  + simpl.
    rewrite unique_f0.
    apply subset_eq_compat.
    reflexivity.
  + unfold fin_bitvector.
    replace (fin_bitvector_fun (S n) f)
       with (Vector.cons _ (negb (f mod 2 =? 0)) _ (fin_bitvector_fun n (f / 2))).
    2: { reflexivity. }
    assert (f = (2 * (f / 2) + f mod 2)) as fsplit.
    { rewrite <- div_mod. { reflexivity. } { lia. } }
    assert (f/2 < 2 ^ n) as fhprp.
    { apply div_lt_upper_bound. { lia. } exact fprp. } 
    assert (bitvector_fin (fin_bitvector (exist _ (f/2) fhprp)) = (exist _ (f/2) fhprp)).
    { apply IHn. } clear IHn. simpl in H.
    destruct (f mod 2 =? 0) eqn:fmod;
    simpl; rewrite H; clear H; simpl;
    apply subset_eq_compat;
    replace (fst (divmod f 1 0 1)) with (f / 2); try reflexivity.
    - rewrite eqb_eq in fmod.
      rewrite fmod, add_0_r in fsplit.
      lia.
    - replace (f mod 2) with 1 in fsplit.
      { lia. }  
      rewrite eqb_neq in fmod.
      destruct (mod_2_0or1 f). { destruct (fmod H). }
      symmetry; assumption.
Qed.

Theorem vector_append_inv1 : forall {A n m}
    (v : Vector.t A (n + m)),
    uncurry Vector.append (Vector.splitat _ v) = v.
Proof.
  intros A n.
  induction n as [|n IHn];
  intros m.
  - intro; reflexivity.
  - intro v.
    simpl in v.
    destruct (vector_cons_split v) as [x [vtl eq]].
    rewrite eq.
    assert (uncurry Vector.append (Vector.splitat n vtl) = vtl).
    { apply IHn. }
    simpl.
    destruct (Vector.splitat n vtl) as [tl1 tl2].
    rewrite <- H.
    reflexivity.
Qed.

Theorem vector_append_inv2 : forall {A n m}
    (v1 : Vector.t A n) (v2 : Vector.t A m),
    Vector.splitat _ (Vector.append v1 v2) = (v1, v2).
  intros A n m v.
  generalize dependent m.
  induction v.
  - reflexivity.
  - simpl.
    intros m vs.
    rewrite IHv.
    reflexivity.
Qed.

Theorem vector_append_split : forall {A n m}
  (v : Vector.t A (n + m)), 
  (exists (vhd : Vector.t A n) (vtl : Vector.t A m),
  v = Vector.append vhd vtl).
Proof.
  intros A n m v.
  rewrite <- (vector_append_inv1 v).
  destruct (Vector.splitat n v) as [v1 v2].
  exists v1, v2.
  reflexivity.
Qed.

Definition vector_concat : forall {A n m},
    Vector.t (Vector.t A n) m -> Vector.t A (m * n).
  intros A n m v.
  induction v.
  - apply Vector.nil.
  - simpl.
    apply Vector.append.
    + apply h.
    + apply IHv.
Defined.

Definition vector_unconcat : forall {A n m},
    Vector.t A (m * n) -> Vector.t (Vector.t A n) m.
  intros A n m v.
  induction m as [|m IHm].
  - apply Vector.nil.
  - simpl in v; destruct (Vector.splitat _ v) as [vv1 vvtl].
    apply Vector.cons.
    + apply vv1.
    + apply IHm.
      apply vvtl.
Defined.

Theorem vector_concat_inv1_lem : forall {A n m}
  (v : Vector.t A (n * m))
  (u : Vector.t A m),
  vector_unconcat (Vector.append u v : Vector.t A (S n * m)) =
  Vector.cons _ u _ (vector_unconcat v).
Proof.
  intros A n m v u.
  generalize dependent v.
  induction u.
  - reflexivity.
  - intros v.
    simpl Vector.append.
    simpl vector_unconcat.
    rewrite vector_append_inv2.
    reflexivity.
Qed.

Theorem vector_concat_inv1 : forall {A n m}
  (v : Vector.t A (n * m)),
  vector_concat (vector_unconcat v) = v.
Proof.
  intros A n.
  induction n as [|n IHn];
  intros m v.
  - simpl.
    apply (Vector.case0 (fun v => Vector.nil A = v)).
    reflexivity.
  - simpl in v.
    destruct (vector_append_split v) as [vhd [vtl eq]].
    rewrite eq.
    rewrite vector_concat_inv1_lem.
    simpl.
    rewrite IHn.
    reflexivity.
Qed.

Theorem vector_concat_inv2 : forall {A n m}
    (v : Vector.t (Vector.t A n) m),
    vector_unconcat (vector_concat v) = v.
  intros A n m.
  induction v.
  - reflexivity.
  - simpl.
    rewrite vector_append_inv2.
    rewrite IHv.
    reflexivity.
Qed.

Definition vector_concat_2 : forall {A n m},
    Vector.t (Vector.t A n) m -> Vector.t A (n * m).
  intros A n m v.
  rewrite PeanoNat.Nat.mul_comm.
  apply vector_concat.
  assumption.
Defined.

Definition Block_Lem : forall idx blksz memsz,
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

Definition Block_Load_Store : forall {B memsz}
    (m : Vector.t B memsz)
    (idx blksz: fin memsz)
    (block : Vector.t B (proj1_sig blksz)),
    Vector.t B (proj1_sig blksz) * Vector.t B memsz.
  intros B memsz m [idx lip] [blksz lbp] block.
  destruct (Block_Lem _ _ _ lip lbp) as 
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

(* Memory_Block_Load w/o rebuilding memory. *)
Definition Block_Load : forall {B memsz}
    (m : Vector.t B memsz)
    (idx blksz: fin memsz),
    Vector.t B (proj1_sig blksz).
  intros B memsz m [idx lip] [blksz lbp].
  destruct (Block_Lem _ _ _ lip lbp) as 
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

Definition Block_Store {B memsz}
    (m : Vector.t B memsz)
    (idx blksz: fin memsz)
    (block : Vector.t B (proj1_sig blksz)) :
    Vector.t B memsz :=
  snd (Block_Load_Store m idx blksz block).

