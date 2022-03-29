From Coq Require Import
  Lia Nat VectorDef VectorEq ProofIrrelevance.
Import VectorNotations EqNotations.
From TinyRAM.Utils Require Import
  Fin Arith.

Import PeanoNat.Nat(succ_inj, 
                    add_assoc, 
                    add_comm, 
                    nlt_0_r,
                    mul_comm,
                    ltb_lt).

Theorem cast_rew : forall {A} {m n} (eq : m = n) (v : t A m),
  cast v eq = rew eq in v.
Proof.
  intros A m n eq v. 
  generalize dependent n; induction v; intros.
  - destruct eq; reflexivity.
  - destruct eq; simpl; rewrite IHv; reflexivity.
Qed.

Theorem cast_trans : forall {A n m o}
    (eq1 : n = m) (eq2 : m = o) (v : t A n),
    (cast (cast v eq1) eq2)
    = (cast v (eq_trans eq1 eq2)).
Proof.
  intros A n m o eq1 eq2 v.
  destruct eq1, eq2.
  repeat rewrite cast_rew; reflexivity.
Qed.

Theorem cast_id : forall {A n} (eq : n = n) (v : t A n), (cast v eq) = v.
Proof.
  intros A n eq v.
  replace eq with (eq_refl n).
  - rewrite cast_rew; reflexivity.
  - apply proof_irrelevance.
Qed.

Theorem cast_cons : forall {A n m}
  (h : A) (vn : t A n) (eq : S n = S m),
  cast (h :: vn)  eq
  = h :: cast vn (succ_inj _ _ eq).
Proof.
  intros A n m h vn eq.
  destruct (succ_inj n m eq).
  replace eq with (eq_refl (S n)).
  2: { apply proof_irrelevance. }
  reflexivity.
Qed.

Theorem cast_app_l : forall {A n m o}
  (vn : t A n) (vm : t A m) (eq : n + m = n + o),
  cast (vn ++ vm) eq
  = vn ++ cast vm (Plus.plus_reg_l _ _ _ eq).
Proof.
  intros A n m o vn vm eq.
  destruct (Plus.plus_reg_l _ _ _ eq).
  replace eq with (eq_refl (n + m)).
  2: { apply proof_irrelevance. }
  repeat rewrite cast_id; reflexivity.
Qed.

Theorem cast_app_r : forall {A n m o}
  (vn : t A n) (vm : t A m) (eq : n + m = o + m),
  cast (vn ++ vm) eq
  = cast vn (plus_reg_r _ _ _ eq) ++ vm.
Proof.
  intros A n m o vn vm eq.
  destruct (plus_reg_r _ _ _ eq).
  replace eq with (eq_refl (n + m)).
  2: { apply proof_irrelevance. }
  repeat rewrite cast_id; reflexivity.
Qed.

Theorem cast_app_funct : forall {A n1 n2 m1 m2}
  (neq : n1 = n2) (meq : m1 = m2)
  (vn : t A n1) (vm : t A m1),
  cast vn neq ++ cast vm meq
  = cast (vn ++ vm) (f_equal2_plus _ _ _ _ neq meq).
Proof.
  intros A n1 n2 m1 m2 neq meq vn vm.
  destruct neq, meq.
  replace (f_equal2_plus _ _ _ _ _ _) with (eq_refl (n1 + m1)).
  { repeat rewrite cast_id; reflexivity. }
  apply proof_irrelevance.
Qed.



Theorem cast_app_right_lem :
  forall n m o, m = o -> m + n = o + n.
Proof. intros n m o eq; destruct eq; reflexivity. Qed.

Theorem cast_app_right : 
  forall {A n m o} (vn : t A n) (vm : t A m) (eq : m = o),
    cast vm eq ++ vn = cast (vm ++ vn) (cast_app_right_lem n m o eq).
Proof.
  intros A n m o vn vm eq; destruct eq.
  repeat rewrite cast_id.
  reflexivity.
Qed.

Theorem cast_app_left_lem :
  forall n m o, m = o -> n + m = n + o.
Proof. intros n m o eq; destruct eq; reflexivity. Qed.

Theorem cast_app_left : 
  forall {A n m o} (vn : t A n) (vm : t A m) (eq : m = o),
    vn ++ cast vm eq =
    cast (vn ++ vm) (cast_app_left_lem n m o eq).
Proof.
  intros A n m o vn vm eq; destruct eq.
  repeat rewrite cast_id.
  reflexivity.
Qed.

Theorem cast_app_assoc_1 : forall {A n m o}
  (vn : t A n) (vm : t A m) (vo : t A o),
  cast (vn ++ (vm ++ vo)) (add_assoc n m o)
  = (vn ++ vm) ++ vo.
Proof.
  intros A n m o vn vm vo.
  induction vn.
  - simpl.
    replace (add_assoc 0 m o) with (eq_refl (m + o)).
    + rewrite cast_id; reflexivity.
    + apply proof_irrelevance.
  - simpl.
    f_equal.
    rewrite <- IHvn.
    f_equal.
    apply proof_irrelevance.
Qed.

Theorem cast_app_assoc_2 : forall {A n m o}
  (vn : t A n) (vm : t A m) (vo : t A o),
  cast ((vn ++ vm) ++ vo)  (eq_sym (add_assoc n m o))
  = vn ++ (vm ++ vo).
Proof.
  intros A n m o vn vm vo.
  induction vn.
  - simpl.
    replace (add_assoc 0 m o) with (eq_refl (m + o)).
    + rewrite cast_id; reflexivity.
    + apply proof_irrelevance.
  - simpl.
    f_equal.
    rewrite <- IHvn.
    f_equal.
    apply proof_irrelevance.
Qed.

Theorem vector_nil_eq : forall {A} (v : t A 0),
  v = [].
Proof.
  intros A v.
  apply (case0 (fun vnil => vnil = [])).
  reflexivity.
Qed.

Definition vector_cons_split : forall {A n}
  (v : t A (S n)), 
  { x : A & { vtl : t A n | v = cons A x n vtl } }.
  intros A n v.
  exists (hd v), (tl v). apply Vector.eta.
Defined.

Definition replace :
  forall {A n} (v : t A n) (p: fin n) (a : A), t A n.
  intros A n; induction n as [|n IHn]; intros v [p pprp] a.
  - apply nil.
  - destruct (vector_cons_split v) as [vhd [vtl _]].
    destruct p.
    + apply cons.
      * exact a.
      * exact vtl.
    + apply cons.
      * exact vhd.
      * apply (fun x => IHn vtl x a).
        exists p.
        lia.
Defined. 

Definition nth :
  forall {A n} (v : t A n) (p: fin n), A.
  intros A n; induction n as [|n IHn]; intros v [p pprp].
  - destruct (nlt_0_r _ pprp).
  - destruct (vector_cons_split v) as [vhd [vtl _]].
    destruct p.
    + exact vhd.
    + apply (IHn vtl).
      exists p.
      lia.
Defined.

Theorem vector_rev_append_nil_o : forall {A n}
  (v : t A n),
  rev_append [] v = v.
Proof.
  intros A n v.
  destruct v.
  - unfold rev_append.
    simpl.
    replace (Plus.plus_tail_plus 0 0) with (eq_refl 0).
    { reflexivity. } { apply proof_irrelevance. }
  - unfold rev_append.
    simpl rev_append_tail.
    replace (Plus.plus_tail_plus 0 (S n))
       with (eq_refl (S n)).
    { reflexivity. } { apply proof_irrelevance. }
Qed.

Theorem rev_coerce_unfold : forall {A n}
  (v : t A n),
  rev v = 
  cast (rev_append v []) (eq_sym (plus_n_O n)).
Proof.
  intros A n v.
  rewrite cast_rew; reflexivity.
Qed.

Theorem vector_rev_nil_nil : forall {A},
  rev [] = ([] : t A 0).
Proof.
  intros A.
  rewrite rev_coerce_unfold.
  rewrite vector_rev_append_nil_o.
  replace (plus_n_O 0) with (eq_refl 0).
  { reflexivity. } { apply proof_irrelevance. }
Qed.

Theorem vector_rev_sing_sing : forall {A} (h : A),
  rev [h] = [h].
Proof.
  intros A h.
  rewrite rev_coerce_unfold.
  replace (rev_append [h] []) with [h].
  { replace (plus_n_O 1) with (eq_refl 1).
    { reflexivity. } { apply proof_irrelevance. } }
  unfold rev_append.
  simpl. 
  replace (Plus.plus_tail_plus 1 0) with (eq_refl 1).
  { reflexivity. } { apply proof_irrelevance. }
Qed.

Definition last_ : forall {A n}, t A (n + 1) -> A.
  intros A n v.
  rewrite add_comm in v.
  apply (@last A n).
  exact v.
Defined.

Definition most : forall {A n}, t A (S n) -> t A n.
  intros A n v.
  induction n.
  - apply nil.
  - apply cons.
    + exact (hd v).
    + apply IHn.
      exact (tl v).
Defined.

Definition most_ : forall {A n}, t A (n + 1) -> t A n.
  intros A n v.
  rewrite add_comm in v.
  apply (@most A n).
  exact v.
Defined.

Theorem vector_snoc_eta : forall {A n}
  (v : t A (n + 1)),
  v = most_ v ++ [last_ v].
Proof.
  intros A n v.
  induction n.
  - rewrite (vector_nil_eq (most_ v)).
    rewrite (Vector.eta v).
    rewrite (vector_nil_eq (tl v)).
    simpl; f_equal.
    unfold last_.
    replace (add_comm 0 1) with (eq_refl 1).
    2: { apply proof_irrelevance. }
    reflexivity.
  - rewrite (Vector.eta v).
    assert (tl v = most_ (tl v) ++ [last_ (tl v)]).
    { apply IHn. }
    rewrite H at 1.
    simpl; f_equal.
    + rewrite <- cast_rew.
      reflexivity.
    + f_equal.
      * rewrite <- cast_rew.
        simpl; unfold most_.
        rewrite cast_rew.
        repeat f_equal.
        apply proof_irrelevance.
      * unfold last_ at 2.
        rewrite <- cast_rew.
        rewrite (cast_cons _ (tl v)).
        unfold last_; rewrite cast_rew.
        simpl; repeat f_equal.
        apply proof_irrelevance.
Qed.


Theorem t_snoc_ind : forall (A : Type) (P : forall n : nat, t A n -> Prop),
  P 0 [] ->
  (forall (h : A) (n : nat) (v : t A n), P n v -> P (n + 1) (v ++ [h])) ->
  forall (n : nat) (v : t A n), P n v.
Proof.
  intros A P Pnil Psnoc n v.
  induction n.
  - rewrite (vector_nil_eq v).
    exact Pnil.
  - remember (cast v (eq_sym (add_comm n 1))) as v'.
    assert (v' = most_ v' ++ [last_ v']).
    { apply vector_snoc_eta. }
    assert (P n (most_ v')).
    { apply IHn. }
    apply (Psnoc (last_ v') _ _) in H0.
    assert (n + 1 = S n).
    { rewrite add_comm; reflexivity. }
    apply (depEqLem nat (t A) P (n + 1) (S n) H1 v' v).
    2: { rewrite H; assumption. }
    rewrite Heqv', cast_rew, rew_compose, rew_id.
    reflexivity.
Qed.

Theorem rev_append_step : forall {A n m}
  (h : A) (vn : t A n) (vm : t A m),
  rev_append (h :: vn) vm =
  cast (rev_append vn (h :: vm)) (eq_sym (plus_n_Sm n m)).
Proof.
  intros A n m h vn vm.
  unfold rev_append.
  simpl rev_append_tail.
  rewrite cast_rew.
  unfold eq_rect_r.
  rewrite rew_compose.
  f_equal.
  apply proof_irrelevance.
Qed.

Theorem rev_append_unstep : forall {A n m}
  (h : A) (vn : t A n) (vm : t A m),
  rev_append vn (h :: vm) =
  cast (rev_append (h :: vn) vm) (plus_n_Sm n m).
Proof.
  intros A n m h vn vm.
  unfold rev_append.
  simpl rev_append_tail.
  rewrite cast_rew.
  unfold eq_rect_r.
  rewrite rew_compose.
  f_equal.
  apply proof_irrelevance.
Qed.

Theorem append_nil : forall {A n}
  (vn : t A n),
  vn ++ [] =
  cast vn (plus_n_O n).
Proof.
  intros A n vn; induction vn.
  - rewrite cast_id.
    reflexivity.
  - simpl.
    rewrite IHvn.
    repeat f_equal.
    apply proof_irrelevance.
Qed.

Theorem cast_cons_in : forall {A n m}
  (eq : n = m) (h : A) (vn : t A n),
  h :: cast vn eq
  = cast (h :: vn) (eq_S _ _ eq).
Proof.
  intros A n m eq h vn.
  destruct eq.
  reflexivity.
Qed.

Theorem rev_append_app_step_lem : forall {n m},
  S (n + m) = (n + 1 + m).
Proof. lia. Qed.

Theorem rev_append_cons : forall {A n m}
  (h : A) (vn : t A n) (vm : t A m),
  rev_append (vn ++ [h]) vm =
  cast (h :: rev_append vn vm) rev_append_app_step_lem.
Proof.
  intros A n m h vn vm.
  generalize dependent m.
  generalize dependent h.
  induction vn; intros.
  - simpl.
    replace (rev_append [h] vm)
       with (rev_append [] (h :: vm)).
    repeat rewrite vector_rev_append_nil_o.
    rewrite cast_id.
    reflexivity.
    rewrite rev_append_step.
    rewrite cast_id.
    reflexivity.
  - simpl. 
    rewrite rev_append_step.
    rewrite IHvn.
    rewrite rev_append_step.
    repeat rewrite cast_cons_in, cast_trans.
    f_equal; apply proof_irrelevance.
Qed.

Theorem rev_append_app : forall {A n m o}
  (vn : t A n) (vm : t A m) (vo : t A o),
  rev_append vn vm ++ vo =
  cast (rev_append vn (vm ++ vo)) (add_assoc n m o).
Proof.
  intros A n m o vn vm vo.
  generalize dependent m.
  generalize dependent o.
  induction vn; intros.
  - repeat rewrite vector_rev_append_nil_o.
    rewrite cast_id.
    reflexivity.
  - repeat rewrite rev_append_step.
    rewrite <- (cast_id (eq_refl o) vo) at 1.
    rewrite cast_app_funct.
    rewrite (IHvn _ vo _ (h :: vm)).
    repeat rewrite cast_trans.
    f_equal.
    apply proof_irrelevance.
Qed.

Theorem rev_append_app_2 : forall {A n m o}
  (vn : t A n) (vm : t A m) (vo : t A o),
  rev_append vn (vm ++ vo) =
  cast (rev_append vn vm ++ vo) (eq_sym (add_assoc n m o)).
Proof.
  intros A n m o vn vm vo.
  rewrite rev_append_app.
  rewrite cast_trans.
  rewrite cast_id.
  reflexivity.
Qed.

Theorem rev_cons : forall {A n} (h : A) (v : t A n),
  rev (v ++ [h]) = cast (h :: rev v)  (add_comm 1 n).
Proof.
  intros A n h v.
  repeat rewrite rev_coerce_unfold.
  rewrite rev_append_cons.
  rewrite cast_cons_in.
  repeat rewrite cast_trans.
  f_equal.
  apply proof_irrelevance.
Qed.

Theorem rev_snoc : forall {A n} (h : A) (v : t A n),
  rev (h :: v) = cast (rev v ++ [h]) (add_comm n 1).
Proof.
  intros A n h v.
  repeat rewrite rev_coerce_unfold.
  rewrite rev_append_step, cast_app_right.
  rewrite (rev_append_app v [] [h]).
  repeat rewrite cast_trans.
  f_equal.
  apply proof_irrelevance.
Qed.

Theorem cast_f_swap : forall {A n m}
  (f : forall x, t A x -> t A x)
  (eq : n = m)
  (v : t A n),
  f _ (cast v eq) =
  cast (f _ v) eq.
Proof.
  intros A n m f eq v.
  destruct eq. 
  repeat rewrite cast_id.
  reflexivity.
Qed.

Theorem vector_rev_rev_id : forall {A n}
  (v : t A n),
  rev (rev v) = v.
Proof.
  intros A n v; induction v using t_snoc_ind.
  - repeat rewrite vector_rev_nil_nil.
    reflexivity.
  - rewrite rev_cons.
    rewrite (cast_f_swap (@rev A)).
    rewrite rev_snoc, IHv,
            cast_trans,
            cast_id.
    reflexivity.
Qed.

Theorem vector_append_inv1 : forall {A n m}
    (v : t A (n + m)),
    uncurry append (splitat _ v) = v.
Proof.
  intros A n.
  induction n as [|n IHn];
  intros m.
  - intro; reflexivity.
  - intro v.
    simpl in v.
    destruct (vector_cons_split v) as [x [vtl eq]].
    rewrite eq.
    assert (uncurry append (splitat n vtl) = vtl).
    { apply IHn. }
    simpl.
    destruct (splitat n vtl) as [tl1 tl2].
    rewrite <- H.
    reflexivity.
Qed.

Theorem vector_append_inv2 : forall {A n m}
    (v1 : t A n) (v2 : t A m),
    splitat _ (append v1 v2) = (v1, v2).
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
  (v : t A (n + m)), 
  (exists (vhd : t A n) (vtl : t A m),
  v = append vhd vtl).
Proof.
  intros A n m v.
  rewrite <- (vector_append_inv1 v).
  destruct (splitat n v) as [v1 v2].
  exists v1, v2.
  reflexivity.
Qed.

Definition vector_concat : forall {A n m},
    t (t A n) m -> t A (m * n).
  intros A n m v.
  induction v.
  - apply nil.
  - simpl.
    apply append.
    + apply h.
    + apply IHv.
Defined.

Definition vector_unconcat : forall {A n m},
    t A (m * n) -> t (t A n) m.
  intros A n m v.
  induction m as [|m IHm].
  - apply nil.
  - simpl in v; destruct (splitat _ v) as [vv1 vvtl].
    apply cons.
    + apply vv1.
    + apply IHm.
      apply vvtl.
Defined.

Theorem vector_concat_inv1_lem : forall {A n m}
  (v : t A (n * m))
  (u : t A m),
  vector_unconcat (append u v : t A (S n * m)) =
  cons _ u _ (vector_unconcat v).
Proof.
  intros A n m v u.
  generalize dependent v.
  induction u.
  - reflexivity.
  - intros v.
    simpl append.
    simpl vector_unconcat.
    rewrite vector_append_inv2.
    reflexivity.
Qed.

Theorem vector_concat_inv1 : forall {A n m}
  (v : t A (n * m)),
  vector_concat (vector_unconcat v) = v.
Proof.
  intros A n.
  induction n as [|n IHn];
  intros m v.
  - simpl.
    apply (case0 (fun v => nil A = v)).
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
    (v : t (t A n) m),
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
    t (t A n) m -> t A (n * m).
  intros A n m v.
  rewrite mul_comm.
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
    (m : t B memsz)
    (idx blksz: fin memsz)
    (block : t B (proj1_sig blksz)),
    t B (proj1_sig blksz) * t B memsz.
  intros B memsz m [idx lip] [blksz lbp] block.
  destruct (Block_Lem _ _ _ lip lbp) as 
    [[tl eq]|[blk1[blk2[idx2[eq1 [eq2 eq3]]]]]].
  - rewrite eq in m.
    destruct (splitat _ m) as [m' m3].
    destruct (splitat _ m') as [m1 m2].
    split.
    { exact m2. }
    rewrite eq.
    exact (append (append m1 block) m3).
  - rewrite eq3 in m.
    destruct (splitat _ m) as [m' m3].
    destruct (splitat _ m') as [m1 m2].
    split.
    + apply (fun x => cast x eq1).
      (* Note: m1 is an overflow, so it's
              bits are more significant than m3. *)
      rewrite add_comm.
      apply (append m3 m1).
    + rewrite <- eq1 in block.
      destruct (splitat _ block) as [block1 block2].
      rewrite eq3.
      (* Note: The overflow means block2 should go at
              the begining of memory, and block 1 at the end. *)
      assert (blk1 + idx2 + blk2 = blk2 + idx2 + blk1) as OvrEq.
      { lia. }
      rewrite OvrEq.
      exact (append (append block2 m2) block1).
Defined.

(* Memory_Block_Load w/o rebuilding memory. *)
Definition Block_Load : forall {B memsz}
    (m : t B memsz)
    (idx blksz: fin memsz),
    t B (proj1_sig blksz).
  intros B memsz m [idx lip] [blksz lbp].
  destruct (Block_Lem _ _ _ lip lbp) as 
    [[tl eq]|[blk1[blk2[idx2[eq1 [eq2 eq3]]]]]].
  - rewrite eq in m.
    destruct (splitat _ m) as [m' _].
    destruct (splitat _ m') as [_ m2].
    exact m2.
  - rewrite eq3 in m.
    destruct (splitat _ m) as [m' m3].
    destruct (splitat _ m') as [m1 _].
    apply (fun x => cast x eq1).
    (* Note: m1 is an overflow, so it's
              bits are more significant than m3. *)
    rewrite add_comm.
    apply (append m3 m1).
Defined.

Definition Block_Store {B memsz}
    (m : t B memsz)
    (idx blksz: fin memsz)
    (block : t B (proj1_sig blksz)) :
    t B memsz :=
  snd (Block_Load_Store m idx blksz block).

Ltac vector_bubble :=
  match goal with
  | |- context[cast (cast _ _) _] =>
      rewrite cast_trans
  | |- context[?x ++ cast ?y _] =>
      rewrite cast_app_left
  | |- context[cast ?x _ ++ ?y] =>
      rewrite cast_app_right
  | |- context[?h :: cast ?y _] =>
      rewrite cast_cons_in
  | |- context[(?vn ++ ?vm) ++ ?vo] =>
      rewrite <- cast_app_assoc_1
  | |- context[rev []] =>
      rewrite vector_rev_nil_nil
  | |- context[rev (rev ?x)] =>
      rewrite vector_rev_rev_id
  | |- context[rev (?h :: ?x)] =>
      rewrite rev_snoc
  | |- context[rev (?x ++ [?h])] =>
      rewrite rev_cons
  end.

Ltac vector_simp :=
  repeat vector_bubble;
  repeat rewrite cast_id.

Example test : rev [false ; false ; false ; false ; false ]
                 = [ false ; false ; false ; false ; false ].
Proof.
  vector_simp.
  reflexivity.
Qed. 
