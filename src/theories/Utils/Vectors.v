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
                    mod_small, div_small,
                    ltb_lt, leb_le, ltb_ge).

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

Theorem cast_inj : forall {A n m} (eq : n = m) (v1 v2 : t A n),
    cast v1 eq = cast v2 eq -> v1 = v2.
Proof.
  intros.
  destruct eq.
  repeat rewrite cast_rew in H.
  exact H.
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

Theorem cast_app_distribute : forall {A n m k l} {eq : n + m = k + l}
  {v : t A n} {u : t A m} (eq1 : n = k) (eq2 : m = l),
  cast (v ++ u) eq = cast v eq1 ++ cast u eq2.
Proof.
  intros; destruct eq1, eq2.
  repeat rewrite cast_id.
  reflexivity.
Qed.

Theorem cast_swap : forall {A n m} (v : t A n) (u : t A m)
  (eq : n = m),
  cast v eq = u <-> v = cast u (eq_sym eq).
Proof.
  intros.
  split.
  - intros; rewrite <- H, cast_trans, cast_id; reflexivity.
  - intros; rewrite H, cast_trans, cast_id; reflexivity.
Qed.

Theorem cast_f_apply: forall {A n m} (v u : t A n) (eq : n = m),
  v = u <-> cast v eq = cast u eq.
Proof.
  intros.
  split.
  - intro H; rewrite H; reflexivity.
  - apply cast_inj.
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
  exists (hd v), (tl v). apply VectorSpec.eta.
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

Theorem nth_replace : forall {A a n} (v : t A n) (p: fin n),
  nth (replace v p a) p = a.
Proof. 
  intros; induction v.
  - destruct p; lia.
  - destruct p as [p pP].
    destruct p; [ reflexivity | ].
    apply IHv.
Qed.

Theorem replace_unfold : forall {A n} (l : t A n) h f x
  (lt : S f < S n),
  replace (h :: l) (mk_fin (S f) lt) x
  = h :: replace l (mk_fin f (Lt.lt_S_n _ _ lt)) x.
Proof.
  intros.
  simpl. repeat f_equal.
  apply subset_eq_compat.
  reflexivity.
Qed.

Theorem replace_replace : forall {A n} (l : t A n) f x y,
  replace (replace l f x) f y = replace l f y.
Proof.
  induction l; [ reflexivity | ].
  intros [f flt] x y.
  destruct f; [ reflexivity | ].
  simpl.
  rewrite IHl.
  reflexivity.
Qed.

Theorem replace_swap : forall {A n} (l : t A n) f g x y,
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

Theorem replace_nth_irr : forall {A n} (l : t A n) f g x,
  proj1_sig f <> proj1_sig g ->
  nth (replace l f x) g = nth l g.
Proof.
  induction l; [ reflexivity | ].
  intros [f flt] [g glt] x neq; simpl in neq.
  destruct f.
  - destruct g; [ contradiction | reflexivity ].
  - destruct g; [ reflexivity | simpl; rewrite IHl; auto ].
Qed.

Theorem nth_rew_l : forall {A n m} (eq : n = m)
  (v : t A n) (f : fin m),
  nth (rew eq in v) f = nth v (rew (eq_sym eq) in f).
Proof. intros; destruct eq; reflexivity. Qed.

Theorem nth_rew_r : forall {A n m} (eq : n = m)
  (v : t A m) (f : fin n),
  nth v (rew eq in f) = nth (rew (eq_sym eq) in v) f.
Proof. intros; destruct eq; reflexivity. Qed.

Theorem nth_app_l : forall {A n m o}
  (H : o < n + m) (H1 : o < n) (vn : t A n) (vm : t A m),
  nth (vn ++ vm) (exist _ o H) = nth vn (exist _ o H1).
Proof.
  intros A n m o H H1 vn vm.
  generalize dependent o.
  induction vn.
  - lia.
  - simpl; intros.
    destruct o; [ reflexivity | ].
    assert (o < n) as H2;[lia|].
    rewrite (IHvn _ _ H2). 
    repeat f_equal; apply proof_irrelevance.
Qed.

Theorem nth_app_r_lem : forall {n m o},
  o < n + m -> n <= o -> (o - n) < m.
Proof. lia. Qed.

Theorem nth_app_r : forall {A n m o}
  (H : o < n + m) (H1 : n <= o) (vn : t A n) (vm : t A m),
  nth (vn ++ vm) (exist _ o H) =
  nth vm (exist _ (o - n) (nth_app_r_lem H H1)).
Proof.
  intros A n m o H H1 vn vm.
  generalize dependent o.
  induction vn.
  - intros; simpl; simpl in H; f_equal.
    apply subset_eq_compat; lia.
  - simpl; intros.
    destruct o;[lia|].
    assert (n <= o) as H2;[lia|].
    rewrite (IHvn _ _ H2). 
    repeat f_equal; apply proof_irrelevance.
Qed.

Theorem vector_rev_append_nil_o : forall {A n}
  (v : t A n),
  rev_append [] v = v.
Proof.
  intros A n v.
  destruct v.
  - unfold rev_append.
    simpl.
    replace (Plus.plus_tail_plus 0 0) with (eq_refl 0);
    [ reflexivity | apply proof_irrelevance ].
  - unfold rev_append.
    simpl rev_append_tail.
    replace (Plus.plus_tail_plus 0 (S n))
       with (eq_refl (S n));
    [ reflexivity | apply proof_irrelevance ].
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
  replace (plus_n_O 0) with (eq_refl 0);
  [ reflexivity | apply proof_irrelevance ].
Qed.

Theorem vector_rev_sing_sing : forall {A} (h : A),
  rev [h] = [h].
Proof.
  intros A h.
  rewrite rev_coerce_unfold.
  replace (rev_append [h] []) with [h].
  { replace (plus_n_O 1) with (eq_refl 1);
    [ reflexivity | apply proof_irrelevance ]. }
  unfold rev_append.
  simpl. 
  replace (Plus.plus_tail_plus 1 0) with (eq_refl 1);
  [ reflexivity | apply proof_irrelevance ].
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
    rewrite (VectorSpec.eta v).
    rewrite (vector_nil_eq (tl v)).
    simpl; f_equal.
    unfold last_.
    replace (add_comm 0 1) with (eq_refl 1).
    2: { apply proof_irrelevance. }
    reflexivity.
  - rewrite (VectorSpec.eta v).
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

Theorem nth_rev_lem : forall {n i}, (i < n) -> (n - i - 1) < n.
  Proof. lia. Qed. 

Theorem nth_rev : forall {A n} (v : t A n) (i : fin n),
  nth (rev v) i =
  nth v (exist _ (n - proj1_sig i - 1) 
                 (nth_rev_lem (proj2_sig i))).
Proof.
  intros A n v.
  induction v using t_snoc_ind; intros [i lti].
  - lia.
  - rewrite rev_cons.
    rewrite cast_rew, nth_rew_l, fin_rew.
    destruct i; simpl.
    + assert (n <= n + 1 - 0 - 1) as H;[lia|].
      rewrite (nth_app_r _ H).
      assert (0 < 1) as H0;[lia|].
      transitivity (nth [h] (exist _ 0 H0)); [ reflexivity | ].
      f_equal; apply subset_eq_compat; lia.
    + assert (n + 1 - S i - 1 < n) as H;[lia|].
      rewrite (nth_app_l _ H).
      rewrite IHv.
      f_equal; apply subset_eq_compat; simpl; lia.
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

Theorem app_eq_l : forall {A n m} (v1 v2 : t A n) (v3 v4 : t A m),
  v1 ++ v3 = v2 ++ v4 -> v1 = v2.
Proof.
  intros A n m v1 v2 v3 v4.
  apply (fun I0 IC => 
          rect2 (fun P v1 v2 => v1 ++ v3 = v2 ++ v4 -> v1 = v2) 
        I0 IC v1 v2).
  - reflexivity.
  - clear v1 v2.
    intros n' v1 v2 IHv x1 x2.
    simpl; intro H.
    injection H; intros H0 H1; apply Eqdep.EqdepTheory.inj_pair2 in H0.
    rewrite H1; f_equal.
    apply IHv.
    exact H0.
Qed.

Theorem app_eq_r : forall {A n m} (v1 v2 : t A n) (v3 v4 : t A m),
  v1 ++ v3 = v2 ++ v4 -> v3 = v4.
Proof.
  intros A n m v1 v2 v3 v4.
  apply (fun I0 IC => 
          rect2 (fun P v1 v2 => v1 ++ v3 = v2 ++ v4 -> v3 = v4) 
        I0 IC v1 v2).
  - trivial.
  - clear v1 v2.
    intros n' v1 v2 IHv x1 x2.
    simpl; intro H.
    injection H; intros H0 H1; apply Eqdep.EqdepTheory.inj_pair2 in H0.
    apply IHv.
    exact H0.
Qed.

Theorem const_cons_snoc: forall {B} {b : B} {n},
  b :: const b n = cast (const b n ++ [b]) (add_comm n 1).
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
  VectorDef.rev (const b n) = const b n.
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
  rewrite eq, cast_id.
  apply const_split.
Qed.

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

Theorem Block_Load_Spec : forall {B memsz}
  (memN0 : memsz <> 0)
  (m : t B memsz)
  (idx blksz: fin memsz)
  (bid : fin (proj1_sig blksz)),
  nth (Block_Load m idx blksz) bid =
  nth m (exist _ ((proj1_sig bid + proj1_sig idx) mod memsz)
                 (PeanoNat.Nat.mod_upper_bound _ _ memN0)).
Proof.
  intros B memsz memN0 m [idx lidxm] [blksz lblkszm] [bid lbidbl].
  simpl; simpl in lbidbl.
  destruct (Block_Lem idx blksz memsz lidxm lblkszm) as 
    [[tl eq]|[blk2[blk1[idx2[eq1 [eq2 eq3]]]]]];
  destruct (splitat _ _) as [v12 v3] eqn:speq;
  apply VectorSpec.append_splitat in speq; 
  destruct (splitat _ _) as [v1 v2] eqn:speq2;
  apply VectorSpec.append_splitat in speq2;
  rewrite speq2 in speq; clear speq2.
  - assert (bid + idx < memsz) as H;[lia|].
    replace (fi' ((bid + idx) mod memsz))
       with (exist (fun x => x < memsz) (bid + idx) H).
    2: { apply subset_eq_compat; rewrite mod_small; lia. }
    assert (bid + idx < idx + blksz + tl) as H2;[lia|].
    transitivity (nth ((v1 ++ v2) ++ v3) (exist _ (bid + idx) H2)).
    2: { rewrite <- speq, nth_rew_l, fin_rew; 
         repeat f_equal; apply proof_irrelevance. }
    assert (bid + idx < idx + blksz) as H3;[lia|].
    rewrite (nth_app_l H2 H3).
    assert (idx <= bid + idx) as H4;[lia|].
    rewrite (nth_app_r H3 H4).
    f_equal; apply subset_eq_compat; lia.
  - unfold eq_rect_r.
    rewrite <- cast_rew in speq.
    rewrite cast_rew, rew_compose, nth_rew_l, fin_rew.
    assert ((bid + idx) mod memsz < blk2 + idx2 + blk1) as H0.
    { rewrite <- eq3; apply PeanoNat.Nat.mod_upper_bound; assumption. }
    transitivity (nth (cast m eq3) (exist _ ((bid + idx) mod memsz) H0)).
    2: { rewrite cast_rew, nth_rew_l, fin_rew. 
         repeat f_equal; apply proof_irrelevance. }
    rewrite speq.
    destruct (bid + idx <? memsz) eqn:bim.
    + rewrite ltb_lt in bim.
      assert (bid < blk1) as H1;[lia|].
      rewrite (nth_app_l _ H1).
      assert (blk2 + idx2 <= (bid + idx) mod memsz) as H2.
      { rewrite mod_small; lia. }
      rewrite (nth_app_r _ H2).
      f_equal; apply subset_eq_compat.
      rewrite mod_small; lia.
    + rewrite ltb_ge in bim.
      assert ((bid + idx) mod memsz = bid - blk1).
      { rewrite PeanoNat.Nat.mod_eq; try lia.
        replace (_ / _) with 1. { rewrite PeanoNat.Nat.mul_1_r; lia. }
        symmetry; apply div_bet_1; lia. }
      assert (bid - blk1 < blk2 + idx2 + blk1) as H1;[lia|].
      transitivity (nth ((v1 ++ v2) ++ v3)
                        (exist _ (bid - blk1) H1)).
      2: { f_equal; apply subset_eq_compat; lia. }
      assert (blk1 <= bid) as H2;[lia|].
      rewrite (nth_app_r _ H2).
      assert (bid - blk1 < blk2 + idx2) as H3;[lia|].
      rewrite (nth_app_l _ H3). 
      assert (bid - blk1 < blk2) as H4;[lia|].
      rewrite (nth_app_l _ H4).
      f_equal; apply subset_eq_compat; reflexivity.
Qed.

Definition Block_Store : forall {B memsz}
  (m : t B memsz)
  (idx blksz: fin memsz)
  (block : t B (proj1_sig blksz)),
  t B memsz.
  intros B memsz m [idx lidxm] [blksz lblkszm] block.
  destruct (Block_Lem _ _ _ lidxm lblkszm) as 
    [[tl eq]|[blk2[blk1[idx2[eq1 [eq2 eq3]]]]]].
  - rewrite eq in m; destruct (splitat _ m) as [m' m3];
    destruct (splitat _ m') as [m1 m2].
    rewrite eq.
    exact ((m1 ++ block) ++ m3).
  - rewrite eq3 in m; destruct (splitat _ m) as [m' m3];
    destruct (splitat _ m') as [m1 m2].
    rewrite <- eq1, add_comm in block.
    destruct (splitat _ block) as [block1 block2].
    rewrite eq3.
    (* Note: The overflow means block2 should go at
             the begining of memory, and block 1 at the end. *)
    exact ((block2 ++ m2) ++ block1).
Defined.

Theorem Block_Store_Spec : forall {B memsz}
  (memN0 : memsz <> 0)
  (m : t B memsz)
  (idx blksz: fin memsz)
  (block : t B (proj1_sig blksz))
  (bid : fin (proj1_sig blksz)),
  nth block bid =
  nth (Block_Store m idx blksz block) 
      (exist _ ((proj1_sig bid + proj1_sig idx) mod memsz)
                (PeanoNat.Nat.mod_upper_bound _ _ memN0)).
Proof.
  intros B memsz memN0 m [idx lidxm] [blksz lblkszm] block [bid lbidbl].
  simpl; simpl in lbidbl; simpl in block.
  unfold Block_Store.
  destruct (Block_Lem idx blksz memsz lidxm lblkszm) as 
    [[tl eq]|[blk2[blk1[idx2[eq1 [eq2 eq3]]]]]];
  simpl; destruct (splitat _ _) as [v12 v3] eqn:speq;
  apply VectorSpec.append_splitat in speq;
  destruct (splitat _ _) as [v1 v2] eqn:speq2;
  apply VectorSpec.append_splitat in speq2;
  rewrite speq2 in speq; clear speq2; simpl.
  - unfold eq_rect_r; rewrite nth_rew_l, fin_rew.
    assert (bid + idx < idx + blksz + tl) as H0;[lia|].
    transitivity (nth ((v1 ++ block) ++ v3)
                      (exist _ (bid + idx) H0)).
    2: { f_equal; apply subset_eq_compat;
         symmetry; apply mod_small; lia. }
    assert (bid + idx < idx + blksz) as H1;[lia|].
    rewrite (nth_app_l _ H1).
    assert (idx <= bid + idx) as H2;[lia|].
    rewrite (nth_app_r _ H2).
    f_equal; apply subset_eq_compat; lia.
  - repeat rewrite <- cast_rew.
    destruct (splitat _ _) as [block1 block2] eqn:spblk;
    apply VectorSpec.append_splitat in spblk;
    repeat unfold eq_rect_r; repeat rewrite rew_compose;
    rewrite nth_rew_l, fin_rew.
    unfold eq_rect_r in spblk.
    rewrite cast_rew, rew_compose in spblk.
    assert (bid < blk1 + blk2) as H0;[lia|].
    transitivity (nth (block1 ++ block2)
                      (exist _ bid H0)).
    { rewrite <- spblk, nth_rew_l, fin_rew;
      f_equal; apply subset_eq_compat; reflexivity. }
    clear spblk speq v12 v1 v3.
    destruct (bid + idx <? memsz) eqn:bim.
    + rewrite ltb_lt in bim.
      assert (bid + idx < blk2 + idx2 + blk1) as H1;[lia|].
      transitivity (nth ((block2 ++ v2) ++ block1)
                   (exist _ (bid + idx) H1)).
      2: { f_equal; apply subset_eq_compat; rewrite mod_small; lia. }
      assert (blk2 + idx2 <= bid + idx) as H2;[lia|].
      rewrite (nth_app_r _ H2).
      assert (bid < blk1) as H3;[lia|].
      rewrite (nth_app_l _ H3).
      f_equal; apply subset_eq_compat; lia.
    + rewrite ltb_ge in bim.
      assert ((bid + idx) mod memsz = bid - blk1).
      { rewrite PeanoNat.Nat.mod_eq; try lia.
        replace (_ / _) with 1. { rewrite PeanoNat.Nat.mul_1_r; lia. }
        symmetry; apply div_bet_1; lia. }
      assert (bid - blk1 < blk2 + idx2 + blk1) as H1;[lia|].
      transitivity (nth ((block2 ++ v2) ++ block1)
                        (exist _ (bid - blk1) H1)).
      2: { f_equal; apply subset_eq_compat; lia. }
      clear H.
      assert (blk1 <= bid) as H2;[lia|].
      rewrite (nth_app_r _ H2).
      assert (bid - blk1 < blk2 + idx2) as H3;[lia|].
      rewrite (nth_app_l _ H3). 
      assert (bid - blk1 < blk2) as H4;[lia|].
      rewrite (nth_app_l _ H4).
      f_equal; apply subset_eq_compat; reflexivity.
Qed.

(* Storing then loading a block at the same address gives the same block back. *)
Theorem Block_Store_Load : forall {B memsz}
    (m : t B memsz)
    (idx blksz: fin memsz)
    (block : t B (proj1_sig blksz)),
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
    (m : t B memsz)
    (idx blksz: fin memsz)
    (block block' : t B (proj1_sig blksz)),
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

(*If searching for a block in a memory after a different block was
  stored, we can ignore that storage. *)
Theorem Block_Store_Load_Irr : forall {B memsz}
    (m : t B memsz)
    (idx1 idx2 blksz: fin memsz)
    (block : t B (proj1_sig blksz)),
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
    remember (Plus.plus_reg_l _ _ _ _) as cool eqn:cool2; clear cool2.
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
    remember (Plus.plus_reg_l _ _ _ _) as cool2 eqn:cool3; clear cool3.
    rewrite speq4, cast_trans in speq; clear speq4 vA vB vC.
    repeat rewrite cast_app_l in speq.
    apply app_eq_r, app_eq_l in speq.
    symmetry; exact speq.
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
    (m : t B memsz)
    (idx1 idx2 blksz: fin memsz)
    (block block' : t B (proj1_sig blksz)),
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
      remember (plus_reg_r _ _ _ _) as cool0 eqn:cool1; clear cool1.
      rewrite speq in speq9; clear speq v39.
      shake_vect_eq speq2.
      remember (plus_reg_r _ _ _ _) as cool1 eqn:cool2; clear cool2.
      rewrite speq2 in speq9; clear speq2 v15.
      shake_vect_eq speq9.
      remember (plus_reg_r _ _ _ _) as cool2 eqn:cool3; clear cool3 cool0 cool1.
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
      remember (plus_reg_r _ _ _ _) as cool0 eqn:cool1; clear cool1.
      rewrite speq9 in speq3; clear speq9 v25'.
      shake_vect_eq speq2.
      remember (plus_reg_r _ _ _ _) as cool1 eqn:cool2; clear cool2.
      rewrite speq2 in speq3; clear speq2 v9.
      shake_vect_eq speq3.
      remember (plus_reg_r _ _ _ _) as cool2 eqn:cool3; clear cool3 cool1 cool0.
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
    remember (plus_reg_r _ _ _ _) as coolG eqn:fdsaf; clear fdsaf.
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
    clear coolG; remember (plus_reg_r _ _ _ _) as coolG eqn:fdsaf; clear fdsaf.
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
    clear coolG; remember (plus_reg_r _ _ _ _) as coolG eqn:fdsaf; clear fdsaf.
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
    remember (plus_reg_r _ _ _ _) as coolG eqn:fdsvd; clear fdsvd.
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
    clear coolG; remember (plus_reg_r _ _ _ _) as coolG eqn:fdsvd; clear fdsvd.
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
    clear coolG; remember (plus_reg_r _ _ _ _) as coolG eqn:fdsvd; clear fdsvd.
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
