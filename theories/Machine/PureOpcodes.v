From Coq Require Import
  Lia ZArith.Int Numbers.BinNums BinIntDef
  VectorDef VectorEq ProofIrrelevance.
Import BinInt.Z PeanoNat.Nat VectorNotations EqNotations.
From TinyRAM.Utils Require Import
  Vectors BitVectors Fin Arith.
From TinyRAM.Machine Require Import
  Parameters Words Memory.

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

  (* All opcodes which operate purely on state. *)

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
    - exact (bv_incr pcIncrement programCounter0).
    (* Registers *)
    - exact (replace registerValues0 ri res).
    (* Flag *)
    - exact (bv_eq res (Vector.const false _)).
    (* Memory *)
    - exact memory0.
  Defined.

  Theorem pureOp_and_correct (ri rj : regId) (A : Word) (m : MachineState) :
    nth (registerValues (pureOp_and ri rj A m)) ri = 
    bv_and (nth (registerValues m) rj) A.
  Proof. destruct m; simpl. rewrite nth_replace. reflexivity. Qed.

  Theorem pureOp_and_correct_flag (ri rj : regId) (A : Word) (m : MachineState) :
    conditionFlag (pureOp_and ri rj A m) = 
    (bitvector_nat_big (bv_and (nth (registerValues m) rj) A) =? 0).
  Proof. destruct m; simpl. apply bitvector_fin_big_0_0. Qed.

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
    - exact (bv_incr pcIncrement programCounter0).
    (* Registers *)
    - exact (replace registerValues0 ri res).
    (* Flag *)
    - exact (bv_eq res (Vector.const false _)).
    (* Memory *)
    - exact memory0.
  Defined.

  Theorem pureOp_or_correct (ri rj : regId) (A : Word) (m : MachineState) :
    nth (registerValues (pureOp_or ri rj A m)) ri = 
    bv_or (nth (registerValues m) rj) A.
  Proof. destruct m; simpl. rewrite nth_replace. reflexivity. Qed.

  Theorem pureOp_or_correct_flag (ri rj : regId) (A : Word) (m : MachineState) :
    conditionFlag (pureOp_or ri rj A m) = 
    (bitvector_nat_big (bv_or (nth (registerValues m) rj) A) =? 0).
  Proof. destruct m; simpl. apply bitvector_fin_big_0_0. Qed.

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
    - exact (bv_incr pcIncrement programCounter0).
    (* Registers *)
    - exact (replace registerValues0 ri res).
    (* Flag *)
    - exact (bv_eq res (Vector.const false _)).
    (* Memory *)
    - exact memory0.
  Defined.

  Theorem pureOp_xor_correct (ri rj : regId) (A : Word) (m : MachineState) :
    nth (registerValues (pureOp_xor ri rj A m)) ri = 
    bv_xor (nth (registerValues m) rj) A.
  Proof. destruct m; simpl. rewrite nth_replace. reflexivity. Qed.

  Theorem pureOp_xor_correct_flag (ri rj : regId) (A : Word) (m : MachineState) :
    conditionFlag (pureOp_xor ri rj A m) = 
    (bitvector_nat_big (bv_xor (nth (registerValues m) rj) A) =? 0).
  Proof. destruct m; simpl. apply bitvector_fin_big_0_0. Qed.

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
    - exact (bv_incr pcIncrement programCounter0).
    (* Registers *)
    - exact (replace registerValues0 ri res).
    (* Flag *)
    - exact (bv_eq res (Vector.const false _)).
    (* Memory *)
    - exact memory0.
  Defined.

  Theorem pureOp_not_correct (ri : regId) (A : Word) (m : MachineState) :
    nth (registerValues (pureOp_not ri A m)) ri = 
    bv_not A.
  Proof. destruct m; simpl. rewrite nth_replace. reflexivity. Qed.

  Theorem pureOp_not_correct_flag (ri : regId) (A : Word) (m : MachineState) :
    conditionFlag (pureOp_not ri A m) = 
    (bitvector_nat_big (bv_not A) =? 0).
  Proof. destruct m; simpl. apply bitvector_fin_big_0_0. Qed.

  (*"""
  The instruction add ri rj A stores in ri the W-bit string
  a_{W-1}...a_0 obtained as follows:
  a_{W-1}...a_0 are the W least significant bits of G = [rj]u - [A]u.
  Moreover, flag is set to GW , where GW is the MSB of G.
  """*)
  Definition pureOp_add (ri rj : regId) (A : Word) :
    MachineState -> MachineState.
    intro ms; destruct ms.
    apply (nth registerValues0) in rj.
    remember (bv_add rj A) as res eqn:resDef.
    split.
    (* PC *)
    - exact (bv_incr pcIncrement programCounter0).
    (* Registers *)
    - exact (replace registerValues0 ri (tl res)).
    (* Flag *)
    - exact (hd res).
    (* Memory *)
    - exact memory0.
  Defined.

  Theorem pureOp_add_correct (ri rj : regId) (A : Word) (m : MachineState) :
    conditionFlag (pureOp_add ri rj A m) :: 
    nth (registerValues (pureOp_add ri rj A m)) ri
    = nat_bitvector_big _ 
       (bitvector_nat_big (nth (registerValues m) rj)
        + bitvector_nat_big A).
  Proof.
    destruct m.
    unfold pureOp_add; rewrite bv_add_correct_1.
    simpl nth; simpl conditionFlag.
    rewrite nth_replace. reflexivity.
  Qed.

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
    - exact (bv_incr pcIncrement programCounter0).
    (* Registers *)
    - exact (replace registerValues0 ri (tl res)).
    (* Flag *)
    - exact (negb (hd res)).
    (* Memory *)
    - exact memory0.
  Defined.

  Theorem pureOp_sub_correct (ri rj : regId) (A : Word) (m : MachineState) :
    negb (conditionFlag (pureOp_sub ri rj A m)) :: 
    nth (registerValues (pureOp_sub ri rj A m)) ri
    = nat_bitvector_big _ 
       (bitvector_nat_big (nth (registerValues m) rj)
        + 2 ^ wordSize - bitvector_nat_big A).
  Proof.
    destruct m.
    unfold pureOp_sub; rewrite bv_sub_correct_1.
    simpl nth; simpl conditionFlag.
    rewrite nth_replace, Bool.negb_involutive.
    reflexivity.
  Qed.

  (*"""
  compute [rj]u * [A]u and store least significant bits of result in ri
 
  flag is set to 1 if [rj]u * [A]u ∈ U_W and to 0 otherwise.
  """*)
  Definition pureOp_mull (ri rj : regId) (A : Word) :
    MachineState -> MachineState.
    intro ms; destruct ms.
    apply (nth registerValues0) in rj.
    destruct (splitat wordSize (bv_mul rj A)) as [resh resl].
    split.
    (* PC *)
    - exact (bv_incr pcIncrement programCounter0).
    (* Registers *)
    - exact (replace registerValues0 ri resl).
    (* Flag *)
    - exact (bv_eq resh (const b0 _)).
    (* Memory *)
    - exact memory0.
  Defined.

  Theorem pureOp_mull_correct (ri rj : regId) (A : Word) (m : MachineState) :
    nth (registerValues (pureOp_mull ri rj A m)) ri
    = nat_bitvector_big _ 
       (bitvector_nat_big (nth (registerValues m) rj)
        * bitvector_nat_big A mod 2 ^ wordSize).
  Proof.
    destruct m.
    unfold pureOp_mull.
    rewrite bv_mullh_correct; simpl.
    rewrite nth_replace; reflexivity.
  Qed.

  Theorem pureOp_mull_correct_flag (ri rj : regId) (A : Word) (m : MachineState) :
    conditionFlag (pureOp_mull ri rj A m) = 
    ((bitvector_nat_big (nth (registerValues m) rj)
     * bitvector_nat_big A) <? 2 ^ wordSize).
  Proof. 
    destruct m; unfold pureOp_mull.
    destruct (splitat _ _) as [mh ml] eqn:sm; simpl.
    rewrite Bool.eq_iff_eq_true, bv_eq_equiv, ltb_lt, bv_mull_high_const0, sm.
    reflexivity.
  Qed.

  (*"""
  compute [rj]u * [A]u and store most significant bits of result in ri
 
  flag is set to 1 if [rj]u * [A]u ∈ U_W and to 0 otherwise.
  """*)
  Definition pureOp_umulh (ri rj : regId) (A : Word) :
    MachineState -> MachineState.
    intro ms; destruct ms.
    apply (nth registerValues0) in rj.
    destruct (splitat wordSize (bv_mul rj A)) as [resh resl].
    split.
    (* PC *)
    - exact (bv_incr pcIncrement programCounter0).
    (* Registers *)
    - exact (replace registerValues0 ri resh).
    (* Flag *)
    - exact (bv_eq resh (const b0 _)).
    (* Memory *)
    - exact memory0.
  Defined.

  Theorem pureOp_umulh_correct (ri rj : regId) (A : Word) (m : MachineState) :
    nth (registerValues (pureOp_umulh ri rj A m)) ri
    = nat_bitvector_big _ 
       (bitvector_nat_big (nth (registerValues m) rj)
        * bitvector_nat_big A / 2 ^ wordSize).
  Proof.
    destruct m.
    unfold pureOp_umulh.
    rewrite bv_mullh_correct; simpl.
    rewrite nth_replace; reflexivity.
  Qed.

  Theorem pureOp_umulh_correct_flag (ri rj : regId) (A : Word) (m : MachineState) :
    conditionFlag (pureOp_umulh ri rj A m) = 
    ((bitvector_nat_big (nth (registerValues m) rj)
     * bitvector_nat_big A) <? 2 ^ wordSize).
  Proof. 
    destruct m; unfold pureOp_umulh.
    destruct (splitat _ _) as [mh ml] eqn:sm; simpl.
    rewrite Bool.eq_iff_eq_true, bv_eq_equiv, ltb_lt, bv_mull_high_const0, sm.
    reflexivity.
  Qed.

  Theorem pureOp_mul_correct (ri rj : regId) (A : Word) (m : MachineState) :
    nth (registerValues (pureOp_umulh ri rj A m)) ri ++ 
    nth (registerValues (pureOp_mull ri rj A m)) ri
    = nat_bitvector_big _ 
       (bitvector_nat_big (nth (registerValues m) rj)
        * bitvector_nat_big A).
  Proof.
    destruct m.
    unfold pureOp_mull, pureOp_umulh.
    rewrite bv_mul_correct_1; simpl.
    destruct (splitat _ _) as [b1 b2] eqn:speq.
    apply VectorSpec.append_splitat in speq.
    simpl; repeat rewrite nth_replace.
    symmetry; exact speq.
  Qed.

  (*"""
  compute [rj]s * [A]s and store most significant bits of result in ri
  """*)
  Definition pureOp_smulh (ri rj : regId) (A : Word) :
    MachineState -> MachineState.
    intro ms; destruct ms.
    apply (nth registerValues0) in rj.
    unfold Word in rj, A.
    replace wordSize with (S (pred wordSize)) in rj, A.
    2: { apply succ_pred_pos; apply wordSizePos. }
    remember (twos_complement rj * twos_complement A)%Z as mjA.
    remember (twos_complement_inv (pred wordSize + pred wordSize) mjA) as sres.
    remember (hd sres) as sign.
    destruct (splitat _ (bv_abs sres)) as [resh resl].
    split.
    (* PC *)
    - exact (bv_incr pcIncrement programCounter0).
    (* Registers *)
    - apply (replace registerValues0 ri).
      unfold Word.
      replace wordSize with (S (pred wordSize)). 
      2: { apply succ_pred_pos; apply wordSizePos. } 
      exact (sign :: resh).
    (* Flag *)
    (*"""
    flag is set to 1 if [rj]s x [A]s ∈ S_W and to 0 otherwise.
    """ """
    S_W is the set of integers {-2^(W-1), ..., 0, 1, ..., 2^(W-1) - 1};
    """*)
    - exact (andb (- 2 ^ (of_nat wordSize - 1) <=? mjA) 
                  (mjA <? 2 ^ (of_nat wordSize - 1)))%Z.
    (* Memory *)
    - exact memory0.
  Defined.

  Definition wcast (v : Word) := 
    cast v (eq_sym (succ_pred_pos _ wordSizePos)).

  Theorem pureOp_smulh_correct_value (ri rj : regId) (A : Word) (m : MachineState) :
    (wcast (nth (registerValues m) rj)) <> b1 :: const b0 _ ->
    (wcast A) <> b1 :: const b0 _ ->
    tl (wcast (nth (registerValues (pureOp_smulh ri rj A m)) ri))
    = fst (splitat (pred wordSize)
          (nat_bitvector_big (pred wordSize + pred wordSize)
          (Z.abs_nat (twos_complement (wcast (nth (registerValues m) rj))
                      * twos_complement (wcast A))%Z))).
  Proof.
    destruct m; simpl.
    destruct (splitat _ _) as [absh absl] eqn:speq1;
    apply VectorSpec.append_splitat in speq1; simpl.
    destruct (splitat _ _) as [b3 b4] eqn:speq2;
    apply VectorSpec.append_splitat in speq2; simpl.
    rewrite nth_replace.
    rewrite <- cast_rew; unfold wcast.
    remember (eq_rec_r _ (nth registerValues0 rj) _) as regj.
    remember (eq_rec_r _ A _) as A'.
    rewrite cast_trans, cast_id.
    simpl. intros jmin Amin.
    rewrite twos_complement_nmin_1s in jmin, Amin.
    apply (app_eq_l _ _ absl b4).
    rewrite  <- speq1, <- speq2.
    rewrite bv_abs_correct.
    repeat f_equal.
    rewrite Heqregj, HeqA'; unfold wcast, eq_rec_r, eq_rec; repeat rewrite <- cast_rew.
    rewrite twos_complement_iso_2;
    try reflexivity; try apply twos_complement_max;
    rewrite Znat.Nat2Z.inj_add, BinInt.Z.pow_add_r; try lia.
    - apply le_opp_mul_mul;
      try apply twos_complement_max; try apply twos_complement_min.
    - apply lt_mul_mul; try apply twos_complement_max; assumption.
  Qed.

  Theorem pureOp_smulh_correct_sign (ri rj : regId) (A : Word) (m : MachineState) :
    (wcast (nth (registerValues m) rj)) <> b1 :: const b0 _ ->
    (wcast A) <> b1 :: const b0 _ ->
    hd (wcast (nth (registerValues (pureOp_smulh ri rj A m)) ri))
    = (twos_complement (wcast (nth (registerValues m) rj))
      * twos_complement (wcast A) <? 0)%Z.
  Proof.
    destruct m; simpl.
    destruct (splitat _ _) as [absh absl] eqn:speq1; simpl.
    rewrite nth_replace.
    unfold eq_rec_r, eq_rec.
    repeat rewrite <- cast_rew; unfold wcast.
    rewrite cast_trans, cast_id.
    simpl. intros jmin Amin.
    apply bv_smul_correct_sign; assumption.
  Qed.

  Theorem pureOp_smulh_correct_flag (ri rj : regId) (A : Word) (m : MachineState) :
    conditionFlag (pureOp_smulh ri rj A m) = 
    (andb (- 2 ^ (of_nat wordSize - 1) <=? 
          (twos_complement (wcast (nth (registerValues m) rj)) * twos_complement (wcast A)))
          (twos_complement (wcast (nth (registerValues m) rj)) * twos_complement (wcast A) <? 2 ^ (of_nat wordSize - 1)))%Z.
  Proof. 
    destruct m; unfold pureOp_smulh.
    destruct (splitat _ _) as [mh ml] eqn:sm; simpl.
    replace (eq_rec_r _ (nth registerValues0 rj) _)
       with (wcast (nth registerValues0 rj)).
    2: { unfold wcast; rewrite cast_rew; reflexivity. }
    replace (eq_rec_r _ A _) with (wcast A).
    2: { unfold wcast; rewrite cast_rew; reflexivity. }
    reflexivity.
  Qed.

  (*"""
  compute quotient of [rj]u/[A]u and store result in ri
  [flag:] [A]u = 0
  """*)
  Definition pureOp_udiv (ri rj : regId) (A : Word) :
    MachineState -> MachineState.
    intro ms; destruct ms.
    apply (nth registerValues0) in rj.
    remember (bv_udiv rj A) as res.
    split.
    (* PC *)
    - exact (bv_incr pcIncrement programCounter0).
    (* Registers *)
    - exact (replace registerValues0 ri res).
    (* Flag *)
    - exact (bv_eq A (const b0 _)).
    (* Memory *)
    - exact memory0.
  Defined.

  Theorem pureOp_udiv_correct (ri rj : regId) (A : Word) (m : MachineState) :
    nth (registerValues (pureOp_udiv ri rj A m)) ri
    = nat_bitvector_big _ 
       (bitvector_nat_big (nth (registerValues m) rj) / bitvector_nat_big A).
  Proof.
    destruct m.
    unfold pureOp_udiv; rewrite bv_udiv_correct_1.
    simpl nth; rewrite nth_replace. 
    reflexivity.
  Qed.

  Theorem pureOp_udiv_flag_correct (ri rj : regId) (A : Word) (m : MachineState) :
    conditionFlag (pureOp_udiv ri rj A m)
    = (bitvector_nat_big A =? 0).
  Proof.
    destruct m; simpl conditionFlag.
    rewrite Bool.eq_iff_eq_true, bv_eq_equiv, eqb_eq.
    apply bitvector_fin_big_0_const.
  Qed.

  (*"""
  compute remainder of [rj]u/[A]u and store result in ri
  [flag:] [A]u = 0
  """*)
  Definition pureOp_umod (ri rj : regId) (A : Word) :
    MachineState -> MachineState.
    intro ms; destruct ms.
    apply (nth registerValues0) in rj.
    remember (bv_umod rj A) as res.
    split.
    (* PC *)
    - exact (bv_incr pcIncrement programCounter0).
    (* Registers *)
    - exact (replace registerValues0 ri res).
    (* Flag *)
    - exact (bv_eq A (const b0 _)).
    (* Memory *)
    - exact memory0.
  Defined.

  Theorem pureOp_umod_correct (ri rj : regId) (A : Word) (m : MachineState) :
    nth (registerValues (pureOp_umod ri rj A m)) ri
    = nat_bitvector_big _ 
       (bitvector_nat_big (nth (registerValues m) rj) mod bitvector_nat_big A).
  Proof.
    destruct m.
    unfold pureOp_umod; rewrite bv_umod_correct_1.
    simpl nth; rewrite nth_replace. 
    reflexivity.
  Qed.

  Theorem pureOp_umod_flag_correct (ri rj : regId) (A : Word) (m : MachineState) :
    conditionFlag (pureOp_umod ri rj A m)
    = (bitvector_nat_big A =? 0).
  Proof.
    destruct m; simpl conditionFlag.
    rewrite Bool.eq_iff_eq_true, bv_eq_equiv, eqb_eq.
    apply bitvector_fin_big_0_const.
  Qed.

  (*"""
  shift [rj] by [A]u bits to the left and store result in ri
  [flag:] MSB of [rj]
  """*)
  Definition pureOp_shl (ri rj : regId) (A : Word) :
    MachineState -> MachineState.
    intro ms; destruct ms.
    apply (nth registerValues0) in rj.
    split.
    (* PC *)
    - exact (bv_incr pcIncrement programCounter0).
    (* Registers *)
    - apply bitvector_nat_big in A.
      remember (bv_shl A rj) as res.
      exact (replace registerValues0 ri res).
    (* Flag *)
    - exact (hd (wcast rj)).
    (* Memory *)
    - exact memory0.
  Defined.

  Theorem pureOp_shl_correct (ri rj : regId) (A : Word) 
                             (m : MachineState) (e : bitvector_nat_big A <= wordSize):
    nth (registerValues (pureOp_shl ri rj A m)) ri
    = cast (snd (splitat _ (cast (nth (registerValues m) rj)
                           (Minus.le_plus_minus _ _ e)))
            ++ const b0 _)
           (sub_add _ _ e).
  Proof.
    destruct m.
    unfold pureOp_shl.
    simpl nth; rewrite nth_replace.
    remember (nth _ rj) as regj.
    remember (cast regj _) as cregj.
    apply (cast_inj (Minus.le_plus_minus _ _ e)).
    transitivity (bv_shl (bitvector_nat_big A) cregj).
    { rewrite Heqcregj, (cast_f_swap (fun x v => bv_shl _ v)); reflexivity. }
    rewrite bv_shl_correct.
    vector_simp.
    f_equal; apply proof_irrelevance.
  Qed.

  Theorem pureOp_shl_flag_correct (ri rj : regId) (A : Word) (m : MachineState) :
    conditionFlag (pureOp_shl ri rj A m) = hd (wcast (nth (registerValues m) rj)).
  Proof. destruct m; reflexivity. Qed.

  (*"""
  shift [rj] by [A]u bits to the right and store result in ri
  [flag:] LSB of [rj]
  """*)
  Definition pureOp_shr (ri rj : regId) (A : Word) :
    MachineState -> MachineState.
    intro ms; destruct ms.
    apply (nth registerValues0) in rj.      
    split.
    (* PC *)
    - exact (bv_incr pcIncrement programCounter0).
    (* Registers *)
    - apply bitvector_nat_big in A.
      remember (bv_shr A rj) as res.
      exact (replace registerValues0 ri res).
    (* Flag *)
    - exact (last (wcast rj)).
    (* Memory *)
    - exact memory0.
  Defined.

  Theorem pureOp_shr_correct (ri rj : regId) (A : Word) 
                             (m : MachineState) (e : bitvector_nat_big A <= wordSize):
    nth (registerValues (pureOp_shr ri rj A m)) ri
    = cast (const b0 _ ++ fst (splitat _ (cast (nth (registerValues m) rj)
                              (eq_sym (sub_add _ _ e)))))
           (eq_sym (Minus.le_plus_minus _ _ e)).
  Proof.
    destruct m.
    unfold pureOp_shr.
    simpl nth; rewrite nth_replace.
    remember (nth _ rj) as regj.
    remember (cast regj _) as cregj.
    apply (cast_inj (eq_sym (sub_add _ _ e))).
    transitivity (bv_shr (bitvector_nat_big A) cregj).
    { rewrite Heqcregj, (cast_f_swap (fun x v => bv_shr _ v)); reflexivity. }
    rewrite bv_shr_correct.
    vector_simp.
    f_equal; apply proof_irrelevance.
  Qed.

  Theorem pureOp_shr_flag_correct (ri rj : regId) (A : Word) (m : MachineState) :
    conditionFlag (pureOp_shr ri rj A m) = last (wcast (nth (registerValues m) rj)).
  Proof. destruct m; reflexivity. Qed.

  (*"""
  “compare equal”
  [flag:] [ri] = [A]
  """*)
  Definition pureOp_cmpe (ri : regId) (A : Word) :
    MachineState -> MachineState.
    intro ms; destruct ms.
    apply (nth registerValues0) in ri.      
    split.
    (* PC *)
    - exact (bv_incr pcIncrement programCounter0).
    (* Registers *)
    - exact registerValues0.
    (* Flag *)
    - destruct (bitvector_fin_big ri) as [ri_N _].
      destruct (bitvector_fin_big A) as [A_N _].
      exact (ri_N =? A_N).
    (* Memory *)
    - exact memory0.
  Defined.

  (*"""
  “compare above”, unsigned
  [flag:] [ri]u > [A]u
  """*)
  Definition pureOp_cmpa (ri : regId) (A : Word) :
    MachineState -> MachineState.
    intro ms; destruct ms.
    apply (nth registerValues0) in ri.      
    split.
    (* PC *)
    - exact (bv_incr pcIncrement programCounter0).
    (* Registers *)
    - exact registerValues0.
    (* Flag *)
    - destruct (bitvector_fin_big ri) as [ri_N _].
      destruct (bitvector_fin_big A) as [A_N _].
      exact (A_N <? ri_N).
    (* Memory *)
    - exact memory0.
  Defined.

  (*"""
  “compare above or equal”, unsigned
  [flag:] [ri]u ≥ [A]u
  """*)
  Definition pureOp_cmpae (ri : regId) (A : Word) :
    MachineState -> MachineState.
    intro ms; destruct ms.
    apply (nth registerValues0) in ri.
    split.
    (* PC *)
    - exact (bv_incr pcIncrement programCounter0).
    (* Registers *)
    - exact registerValues0.
    (* Flag *)
    - destruct (bitvector_fin_big ri) as [ri_N _].
      destruct (bitvector_fin_big A) as [A_N _].
      exact (A_N <=? ri_N).
    (* Memory *)
    - exact memory0.
  Defined.

  (*"""
  “compare greater”, signed
  [flag:] [ri]s > [A]s
  """*)
  Definition pureOp_cmpg (ri : regId) (A : Word) :
    MachineState -> MachineState.
    intro ms; destruct ms.
    apply (nth registerValues0) in ri.
    unfold Word in A, ri; replace wordSize with (S (wordSize - 1)) in A, ri.
    2: { apply (Minus.le_plus_minus_r 1), Lt.lt_le_S, wordSizePos. }
    split.
    (* PC *)
    - exact (bv_incr pcIncrement programCounter0).
    (* Registers *)
    - exact registerValues0.
    (* Flag *)
    - destruct (bitvector_fin_big (tl ri)) as [ri_N _].
      destruct (bitvector_fin_big (tl A)) as [A_N _].
      destruct (hd ri) eqn:sri; destruct (hd A) eqn:sA.
      (* - > - *)
      + exact (ri_N <? A_N).
      (* - > + *)
      + exact false.
      (* + > - *)
      + exact true.
      (* + > + *)
      + exact (A_N <? ri_N).
    (* Memory *)
    - exact memory0.
  Defined.

  (*"""
  “compare greater or equal”, signed
  [flag:] [ri]s ≥ [A]s
  """*)
  Definition pureOp_cmpge (ri : regId) (A : Word) :
    MachineState -> MachineState.
    intro ms; destruct ms.
    apply (nth registerValues0) in ri.
    unfold Word in A, ri; replace wordSize with (S (wordSize - 1)) in A, ri.
    2: { apply (Minus.le_plus_minus_r 1), Lt.lt_le_S, wordSizePos. }
    split.
    (* PC *)
    - exact (bv_incr pcIncrement programCounter0).
    (* Registers *)
    - exact registerValues0.
    (* Flag *)
    - destruct (bitvector_fin_big (tl ri)) as [ri_N _].
      destruct (bitvector_fin_big (tl A)) as [A_N _].
      destruct (hd ri) eqn:sri; destruct (hd A) eqn:sA.
      (* - >= - *)
      + exact (ri_N <=? A_N).
      (* - >= + *)
      + exact false.
      (* + > - *)
      + exact true.
      (* + >= + *)
      + exact (A_N <=? ri_N).
    (* Memory *)
    - exact memory0.
  Defined.

  (*"""
  store [A] in ri
  """*)
  Definition pureOp_mov (ri : regId) (A : Word) :
    MachineState -> MachineState.
    intro ms; destruct ms.
    split.
    (* PC *)
    - exact (bv_incr pcIncrement programCounter0).
    (* Registers *)
    - exact (replace registerValues0 ri A).
    (* Flag *)
    - exact conditionFlag0.
    (* Memory *)
    - exact memory0.
  Defined.

  (*"""
  if flag = 1, store [A] in ri
  """*)
  Definition pureOp_cmov (ri : regId) (A : Word) :
    MachineState -> MachineState.
    intro ms; destruct ms.
    split.
    (* PC *)
    - exact (bv_incr pcIncrement programCounter0).
    (* Registers *)
    - destruct conditionFlag0.
      + exact (replace registerValues0 ri A). 
      + exact registerValues0.
    (* Flag *)
    - exact conditionFlag0.
    (* Memory *)
    - exact memory0.
  Defined.

  (*"""
  set pc to [A]
  """*)
  Definition pureOp_jmp (A : Word) :
    MachineState -> MachineState.
    intro ms; destruct ms.
    split.
    (* PC *)
    - exact A.
    (* Registers *)
    - exact registerValues0.
    (* Flag *)
    - exact conditionFlag0.
    (* Memory *)
    - exact memory0.
  Defined.


  (*"""
  if flag = 1, set pc to [A] (else increment pc as usual)
  """*)
  Definition pureOp_cjmp (A : Word) :
    MachineState -> MachineState.
    intro ms; destruct ms.
    split.
    (* PC *)
    - destruct conditionFlag0.
      + exact A.
      + exact (bv_incr pcIncrement programCounter0).
    (* Registers *)
    - exact registerValues0.
    (* Flag *)
    - exact conditionFlag0.
    (* Memory *)
    - exact memory0.
  Defined.


  (*"""
  if flag = 0, set pc to [A] (else increment pc as usual)
  """*)
  Definition pureOp_cnjmp (A : Word) :
    MachineState -> MachineState.
    intro ms; destruct ms.
    split.
    (* PC *)
    - destruct conditionFlag0.
      + exact (bv_incr pcIncrement programCounter0).
      + exact A.
    (* Registers *)
    - exact registerValues0.
    (* Flag *)
    - exact conditionFlag0.
    (* Memory *)
    - exact memory0.
  Defined.

  (*"""
  store the least-significant byte of [ri] at the [A]u-th byte in memory
  """*)
  Definition pureOp_store_b (A : Word) (ri : regId) :
    MachineState -> MachineState.
    intro ms; destruct ms; split.
    (* PC *)
    - exact (bv_incr pcIncrement programCounter0).
    (* Registers *)
    - exact registerValues0.
    (* Flag *)
    - exact conditionFlag0.
    (* Memory *)
    - apply (replace memory0).
      (*" at the [A]u-th byte "*)
      + apply bitvector_fin_big.
        exact A.
      (*" the least-significant byte of [ri] "*)
      + apply (fun x => nth x ri) in registerValues0 as regi.
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
    - exact (bv_incr pcIncrement programCounter0).
    (* Registers *)
    - apply (replace registerValues0 ri).
      apply BytesRegister.
      (*" (with zero-padding in front) "*)
      replace wordSizeEighth with (Nat.pred wordSizeEighth + 1).
      2: { assert (Nat.pred wordSizeEighth < wordSizeEighth).
          { apply Lt.lt_pred_n_n. apply wordSizeEighthPos. }
          lia. }
      apply Vector.append.
      (*" zero-padding "*)
      + apply (Vector.const zeroByte).
      (*" [A]u-th byte in memory "*)
      + apply (fun x => Vector.cons _ x _ (Vector.nil _)).
        apply (nth memory0).
        apply bitvector_fin_big.
        exact A.
    (* Flag *)
    - exact conditionFlag0.
    (* Memory *)
    - exact memory0.
  Defined.

  (*"""
  store [ri] at the word in memory that is aligned to the [A]w-th byte
  """*)
  Definition pureOp_store_w (ri : regId) (A : Word) :
    MachineState -> MachineState.
    intro ms; destruct ms; split.
    (* PC *)
    - exact (bv_incr pcIncrement programCounter0).
    (* Registers *)
    - exact registerValues0.
    (* Flag *)
    - exact conditionFlag0.
    (* Memory *)
    - apply (Memory_Register_Store_from_Reg memory0).
      (*" at the word in memory that is aligned to the [A]w-th byte "*)
      + exact A. 
      (* store [ri] *)
      + exact (nth registerValues0 ri).
  Defined.

  (*"""
  store into ri the word in memory that is aligned to the [A]w-th byte
  """*)
  Definition pureOp_load_w (ri : regId) (A : Word) :
    MachineState -> MachineState.
    intro ms; destruct ms; split.
    (* PC *)
    - exact (bv_incr pcIncrement programCounter0).
    (* Registers *)
    - apply (replace registerValues0 ri).
      apply (Memory_Register_Load_from_Reg memory0).
      exact A.
    (* Flag *)
    - exact conditionFlag0. 
    (* Memory *)
    - exact memory0.
  Defined.

End TinyRAMState.


