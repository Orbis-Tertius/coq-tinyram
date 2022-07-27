From Coq Require Import
    Lia
    Psatz
    Strings.String
    List
    Program.Basics
    Morphisms
    ZArith
    Setoid
    RelationClasses
    VectorDef VectorEq ProofIrrelevance.

From ITree Require Import
    ITree
    ITreeFacts
    Basics.CategorySub
    Basics.HeterogeneousRelations
    Events.State
    Events.StateFacts
    Eq.EqAxiom.

Import ITreeNotations.

From ExtLib Require Import
    Core.RelDec
    Structures.Monad.

Import Monads MonadNotation BinInt.Z PeanoNat.Nat VectorNotations EqNotations.

From TinyRAM.Utils Require Import
  Vectors BitVectors Fin Arith.

From TinyRAM.Machine Require Import
  Parameters Handlers.

Module TinyRAMInstThm (Params : TinyRAMParameters).
  Module TRHan := TinyRAMHandlers Params.
  Import TRHan.
  Export TRHan.

  Section with_event.
    Context {E': Type -> Type}.
    Notation E := (MachineE +' E').

    Local Open Scope monad_scope.
    (* All opcodes which operate purely on state. *)

    (*"""
    compute bitwise AND of [rj] and [A] and store result in ri
    [flag:] result is 0W
    """*)
    Definition pureOp_and (ri rj : regId) (A : Word) :
      MachineState -> MachineState.
      intro ms; destruct ms.
      apply (nth registers0) in rj.
      remember (bv_and rj A) as res eqn:resDef.
      split.
      (* PC *)
      - exact (bv_succ programCounter0).
      (* Registers *)
      - exact (replace registers0 ri res).
      (* Flag *)
      - exact (bv_eq res (const false _)).
      (* Memory *)
      - exact memory0.
      (* Main Tape *)
      - exact tapeMain0.
      (* Aux Tape *)
      - exact tapeAux0.
      (* Program *)
      - exact program0.
    Defined.

    Theorem pureOp_and_correct (ri rj : regId) (A : Word) (m : MachineState) :
      nth (registers (pureOp_and ri rj A m)) ri = 
      bv_and (nth (registers m) rj) A.
    Proof. destruct m; simpl. rewrite nth_replace. reflexivity. Qed.

    Theorem pureOp_and_correct_flag (ri rj : regId) (A : Word) (m : MachineState) :
      flag (pureOp_and ri rj A m) = 
      (bitvector_nat_big (bv_and (nth (registers m) rj) A) =? 0).
    Proof. destruct m; simpl. apply bitvector_fin_big_0_0. Qed.

    Theorem pureOp_and_interp_imm {S} (k: itree E S) (ri rj : regId) 
                                  (A : Word) (m : MachineState) :
    interp_machine (denote_instruction (andI ri rj, inl A) ;; k) m
    ≈ interp_machine k (pureOp_and ri rj A m).
    Proof. tau_steps; destruct m; reflexivity. Qed.

    Theorem pureOp_and_interp_reg {S} (k: itree E S) (ri rj A : regId)
                                  (m : MachineState) :
    interp_machine (denote_instruction (andI ri rj, inr A) ;; k) m
    ≈ interp_machine k (pureOp_and ri rj (nth (registers m) A) m).
    Proof. tau_steps; destruct m; reflexivity. Qed.

    (*"""
    compute bitwise OR of [rj] and [A] and store result in ri
    [flag:] result is 0W
    """*)
    Definition pureOp_or (ri rj : regId) (A : Word) :
      MachineState -> MachineState.
      intro ms; destruct ms.
      apply (nth registers0) in rj.
      remember (bv_or rj A) as res eqn:resDef.
      split.
      (* PC *)
      - exact (bv_succ programCounter0).
      (* Registers *)
      - exact (replace registers0 ri res).
      (* Flag *)
      - exact (bv_eq res (const false _)).
      (* Memory *)
      - exact memory0.
      (* Main Tape *)
      - exact tapeMain0.
      (* Aux Tape *)
      - exact tapeAux0.
      (* Program *)
      - exact program0.
    Defined.

    Theorem pureOp_or_correct (ri rj : regId) (A : Word) (m : MachineState) :
      nth (registers (pureOp_or ri rj A m)) ri = 
      bv_or (nth (registers m) rj) A.
    Proof. destruct m; simpl. rewrite nth_replace. reflexivity. Qed.

    Theorem pureOp_or_correct_flag (ri rj : regId) (A : Word) (m : MachineState) :
      flag (pureOp_or ri rj A m) = 
      (bitvector_nat_big (bv_or (nth (registers m) rj) A) =? 0).
    Proof. destruct m; simpl. apply bitvector_fin_big_0_0. Qed.

    Theorem pureOp_or_interp_imm {S} (k: itree E S) (ri rj : regId) 
                                  (A : Word) (m : MachineState) :
    interp_machine (denote_instruction (orI ri rj, inl A) ;; k) m
    ≈ interp_machine k (pureOp_or ri rj A m).
    Proof. tau_steps; destruct m; reflexivity. Qed.

    Theorem pureOp_or_interp_reg {S} (k: itree E S) (ri rj A : regId)
                                  (m : MachineState) :
    interp_machine (denote_instruction (orI ri rj, inr A) ;; k) m
    ≈ interp_machine k (pureOp_or ri rj (nth (registers m) A) m).
    Proof. tau_steps; destruct m; reflexivity. Qed.
  
    (*"""
    compute bitwise XOR of [rj] and [A] and store result in ri
    [flag:] result is 0W
    """*)
    Definition pureOp_xor (ri rj : regId) (A : Word) :
      MachineState -> MachineState.
      intro ms; destruct ms.
      apply (nth registers0) in rj.
      remember (bv_xor rj A) as res eqn:resDef.
      split.
      (* PC *)
      - exact (bv_succ programCounter0).
      (* Registers *)
      - exact (replace registers0 ri res).
      (* Flag *)
      - exact (bv_eq res (const false _)).
      (* Memory *)
      - exact memory0.
      (* Main Tape *)
      - exact tapeMain0.
      (* Aux Tape *)
      - exact tapeAux0.
      (* Program *)
      - exact program0.
    Defined.

    Theorem pureOp_xor_correct (ri rj : regId) (A : Word) (m : MachineState) :
      nth (registers (pureOp_xor ri rj A m)) ri = 
      bv_xor (nth (registers m) rj) A.
    Proof. destruct m; simpl. rewrite nth_replace. reflexivity. Qed.

    Theorem pureOp_xor_correct_flag (ri rj : regId) (A : Word) (m : MachineState) :
      flag (pureOp_xor ri rj A m) = 
      (bitvector_nat_big (bv_xor (nth (registers m) rj) A) =? 0).
    Proof. destruct m; simpl. apply bitvector_fin_big_0_0. Qed.

    Theorem pureOp_xor_interp_imm {S} (k: itree E S) (ri rj : regId) 
                                  (A : Word) (m : MachineState) :
    interp_machine (denote_instruction (xorI ri rj, inl A) ;; k) m
    ≈ interp_machine k (pureOp_xor ri rj A m).
    Proof. tau_steps; destruct m; reflexivity. Qed.

    Theorem pureOp_xor_interp_reg {S} (k: itree E S) (ri rj A : regId)
                                  (m : MachineState) :
    interp_machine (denote_instruction (xorI ri rj, inr A) ;; k) m
    ≈ interp_machine k (pureOp_xor ri rj (nth (registers m) A) m).
    Proof. tau_steps; destruct m; reflexivity. Qed.
  
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
      - exact (bv_succ programCounter0).
      (* Registers *)
      - exact (replace registers0 ri res).
      (* Flag *)
      - exact (bv_eq res (const false _)).
      (* Memory *)
      - exact memory0.
      (* Main Tape *)
      - exact tapeMain0.
      (* Aux Tape *)
      - exact tapeAux0.
      (* Program *)
      - exact program0.
    Defined.

    Theorem pureOp_not_correct (ri : regId) (A : Word) (m : MachineState) :
      nth (registers (pureOp_not ri A m)) ri = 
      bv_not A.
    Proof. destruct m; simpl. rewrite nth_replace. reflexivity. Qed.

    Theorem pureOp_not_correct_flag (ri : regId) (A : Word) (m : MachineState) :
      flag (pureOp_not ri A m) = 
      (bitvector_nat_big (bv_not A) =? 0).
    Proof. destruct m; simpl. apply bitvector_fin_big_0_0. Qed.

    Theorem pureOp_not_interp_imm {S} (k: itree E S) (ri : regId) 
                                  (A : Word) (m : MachineState) :
    interp_machine (denote_instruction (notI ri, inl A) ;; k) m
    ≈ interp_machine k (pureOp_not ri A m).
    Proof. tau_steps; destruct m; reflexivity. Qed.

    Theorem pureOp_not_interp_reg {S} (k: itree E S) (ri A : regId)
                                  (m : MachineState) :
    interp_machine (denote_instruction (notI ri, inr A) ;; k) m
    ≈ interp_machine k (pureOp_not ri (nth (registers m) A) m).
    Proof. tau_steps; destruct m; reflexivity. Qed.
  
    (*"""
    The instruction add ri rj A stores in ri the W-bit string
    a_{W-1}...a_0 obtained as follows:
    a_{W-1}...a_0 are the W least significant bits of G = [rj]u + [A]u.
    Moreover, flag is set to GW , where GW is the MSB of G.
    """*)
    Definition pureOp_add (ri rj : regId) (A : Word) :
      MachineState -> MachineState.
      intro ms; destruct ms.
      apply (nth registers0) in rj.
      remember (bv_add rj A) as res eqn:resDef.
      split.
      (* PC *)
      - exact (bv_succ programCounter0).
      (* Registers *)
      - exact (replace registers0 ri (tl res)).
      (* Flag *)
      - exact (hd res).
      (* Memory *)
      - exact memory0.
      (* Main Tape *)
      - exact tapeMain0.
      (* Aux Tape *)
      - exact tapeAux0.
      (* Program *)
      - exact program0.
    Defined.

    Theorem pureOp_add_correct (ri rj : regId) (A : Word) (m : MachineState) :
      flag (pureOp_add ri rj A m) :: 
      nth (registers (pureOp_add ri rj A m)) ri
      = nat_bitvector_big _ 
        (bitvector_nat_big (nth (registers m) rj)
          + bitvector_nat_big A).
    Proof.
      destruct m.
      unfold pureOp_add; rewrite bv_add_correct_1.
      simpl nth; simpl flag.
      rewrite nth_replace. reflexivity.
    Qed.

    Theorem pureOp_add_interp_imm {S} (k: itree E S) (ri rj : regId) 
                                  (A : Word) (m : MachineState) :
    interp_machine (denote_instruction (addI ri rj, inl A) ;; k) m
    ≈ interp_machine k (pureOp_add ri rj A m).
    Proof. tau_steps; destruct m; reflexivity. Qed.

    Theorem pureOp_add_interp_reg {S} (k: itree E S) (ri rj A : regId)
                                  (m : MachineState) :
    interp_machine (denote_instruction (addI ri rj, inr A) ;; k) m
    ≈ interp_machine k (pureOp_add ri rj (nth (registers m) A) m).
    Proof. tau_steps; destruct m; reflexivity. Qed.

    (*"""
    compute [rj]u - [A]u and store result in ri
    
    flag is set to 1 - GW , where GW is the MSB of G [res].
    """*)
    Definition pureOp_sub (ri rj : regId) (A : Word) :
      MachineState -> MachineState.
      intro ms; destruct ms.
      apply (nth registers0) in rj.
      remember (bv_sub rj A) as res.
      split.
      (* PC *)
      - exact (bv_succ programCounter0).
      (* Registers *)
      - exact (replace registers0 ri (tl res)).
      (* Flag *)
      - exact (negb (hd res)).
      (* Memory *)
      - exact memory0.
      (* Main Tape *)
      - exact tapeMain0.
      (* Aux Tape *)
      - exact tapeAux0.
      (* Program *)
      - exact program0.
    Defined.

    Theorem pureOp_sub_correct (ri rj : regId) (A : Word) (m : MachineState) :
      negb (flag (pureOp_sub ri rj A m)) :: 
      nth (registers (pureOp_sub ri rj A m)) ri
      = nat_bitvector_big _ 
        (bitvector_nat_big (nth (registers m) rj)
          + 2 ^ wordSize - bitvector_nat_big A).
    Proof.
      destruct m.
      unfold pureOp_sub; rewrite bv_sub_correct_1.
      simpl nth; simpl flag.
      rewrite nth_replace, Bool.negb_involutive.
      reflexivity.
    Qed.

    Theorem pureOp_sub_interp_imm {S} (k: itree E S) (ri rj : regId) 
                                  (A : Word) (m : MachineState) :
    interp_machine (denote_instruction (subI ri rj, inl A) ;; k) m
    ≈ interp_machine k (pureOp_sub ri rj A m).
    Proof. tau_steps; destruct m; reflexivity. Qed.

    Theorem pureOp_sub_interp_reg {S} (k: itree E S) (ri rj A : regId)
                                  (m : MachineState) :
    interp_machine (denote_instruction (subI ri rj, inr A) ;; k) m
    ≈ interp_machine k (pureOp_sub ri rj (nth (registers m) A) m).
    Proof. tau_steps; destruct m; reflexivity. Qed.

    (*"""
    compute [rj]u * [A]u and store least significant bits of result in ri
  
    flag is set to 1 if [rj]u * [A]u ∉ U_W and to 0 otherwise.
    """*)
    Definition pureOp_mull (ri rj : regId) (A : Word) :
      MachineState -> MachineState.
      intro ms; destruct ms.
      apply (nth registers0) in rj.
      destruct (splitat wordSize (bv_mul rj A)) as [resh resl].
      split.
      (* PC *)
      - exact (bv_succ programCounter0).
      (* Registers *)
      - exact (replace registers0 ri resl).
      (* Flag *)
      - exact (negb (bv_eq resh (const b0 _))).
      (* Memory *)
      - exact memory0.
      (* Main Tape *)
      - exact tapeMain0.
      (* Aux Tape *)
      - exact tapeAux0.
      (* Program *)
      - exact program0.
    Defined.

    Theorem pureOp_mull_correct (ri rj : regId) (A : Word) (m : MachineState) :
      nth (registers (pureOp_mull ri rj A m)) ri
      = nat_bitvector_big _ 
        (bitvector_nat_big (nth (registers m) rj)
          * bitvector_nat_big A mod 2 ^ wordSize).
    Proof.
      destruct m.
      unfold pureOp_mull.
      rewrite bv_mullh_correct; simpl.
      rewrite nth_replace; reflexivity.
    Qed.

    Theorem pureOp_mull_correct_flag (ri rj : regId) (A : Word) (m : MachineState) :
      flag (pureOp_mull ri rj A m) = 
      negb ((bitvector_nat_big (nth (registers m) rj)
            * bitvector_nat_big A) <? 2 ^ wordSize).
    Proof. 
      destruct m; unfold pureOp_mull.
      destruct (splitat _ _) as [mh ml] eqn:sm; simpl.
      f_equal.
      rewrite Bool.eq_iff_eq_true, bv_eq_equiv, ltb_lt, bv_mull_high_const0, sm.
      reflexivity.
    Qed.

    Theorem pureOp_mull_interp_imm {S} (k: itree E S) (ri rj : regId) 
                                  (A : Word) (m : MachineState) :
    interp_machine (denote_instruction (mullI ri rj, inl A) ;; k) m
    ≈ interp_machine k (pureOp_mull ri rj A m).
    Proof. tau_steps; destruct m.
          cbn; destruct (splitat _ _); reflexivity.
    Qed.

    Theorem pureOp_mull_interp_reg {S} (k: itree E S) (ri rj A : regId)
                                  (m : MachineState) :
    interp_machine (denote_instruction (mullI ri rj, inr A) ;; k) m
    ≈ interp_machine k (pureOp_mull ri rj (nth (registers m) A) m).
    Proof. tau_steps; destruct m.
          cbn; destruct (splitat _ _); reflexivity.
    Qed.

    (*"""
    compute [rj]u * [A]u and store most significant bits of result in ri
  
    flag is set to 1 if [rj]u * [A]u ∉ U_W and to 0 otherwise.
    """*)
    Definition pureOp_umulh (ri rj : regId) (A : Word) :
      MachineState -> MachineState.
      intro ms; destruct ms.
      apply (nth registers0) in rj.
      destruct (splitat wordSize (bv_mul rj A)) as [resh resl].
      split.
      (* PC *)
      - exact (bv_succ programCounter0).
      (* Registers *)
      - exact (replace registers0 ri resh).
      (* Flag *)
      - exact (negb (bv_eq resh (const b0 _))).
      (* Memory *)
      - exact memory0.
      (* Main Tape *)
      - exact tapeMain0.
      (* Aux Tape *)
      - exact tapeAux0.
      (* Program *)
      - exact program0.
    Defined.

    Theorem pureOp_umulh_correct (ri rj : regId) (A : Word) (m : MachineState) :
      nth (registers (pureOp_umulh ri rj A m)) ri
      = nat_bitvector_big _ 
        (bitvector_nat_big (nth (registers m) rj)
          * bitvector_nat_big A / 2 ^ wordSize).
    Proof.
      destruct m.
      unfold pureOp_umulh.
      rewrite bv_mullh_correct; simpl.
      rewrite nth_replace; reflexivity.
    Qed.

    Theorem pureOp_umulh_correct_flag (ri rj : regId) (A : Word) (m : MachineState) :
      flag (pureOp_umulh ri rj A m) = 
      negb ((bitvector_nat_big (nth (registers m) rj)
            * bitvector_nat_big A) <? 2 ^ wordSize).
    Proof. 
      destruct m; unfold pureOp_umulh.
      destruct (splitat _ _) as [mh ml] eqn:sm; simpl.
      f_equal.
      rewrite Bool.eq_iff_eq_true, bv_eq_equiv, ltb_lt, bv_mull_high_const0, sm.
      reflexivity.
    Qed.

    Theorem pureOp_umulh_interp_imm {S} (k: itree E S) (ri rj : regId) 
                                  (A : Word) (m : MachineState) :
    interp_machine (denote_instruction (umulhI ri rj, inl A) ;; k) m
    ≈ interp_machine k (pureOp_umulh ri rj A m).
    Proof. tau_steps; destruct m.
          cbn; destruct (splitat _ _); reflexivity.
    Qed.

    Theorem pureOp_umulh_interp_reg {S} (k: itree E S) (ri rj A : regId)
                                  (m : MachineState) :
    interp_machine (denote_instruction (umulhI ri rj, inr A) ;; k) m
    ≈ interp_machine k (pureOp_umulh ri rj (nth (registers m) A) m).
    Proof. tau_steps; destruct m.
          cbn; destruct (splitat _ _); reflexivity.
    Qed.

    Theorem pureOp_mul_correct (ri rj : regId) (A : Word) (m : MachineState) :
      nth (registers (pureOp_umulh ri rj A m)) ri ++ 
      nth (registers (pureOp_mull ri rj A m)) ri
      = nat_bitvector_big _ 
        (bitvector_nat_big (nth (registers m) rj)
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
      apply (nth registers0) in rj.
      apply wcast in rj, A.
      remember (twos_complement rj * twos_complement A)%Z as mjA.
      remember (twos_complement_inv (pred wordSize + pred wordSize) mjA) as sres.
      remember (hd sres) as sign.
      destruct (splitat _ (bv_abs sres)) as [resh resl].
      split.
      (* PC *)
      - exact (bv_succ programCounter0).
      (* Registers *)
      - apply (replace registers0 ri).
        exact (wuncast (sign :: resh)).
      (* Flag *)
      (*"""
      flag is set to 1 if [rj]s x [A]s ∉ S_W and to 0 otherwise.
      """ """
      S_W is the set of integers {-2^(W-1), ..., 0, 1, ..., 2^(W-1) - 1};
      """*)
      - exact (negb (andb (- 2 ^ (of_nat wordSize - 1) <=? mjA) 
                    (mjA <? 2 ^ (of_nat wordSize - 1)))%Z).
      (* Memory *)
      - exact memory0.
      (* Main Tape *)
      - exact tapeMain0.
      (* Aux Tape *)
      - exact tapeAux0.
      (* Program *)
      - exact program0.
    Defined.

    Theorem pureOp_smulh_correct_value (ri rj : regId) (A : Word) (m : MachineState) :
      (wcast (nth (registers m) rj)) <> b1 :: const b0 _ ->
      (wcast A) <> b1 :: const b0 _ ->
      tl (wcast (nth (registers (pureOp_smulh ri rj A m)) ri))
      = nat_bitvector_big (pred wordSize) ((Z.abs_nat 
          (twos_complement (wcast (nth (registers m) rj)) *
          twos_complement (wcast A))%Z) / 2 ^ pred wordSize).
    Proof.
      destruct m; simpl.
      destruct (splitat _ _) as [absh absl] eqn:speq1.
      simpl; rewrite nth_replace.
      unfold wcast, wuncast, eq_rec_r, eq_rec.
      repeat rewrite <- cast_rew.
      rewrite cast_trans, cast_id.
      change (cast (nth registers0 rj) _) with (wcast (nth registers0 rj)).
      change (cast A _) with (wcast A).
      remember (wcast (nth registers0 rj)) as wj.
      remember (wcast A) as wA.
      intros jmin Amin; rewrite twos_complement_nmin_1s in jmin, Amin.
      simpl tl.
      assert (twos_complement wj < 2 ^ of_nat (pred wordSize))%Z.
      { apply twos_complement_max. }
      assert (twos_complement wA < 2 ^ of_nat (pred wordSize))%Z.
      { apply twos_complement_max. }
      assert (bitvector_nat_big absh < 2 ^ pred wordSize).
      { apply bitvector_nat_big_lt_2pow. }
      assert (bitvector_nat_big absl < 2 ^ pred wordSize).
      { apply bitvector_nat_big_lt_2pow. }
      apply VectorSpec.append_splitat in speq1.
      rewrite bv_abs_correct, <- (bitvector_nat_big_inv (absh ++ absl)), 
              bitvector_nat_big_app, twos_complement_iso_2,
              nat_bitvector_big_inj in speq1.
      rewrite speq1; clear speq1.
      rewrite PeanoNat.Nat.div_add_l, div_small, add_0_r.
      symmetry; apply bitvector_nat_big_inv.
      apply bitvector_nat_big_lt_2pow.
      apply pow_nonzero; lia.
      rewrite Znat.Zabs2Nat.inj_mul, pow_add_r.
      replace (2 ^ pred wordSize) with (to_nat (2 ^ of_nat (pred wordSize))).
      apply mul_lt_mono_nonneg; try lia.
      rewrite Z2_inj_pow, Znat.Nat2Z.id; f_equal; lia.
      apply (le_lt_trans _ ((2 ^ pred wordSize - 1) * 2 ^ pred wordSize + (2 ^ pred wordSize - 1))).
      apply Plus.plus_le_compat; try lia.
      apply mul_le_mono_r; lia.
      assert (0 < 2 ^ pred wordSize); [ apply zero2pow | ].
      rewrite pow_add_r, mul_sub_distr_r, add_sub_assoc, mul_1_l, sub_add; try lia.
      rewrite <- (mul_1_l (2 ^ _)) at 1; apply mul_le_mono_nonneg; lia.
      rewrite Znat.Nat2Z.inj_add, BinInt.Z.pow_add_r; try lia.
      apply le_opp_mul_mul; lia.
      rewrite Znat.Nat2Z.inj_add, BinInt.Z.pow_add_r; try lia.
      apply lt_mul_mul; lia.
      rewrite twos_complement_iso_2.
      rewrite Znat.Nat2Z.inj_add, BinInt.Z.pow_add_r; try lia.
      apply lt_opp_mul_mul; lia.
      rewrite Znat.Nat2Z.inj_add, BinInt.Z.pow_add_r; try lia.
      apply le_opp_mul_mul; lia.
      rewrite Znat.Nat2Z.inj_add, BinInt.Z.pow_add_r; try lia.
      apply lt_mul_mul; lia.
    Qed.

    Theorem pureOp_smulh_correct_sign (ri rj : regId) (A : Word) (m : MachineState) :
      (wcast (nth (registers m) rj)) <> b1 :: const b0 _ ->
      (wcast A) <> b1 :: const b0 _ ->
      hd (wcast (nth (registers (pureOp_smulh ri rj A m)) ri))
      = (twos_complement (wcast (nth (registers m) rj))
        * twos_complement (wcast A) <? 0)%Z.
    Proof.
      destruct m; simpl.
      destruct (splitat _ _) as [absh absl] eqn:speq1; simpl.
      rewrite nth_replace.
      unfold eq_rec_r, eq_rec.
      repeat rewrite <- cast_rew; unfold wcast, wuncast.
      rewrite cast_trans, cast_id.
      simpl. intros jmin Amin.
      apply bv_smul_correct_sign; assumption.
    Qed.

    Theorem pureOp_smulh_correct_flag (ri rj : regId) (A : Word) (m : MachineState) :
      flag (pureOp_smulh ri rj A m) = 
      negb (andb (- 2 ^ (of_nat wordSize - 1) <=? 
                 (twos_complement (wcast (nth (registers m) rj)) * twos_complement (wcast A)))
                 (twos_complement (wcast (nth (registers m) rj)) * twos_complement (wcast A) <? 2 ^ (of_nat wordSize - 1)))%Z.
    Proof. 
      destruct m; unfold pureOp_smulh.
      destruct (splitat _ _) as [mh ml] eqn:sm; simpl.
      reflexivity.
    Qed.

    Theorem pureOp_smulh_interp_imm {S} (k: itree E S) (ri rj : regId) 
                                  (A : Word) (m : MachineState) :
    interp_machine (denote_instruction (smulhI ri rj, inl A) ;; k) m
    ≈ interp_machine k (pureOp_smulh ri rj A m).
    Proof. tau_steps; destruct m.
          cbn; destruct (splitat _ _); reflexivity.
    Qed.

    Theorem pureOp_smulh_interp_reg {S} (k: itree E S) (ri rj A : regId)
                                  (m : MachineState) :
    interp_machine (denote_instruction (smulhI ri rj, inr A) ;; k) m
    ≈ interp_machine k (pureOp_smulh ri rj (nth (registers m) A) m).
    Proof. tau_steps; destruct m.
          cbn; destruct (splitat _ _); reflexivity.
    Qed.

    (*"""
    compute quotient of [rj]u/[A]u and store result in ri
    [flag:] [A]u = 0
    """*)
    Definition pureOp_udiv (ri rj : regId) (A : Word) :
      MachineState -> MachineState.
      intro ms; destruct ms.
      apply (nth registers0) in rj.
      remember (bv_udiv rj A) as res.
      split.
      (* PC *)
      - exact (bv_succ programCounter0).
      (* Registers *)
      - exact (replace registers0 ri res).
      (* Flag *)
      - exact (bv_eq A (const b0 _)).
      (* Memory *)
      - exact memory0.
      (* Main Tape *)
      - exact tapeMain0.
      (* Aux Tape *)
      - exact tapeAux0.
      (* Program *)
      - exact program0.
    Defined.

    Theorem pureOp_udiv_correct (ri rj : regId) (A : Word) (m : MachineState) :
      bitvector_nat_big A > 0 ->
      nth (registers (pureOp_udiv ri rj A m)) ri
      = nat_bitvector_big _ 
        (bitvector_nat_big (nth (registers m) rj) / bitvector_nat_big A).
    Proof.
      intro.
      destruct m.
      unfold pureOp_udiv; rewrite bv_udiv_correct_1.
      simpl nth; rewrite nth_replace. 
      reflexivity.
      assumption.
    Qed.

    Theorem pureOp_udiv_flag_correct (ri rj : regId) (A : Word) (m : MachineState) :
      flag (pureOp_udiv ri rj A m)
      = (bitvector_nat_big A =? 0).
    Proof.
      destruct m; simpl flag.
      rewrite Bool.eq_iff_eq_true, bv_eq_equiv, eqb_eq.
      apply bitvector_fin_big_0_const.
    Qed.

    Theorem pureOp_udiv_interp_imm {S} (k: itree E S) (ri rj : regId) 
                                  (A : Word) (m : MachineState) :
    interp_machine (denote_instruction (udivI ri rj, inl A) ;; k) m
    ≈ interp_machine k (pureOp_udiv ri rj A m).
    Proof. tau_steps; destruct m; reflexivity. Qed.

    Theorem pureOp_udiv_interp_reg {S} (k: itree E S) (ri rj A : regId)
                                  (m : MachineState) :
    interp_machine (denote_instruction (udivI ri rj, inr A) ;; k) m
    ≈ interp_machine k (pureOp_udiv ri rj (nth (registers m) A) m).
    Proof. tau_steps; destruct m; reflexivity. Qed.

    (*"""
    compute remainder of [rj]u/[A]u and store result in ri
    [flag:] [A]u = 0
    """*)
    Definition pureOp_umod (ri rj : regId) (A : Word) :
      MachineState -> MachineState.
      intro ms; destruct ms.
      apply (nth registers0) in rj.
      remember (bv_umod rj A) as res.
      split.
      (* PC *)
      - exact (bv_succ programCounter0).
      (* Registers *)
      - exact (replace registers0 ri res).
      (* Flag *)
      - exact (bv_eq A (const b0 _)).
      (* Memory *)
      - exact memory0.
      (* Main Tape *)
      - exact tapeMain0.
      (* Aux Tape *)
      - exact tapeAux0.
      (* Program *)
      - exact program0.
    Defined.

    Theorem pureOp_umod_correct (ri rj : regId) (A : Word) (m : MachineState) :
      bitvector_nat_big A > 0 ->
      nth (registers (pureOp_umod ri rj A m)) ri
      = nat_bitvector_big _ 
        (bitvector_nat_big (nth (registers m) rj) mod bitvector_nat_big A).
    Proof.
      intro.
      destruct m.
      unfold pureOp_umod; rewrite bv_umod_correct_1.
      simpl nth; rewrite nth_replace. 
      reflexivity.
      assumption.
    Qed.

    Theorem pureOp_umod_flag_correct (ri rj : regId) (A : Word) (m : MachineState) :
      flag (pureOp_umod ri rj A m)
      = (bitvector_nat_big A =? 0).
    Proof.
      destruct m; simpl flag.
      rewrite Bool.eq_iff_eq_true, bv_eq_equiv, eqb_eq.
      apply bitvector_fin_big_0_const.
    Qed.

    Theorem pureOp_umod_interp_imm {S} (k: itree E S) (ri rj : regId) 
                                  (A : Word) (m : MachineState) :
    interp_machine (denote_instruction (umodI ri rj, inl A) ;; k) m
    ≈ interp_machine k (pureOp_umod ri rj A m).
    Proof. tau_steps; destruct m; reflexivity. Qed.

    Theorem pureOp_umod_interp_reg {S} (k: itree E S) (ri rj A : regId)
                                  (m : MachineState) :
    interp_machine (denote_instruction (umodI ri rj, inr A) ;; k) m
    ≈ interp_machine k (pureOp_umod ri rj (nth (registers m) A) m).
    Proof. tau_steps; destruct m; reflexivity. Qed.

    (*"""
    shift [rj] by [A]u bits to the left and store result in ri
    [flag:] MSB of [rj]
    """*)
    Definition pureOp_shl (ri rj : regId) (A : Word) :
      MachineState -> MachineState.
      intro ms; destruct ms.
      apply (nth registers0) in rj.
      split.
      (* PC *)
      - exact (bv_succ programCounter0).
      (* Registers *)
      - apply bitvector_nat_big in A.
        remember (bv_shl A rj) as res.
        exact (replace registers0 ri res).
      (* Flag *)
      - exact (hd (wcast rj)).
      (* Memory *)
      - exact memory0.
      (* Main Tape *)
      - exact tapeMain0.
      (* Aux Tape *)
      - exact tapeAux0.
      (* Program *)
      - exact program0.
    Defined.

    Theorem pureOp_shl_correct (ri rj : regId) (A : Word) 
                              (m : MachineState) (e : bitvector_nat_big A <= wordSize):
      nth (registers (pureOp_shl ri rj A m)) ri
      = cast (snd (splitat _ (cast (nth (registers m) rj)
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
      flag (pureOp_shl ri rj A m) = hd (wcast (nth (registers m) rj)).
    Proof. destruct m; reflexivity. Qed.

    Theorem pureOp_shl_interp_imm {S} (k: itree E S) (ri rj : regId) 
                                  (A : Word) (m : MachineState) :
    interp_machine (denote_instruction (shlI ri rj, inl A) ;; k) m
    ≈ interp_machine k (pureOp_shl ri rj A m).
    Proof. tau_steps; destruct m; reflexivity. Qed.

    Theorem pureOp_shl_interp_reg {S} (k: itree E S) (ri rj A : regId)
                                  (m : MachineState) :
    interp_machine (denote_instruction (shlI ri rj, inr A) ;; k) m
    ≈ interp_machine k (pureOp_shl ri rj (nth (registers m) A) m).
    Proof. tau_steps; destruct m; reflexivity. Qed.

    (*"""
    shift [rj] by [A]u bits to the right and store result in ri
    [flag:] LSB of [rj]
    """*)
    Definition pureOp_shr (ri rj : regId) (A : Word) :
      MachineState -> MachineState.
      intro ms; destruct ms.
      apply (nth registers0) in rj.      
      split.
      (* PC *)
      - exact (bv_succ programCounter0).
      (* Registers *)
      - apply bitvector_nat_big in A.
        remember (bv_shr A rj) as res.
        exact (replace registers0 ri res).
      (* Flag *)
      - exact (last (wcast rj)).
      (* Memory *)
      - exact memory0.
      (* Main Tape *)
      - exact tapeMain0.
      (* Aux Tape *)
      - exact tapeAux0.
      (* Program *)
      - exact program0.
    Defined.

    Theorem pureOp_shr_correct (ri rj : regId) (A : Word) 
                              (m : MachineState) (e : bitvector_nat_big A <= wordSize):
      nth (registers (pureOp_shr ri rj A m)) ri
      = cast (const b0 _ ++ fst (splitat _ (cast (nth (registers m) rj)
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
      flag (pureOp_shr ri rj A m) = last (wcast (nth (registers m) rj)).
    Proof. destruct m; reflexivity. Qed.

    Theorem pureOp_shr_interp_imm {S} (k: itree E S) (ri rj : regId) 
                                  (A : Word) (m : MachineState) :
    interp_machine (denote_instruction (shrI ri rj, inl A) ;; k) m
    ≈ interp_machine k (pureOp_shr ri rj A m).
    Proof. tau_steps; destruct m; reflexivity. Qed.

    Theorem pureOp_shr_interp_reg {S} (k: itree E S) (ri rj A : regId)
                                  (m : MachineState) :
    interp_machine (denote_instruction (shrI ri rj, inr A) ;; k) m
    ≈ interp_machine k (pureOp_shr ri rj (nth (registers m) A) m).
    Proof. tau_steps; destruct m; reflexivity. Qed.

    (*"""
    “compare equal”
    [flag:] [ri] = [A]
    """*)
    Definition pureOp_cmpe (ri : regId) (A : Word) :
      MachineState -> MachineState.
      intro ms; destruct ms.
      apply (nth registers0) in ri.      
      split.
      (* PC *)
      - exact (bv_succ programCounter0).
      (* Registers *)
      - exact registers0.
      (* Flag *)
      - exact (bv_eq ri A).
      (* Memory *)
      - exact memory0.
      (* Main Tape *)
      - exact tapeMain0.
      (* Aux Tape *)
      - exact tapeAux0.
      (* Program *)
      - exact program0.
    Defined.

    Theorem pureOp_cmpe_flag_correct (ri : regId) (A : Word) (m : MachineState) :
      flag (pureOp_cmpe ri A m) = bv_eq (nth (registers m) ri) A.
    Proof. destruct m; reflexivity. Qed.

    Theorem registers_pureOp_cmpe : forall v1 v2 m,
      registers (pureOp_cmpe v1 v2 m) = registers m.
    Proof. intros; destruct m; reflexivity. Qed.

    Theorem memory_pureOp_cmpe : forall v1 v2 m,
      memory (pureOp_cmpe v1 v2 m) = memory m.
    Proof. intros; destruct m; reflexivity. Qed.

    Theorem pureOp_cmpe_interp_imm {S} (k: itree E S) (ri : regId) 
                                  (A : Word) (m : MachineState) :
    interp_machine (denote_instruction (cmpeI ri, inl A) ;; k) m
    ≈ interp_machine k (pureOp_cmpe ri A m).
    Proof. tau_steps; destruct m; reflexivity. Qed.

    Theorem pureOp_cmpe_interp_reg {S} (k: itree E S) (ri A : regId)
                                  (m : MachineState) :
    interp_machine (denote_instruction (cmpeI ri, inr A) ;; k) m
    ≈ interp_machine k (pureOp_cmpe ri (nth (registers m) A) m).
    Proof. tau_steps; destruct m; reflexivity. Qed.

    (*"""
    “compare above”, unsigned
    [flag:] [ri]u > [A]u
    """*)
    Definition pureOp_cmpa (ri : regId) (A : Word) :
      MachineState -> MachineState.
      intro ms; destruct ms.
      apply (nth registers0) in ri.
      split.
      (* PC *)
      - exact (bv_succ programCounter0).
      (* Registers *)
      - exact registers0.
      (* Flag *)
      - exact (bv_lt A ri).
      (* Memory *)
      - exact memory0.
      (* Main Tape *)
      - exact tapeMain0.
      (* Aux Tape *)
      - exact tapeAux0.
      (* Program *)
      - exact program0.
    Defined.

    Theorem pureOp_cmpa_flag_correct (ri : regId) (A : Word) (m : MachineState) :
      flag (pureOp_cmpa ri A m) = 
      (bitvector_nat_big A <? bitvector_nat_big (nth (registers m) ri)).
    Proof.
      destruct m.
      unfold pureOp_cmpa, flag, registers.
      rewrite bv_lt_correct.
      reflexivity.
    Qed.

    Theorem pureOp_cmpa_interp_imm {S} (k: itree E S) (ri : regId) 
                                  (A : Word) (m : MachineState) :
    interp_machine (denote_instruction (cmpaI ri, inl A) ;; k) m
    ≈ interp_machine k (pureOp_cmpa ri A m).
    Proof. tau_steps; destruct m; reflexivity. Qed.

    Theorem pureOp_cmpa_interp_reg {S} (k: itree E S) (ri A : regId)
                                  (m : MachineState) :
    interp_machine (denote_instruction (cmpaI ri, inr A) ;; k) m
    ≈ interp_machine k (pureOp_cmpa ri (nth (registers m) A) m).
    Proof. tau_steps; destruct m; reflexivity. Qed.

    (*"""
    “compare above or equal”, unsigned
    [flag:] [ri]u ≥ [A]u
    """*)
    Definition pureOp_cmpae (ri : regId) (A : Word) :
      MachineState -> MachineState.
      intro ms; destruct ms.
      apply (nth registers0) in ri.
      split.
      (* PC *)
      - exact (bv_succ programCounter0).
      (* Registers *)
      - exact registers0.
      (* Flag *)
      - exact (bv_le A ri).
      (* Memory *)
      - exact memory0.
      (* Main Tape *)
      - exact tapeMain0.
      (* Aux Tape *)
      - exact tapeAux0.
      (* Program *)
      - exact program0.
    Defined.

    Theorem pureOp_cmpae_flag_correct (ri : regId) (A : Word) (m : MachineState) :
      flag (pureOp_cmpae ri A m) = 
      (bitvector_nat_big A <=? bitvector_nat_big (nth (registers m) ri)).
    Proof. 
      destruct m.
      unfold pureOp_cmpae, flag, registers.
      rewrite bv_le_correct.
      reflexivity.
    Qed.

    Theorem pureOp_cmpae_interp_imm {S} (k: itree E S) (ri : regId) 
                                  (A : Word) (m : MachineState) :
    interp_machine (denote_instruction (cmpaeI ri, inl A) ;; k) m
    ≈ interp_machine k (pureOp_cmpae ri A m).
    Proof. tau_steps; destruct m; reflexivity. Qed.

    Theorem pureOp_cmpae_interp_reg {S} (k: itree E S) (ri A : regId)
                                  (m : MachineState) :
    interp_machine (denote_instruction (cmpaeI ri, inr A) ;; k) m
    ≈ interp_machine k (pureOp_cmpae ri (nth (registers m) A) m).
    Proof. tau_steps; destruct m; reflexivity. Qed.

    (*"""
    “compare greater”, signed
    [flag:] [ri]s > [A]s
    """*)
    Definition pureOp_cmpg (ri : regId) (A : Word) :
      MachineState -> MachineState.
      intro ms; destruct ms.
      apply (nth registers0) in ri.
      apply wcast in ri, A.
      split.
      (* PC *)
      - exact (bv_succ programCounter0).
      (* Registers *)
      - exact registers0.
      (* Flag *)
      - apply twos_complement in ri, A.
        exact (A <? ri)%Z.
      (* Memory *)
      - exact memory0.
      (* Main Tape *)
      - exact tapeMain0.
      (* Aux Tape *)
      - exact tapeAux0.
      (* Program *)
      - exact program0.
    Defined.

    Theorem pureOp_cmpg_flag_correct (ri : regId) (A : Word) (m : MachineState) :
      flag (pureOp_cmpg ri A m) = 
      (twos_complement (wcast A) <?
      twos_complement (wcast (nth (registers m) ri)))%Z.
    Proof. destruct m; reflexivity. Qed.

    Theorem pureOp_cmpg_interp_imm {S} (k: itree E S) (ri : regId) 
                                  (A : Word) (m : MachineState) :
    interp_machine (denote_instruction (cmpgI ri, inl A) ;; k) m
    ≈ interp_machine k (pureOp_cmpg ri A m).
    Proof. tau_steps; destruct m; reflexivity. Qed.

    Theorem pureOp_cmpg_interp_reg {S} (k: itree E S) (ri A : regId)
                                  (m : MachineState) :
    interp_machine (denote_instruction (cmpgI ri, inr A) ;; k) m
    ≈ interp_machine k (pureOp_cmpg ri (nth (registers m) A) m).
    Proof. tau_steps; destruct m; reflexivity. Qed.

    (*"""
    “compare greater or equal”, signed
    [flag:] [ri]s ≥ [A]s
    """*)
    Definition pureOp_cmpge (ri : regId) (A : Word) :
      MachineState -> MachineState.
      intro ms; destruct ms.
      apply (nth registers0) in ri.
      apply wcast in ri, A.
      split.
      (* PC *)
      - exact (bv_succ programCounter0).
      (* Registers *)
      - exact registers0.
      (* Flag *)
      - apply twos_complement in ri, A.
        exact (A <=? ri)%Z.
      (* Memory *)
      - exact memory0.
      (* Main Tape *)
      - exact tapeMain0.
      (* Aux Tape *)
      - exact tapeAux0.
      (* Program *)
      - exact program0.
    Defined.

    Theorem pureOp_cmpge_flag_correct (ri : regId) (A : Word) (m : MachineState) :
      flag (pureOp_cmpge ri A m) = 
      (twos_complement (wcast A) <=?
      twos_complement (wcast (nth (registers m) ri)))%Z.
    Proof. destruct m; reflexivity. Qed.

    Theorem pureOp_cmpge_interp_imm {S} (k: itree E S) (ri : regId) 
                                  (A : Word) (m : MachineState) :
    interp_machine (denote_instruction (cmpgeI ri, inl A) ;; k) m
    ≈ interp_machine k (pureOp_cmpge ri A m).
    Proof. tau_steps; destruct m; reflexivity. Qed.

    Theorem pureOp_cmpge_interp_reg {S} (k: itree E S) (ri A : regId)
                                  (m : MachineState) :
    interp_machine (denote_instruction (cmpgeI ri, inr A) ;; k) m
    ≈ interp_machine k (pureOp_cmpge ri (nth (registers m) A) m).
    Proof. tau_steps; destruct m; reflexivity. Qed.

    (*"""
    store [A] in ri
    """*)
    Definition pureOp_mov (ri : regId) (A : Word) :
      MachineState -> MachineState.
      intro ms; destruct ms.
      split.
      (* PC *)
      - exact (bv_succ programCounter0).
      (* Registers *)
      - exact (replace registers0 ri A).
      (* Flag *)
      - exact flag0.
      (* Memory *)
      - exact memory0.
      (* Main Tape *)
      - exact tapeMain0.
      (* Aux Tape *)
      - exact tapeAux0.
      (* Program *)
      - exact program0.
    Defined.

    Theorem pureOp_mov_correct (ri : regId) (A : Word) (m : MachineState) :
      nth (registers (pureOp_mov ri A m)) ri = A.
    Proof. destruct m; simpl; rewrite nth_replace; reflexivity. Qed.

    Theorem pureOp_mov_interp_imm {S} (k: itree E S) (ri : regId) 
                                  (A : Word) (m : MachineState) :
    interp_machine (denote_instruction (movI ri, inl A) ;; k) m
    ≈ interp_machine k (pureOp_mov ri A m).
    Proof. tau_steps; destruct m; reflexivity. Qed.

    Theorem pureOp_mov_interp_reg {S} (k: itree E S) (ri A : regId)
                                  (m : MachineState) :
    interp_machine (denote_instruction (movI ri, inr A) ;; k) m
    ≈ interp_machine k (pureOp_mov ri (nth (registers m) A) m).
    Proof. tau_steps; destruct m; reflexivity. Qed.

    (*"""
    if flag = 1, store [A] in ri
    """*)
    Definition pureOp_cmov (ri : regId) (A : Word) :
      MachineState -> MachineState.
      intro ms; destruct ms.
      split.
      (* PC *)
      - exact (bv_succ programCounter0).
      (* Registers *)
      - exact (if flag0
              then (replace registers0 ri A) 
              else registers0).
      (* Flag *)
      - exact flag0.
      (* Memory *)
      - exact memory0.
      (* Main Tape *)
      - exact tapeMain0.
      (* Aux Tape *)
      - exact tapeAux0.
      (* Program *)
      - exact program0.
    Defined.

    Theorem pureOp_cmov_correct_0 (ri : regId) (A : Word) (m : MachineState) :
      flag m = b0 ->
      nth (registers (pureOp_cmov ri A m)) ri = 
      nth (registers m) ri.
    Proof. destruct m; simpl; intro H; rewrite H; reflexivity. Qed.

    Theorem pureOp_cmov_correct_1 (ri : regId) (A : Word) (m : MachineState) :
      flag m = b1 ->
      nth (registers (pureOp_cmov ri A m)) ri = A.
    Proof.
      destruct m; simpl; intro H; rewrite H; simpl; 
      rewrite nth_replace; reflexivity.
    Qed.

    Theorem pureOp_cmov_interp_imm {S} (k: itree E S) (ri : regId) 
                                  (A : Word) (m : MachineState) :
    interp_machine (denote_instruction (cmovI ri, inl A) ;; k) m
    ≈ interp_machine k (pureOp_cmov ri A m).
    Proof.
      tau_steps; destruct m; cbn.
      remember (ITree.subst _ (Ret _)) as inlA eqn:inlADef.
      assert (inlA = (if flag0 then (trigger (GetReg ri);; trigger (SetReg ri A)) else Ret tt);; trigger IncPC) as H.
      2: { rewrite H. destruct flag0; tau_steps; reflexivity. }
      rewrite inlADef.
      apply bisimulation_is_eq.
      change (ITree.subst ?k ?x) with (ITree.bind x k).
      rewrite bind_ret_l.
      reflexivity.
    Qed.

    Theorem pureOp_cmov_interp_reg {S} (k: itree E S) (ri A : regId)
                                  (m : MachineState) :
    interp_machine (denote_instruction (cmovI ri, inr A) ;; k) m
    ≈ interp_machine k (pureOp_cmov ri (nth (registers m) A) m).
    Proof.
      tau_steps; destruct m; cbn.
      remember (ITree.subst _ (Ret _)) as inlA eqn:inlADef.
      assert (inlA = (if flag0 then (trigger (GetReg ri);; trigger (SetReg ri (nth registers0 A))) else Ret tt);; trigger IncPC) as H.
      2: { rewrite H. destruct flag0; tau_steps; reflexivity. }
      rewrite inlADef.
      apply bisimulation_is_eq.
      change (ITree.subst ?k ?x) with (ITree.bind x k).
      rewrite bind_ret_l.
      reflexivity.
    Qed.

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
      - exact registers0.
      (* Flag *)
      - exact flag0.
      (* Memory *)
      - exact memory0.
      (* Main Tape *)
      - exact tapeMain0.
      (* Aux Tape *)
      - exact tapeAux0.
      (* Program *)
      - exact program0.
    Defined.

    Theorem pureOp_jmp_correct (A : Word) (m : MachineState) :
      programCounter (pureOp_jmp A m) = A.
    Proof. destruct m; reflexivity. Qed.

    Theorem pureOp_jmp_interp_imm {S} (k: itree E S)
                                  (A : Word) (m : MachineState) :
    interp_machine (denote_instruction (jmpI, inl A) ;; k) m
    ≈ interp_machine k (pureOp_jmp A m).
    Proof. tau_steps; destruct m; reflexivity. Qed.

    Theorem pureOp_jmp_interp_reg {S} (k: itree E S) (A : regId)
                                  (m : MachineState) :
    interp_machine (denote_instruction (jmpI, inr A) ;; k) m
    ≈ interp_machine k (pureOp_jmp (nth (registers m) A) m).
    Proof. tau_steps; destruct m; reflexivity. Qed.

    (*"""
    if flag = 1, set pc to [A] (else increment pc as usual)
    """*)
    Definition pureOp_cjmp (A : Word) :
      MachineState -> MachineState.
      intro ms; destruct ms.
      split.
      (* PC *)
      - destruct flag0.
        + exact A.
        + exact (bv_succ programCounter0).
      (* Registers *)
      - exact registers0.
      (* Flag *)
      - exact flag0.
      (* Memory *)
      - exact memory0.
      (* Main Tape *)
      - exact tapeMain0.
      (* Aux Tape *)
      - exact tapeAux0.
      (* Program *)
      - exact program0.
    Defined.

    Theorem pureOp_cjmp_correct_0 (A : Word) (m : MachineState) :
      flag m = b0 ->
      programCounter (pureOp_cjmp A m) = 
      (bv_succ (programCounter m)).
    Proof. destruct m; simpl; intro H; rewrite H; reflexivity. Qed.

    Theorem pureOp_cjmp_correct_1 (A : Word) (m : MachineState) :
      flag m = b1 ->
      programCounter (pureOp_cjmp A m) = A.
    Proof. destruct m; simpl; intro H; rewrite H; reflexivity. Qed.

    Theorem registers_pureOp_cjmp : forall v m,
      registers (pureOp_cjmp v m) = registers m.
    Proof. intros; destruct m; reflexivity. Qed.

    Theorem memory_pureOp_cjmp : forall v m,
      memory (pureOp_cjmp v m) = memory m.
    Proof. intros; destruct m; reflexivity. Qed.

    Theorem pureOp_cjmp_interp_imm {S} (k: itree E S)
                                  (A : Word) (m : MachineState) :
    interp_machine (denote_instruction (cjmpI, inl A) ;; k) m
    ≈ interp_machine k (pureOp_cjmp A m).
    Proof.
      tau_steps; destruct m; cbn.
      repeat change (ITree.subst ?k ?x) with (ITree.bind x k).
      rewrite (bisimulation_is_eq _ _ (bind_ret_l _ _)).
      destruct flag0; tau_steps; reflexivity.
    Qed.

    Theorem pureOp_cjmp_interp_reg {S} (k: itree E S) (A : regId)
                                  (m : MachineState) :
    interp_machine (denote_instruction (cjmpI, inr A) ;; k) m
    ≈ interp_machine k (pureOp_cjmp (nth (registers m) A) m).
    Proof.
      tau_steps; destruct m; cbn.
      repeat change (ITree.subst ?k ?x) with (ITree.bind x k).
      rewrite (bisimulation_is_eq _ _ (bind_ret_l _ _)).
      destruct flag0; tau_steps; reflexivity.
    Qed.

    (*"""
    if flag = 0, set pc to [A] (else increment pc as usual)
    """*)
    Definition pureOp_cnjmp (A : Word) :
      MachineState -> MachineState.
      intro ms; destruct ms.
      split.
      (* PC *)
      - destruct flag0.
        + exact (bv_succ programCounter0).
        + exact A.
      (* Registers *)
      - exact registers0.
      (* Flag *)
      - exact flag0.
      (* Memory *)
      - exact memory0.
      (* Main Tape *)
      - exact tapeMain0.
      (* Aux Tape *)
      - exact tapeAux0.
      (* Program *)
      - exact program0.
    Defined.

    Theorem pureOp_cnjmp_correct_0 (A : Word) (m : MachineState) :
      flag m = b0 ->
      programCounter (pureOp_cnjmp A m) = A.
    Proof. destruct m; simpl; intro H; rewrite H; reflexivity. Qed.

    Theorem pureOp_cnjmp_correct_1 (A : Word) (m : MachineState) :
      flag m = b1 ->
      programCounter (pureOp_cnjmp A m) = 
      (bv_succ (programCounter m)).
    Proof. destruct m; simpl; intro H; rewrite H; reflexivity. Qed.

    Theorem pureOp_cnjmp_interp_imm {S} (k: itree E S)
                                  (A : Word) (m : MachineState) :
    interp_machine (denote_instruction (cnjmpI, inl A) ;; k) m
    ≈ interp_machine k (pureOp_cnjmp A m).
    Proof.
      tau_steps; destruct m; cbn.
      repeat change (ITree.subst ?k ?x) with (ITree.bind x k).
      rewrite (bisimulation_is_eq _ _ (bind_ret_l _ _)).
      destruct flag0; tau_steps; reflexivity.
    Qed.

    Theorem pureOp_cnjmp_interp_reg {S} (k: itree E S) (A : regId)
                                  (m : MachineState) :
    interp_machine (denote_instruction (cnjmpI, inr A) ;; k) m
    ≈ interp_machine k (pureOp_cnjmp (nth (registers m) A) m).
    Proof.
      tau_steps; destruct m; cbn.
      repeat change (ITree.subst ?k ?x) with (ITree.bind x k).
      rewrite (bisimulation_is_eq _ _ (bind_ret_l _ _)).
      destruct flag0; tau_steps; reflexivity.
    Qed.

    (*"""
    store the least-significant byte of [ri] at the [A]u-th byte in memory
    """*)
    Definition pureOp_store_b (ri : regId) (A : Word) :
      MachineState -> MachineState.
      intro ms; destruct ms; apply (nth registers0) in ri; split.
      (* PC *)
      - exact (bv_succ programCounter0).
      (* Registers *)
      - exact registers0.
      (* Flag *)
      - exact flag0.
      (* Memory *)
      - apply (replace memory0).
        (*" at the [A]u-th byte "*)
        + exact (bitvector_fin_big A).
        (*" the least-significant byte of [ri] "*)
        + exact (snd (splitat _ (wbcast ri))).
      (* Main Tape *)
      - exact tapeMain0.
      (* Aux Tape *)
      - exact tapeAux0.
      (* Program *)
      - exact program0.
    Defined.

    Theorem pureOp_store_b_correct :
      forall (ri : regId) (A : Word) (m : MachineState),
      nth (memory (pureOp_store_b ri A m)) (bitvector_fin_big A)
        = snd (splitat _ (wbcast (nth (registers m) ri))).
    Proof.
      intros [ri ltri] A m; destruct m; simpl.
      apply nth_replace.
    Qed.

    Theorem pureOp_store_b_interp_imm {S} (k: itree E S) (ri : regId) 
                                  (A : Word) (m : MachineState) :
    interp_machine (denote_instruction (store_bI ri, inl A) ;; k) m
    ≈ interp_machine k (pureOp_store_b ri A m).
    Proof. tau_steps; destruct m; reflexivity. Qed.

    Theorem pureOp_store_b_interp_reg {S} (k: itree E S) (ri A : regId)
                                  (m : MachineState) :
    interp_machine (denote_instruction (store_bI ri, inr A) ;; k) m
    ≈ interp_machine k (pureOp_store_b ri (nth (registers m) A) m).
    Proof. tau_steps; destruct m; reflexivity. Qed.

    (*"""
    store into ri (with zero-padding in front) the [A]u-th byte in memory
    """*)
    Definition pureOp_load_b (ri : regId) (A : Word) :
      MachineState -> MachineState.
      intro ms; destruct ms; split.
      (* PC *)
      - exact (bv_succ programCounter0).
      (* Registers *)
      - apply (replace registers0 ri).
        apply (fun x => wbuncast (const b0 _ ++ x)).
        (*" [A]u-th byte in memory "*)
        exact (nth memory0 (bitvector_fin_big A)).
      (* Flag *)
      - exact flag0.
      (* Memory *)
      - exact memory0.
      (* Main Tape *)
      - exact tapeMain0.
      (* Aux Tape *)
      - exact tapeAux0.
      (* Program *)
      - exact program0.
    Defined.

    Theorem pureOp_load_b_correct :
      forall (ri : regId) (A : Word) (m : MachineState),
        nth (registers (pureOp_load_b ri A m)) ri = 
        (wbuncast (const b0 _ ++ nth (memory m) (bitvector_fin_big A))).
    Proof.
      intros [ri ltri] A m; destruct m; simpl.
      rewrite nth_replace.
      reflexivity.
    Qed.

    Theorem pureOp_load_b_interp_imm {S} (k: itree E S) (ri : regId) 
                                  (A : Word) (m : MachineState) :
    interp_machine (denote_instruction (load_bI ri, inl A) ;; k) m
    ≈ interp_machine k (pureOp_load_b ri A m).
    Proof. tau_steps; destruct m; reflexivity. Qed.

    Theorem pureOp_load_b_interp_reg {S} (k: itree E S) (ri A : regId)
                                  (m : MachineState) :
    interp_machine (denote_instruction (load_bI ri, inr A) ;; k) m
    ≈ interp_machine k (pureOp_load_b ri (nth (registers m) A) m).
    Proof. tau_steps; destruct m; reflexivity. Qed.

    (*"""
    store [ri] at the word in memory that is aligned to the [A]w-th byte
    """*)
    Definition pureOp_store_w (ri : regId) (A : Word) :
      MachineState -> MachineState.
      intro ms; destruct ms; split.
      (* PC *)
      - exact (bv_succ programCounter0).
      (* Registers *)
      - exact registers0.
      (* Flag *)
      - exact flag0.
      (* Memory *)
      - apply (Memory_Word_Store_from_Reg memory0).
        (*" at the word in memory that is aligned to the [A]w-th byte "*)
        + exact A. 
        (* store [ri] *)
        + exact (nth registers0 ri).
      (* Main Tape *)
      - exact tapeMain0.
      (* Aux Tape *)
      - exact tapeAux0.
      (* Program *)
      - exact program0.
    Defined.

    Theorem pureOp_store_w_correct_lem : (2 ^ wordSize) <> 0.
    Proof. apply pow_nonzero; lia. Qed.

    Theorem pureOp_store_w_correct (ri : regId) (A : Word) (m : MachineState) :
      forall (bid : fin wordSizeEighth),
      nth (WordBytes (nth (registers m) ri)) bid =
      nth (memory (pureOp_store_w ri A m))
          (exist _ ((wordSizeEighth - proj1_sig bid - 1 + bitvector_nat_big A) mod (2 ^ wordSize))
                  (PeanoNat.Nat.mod_upper_bound _ _ pureOp_store_w_correct_lem)).
    Proof.
      intros bid; destruct m; simpl.
      unfold Memory_Word_Store_from_Reg, Memory_Word_Store, Memory_Block_Store.
      replace (WordBytes (nth registers0 ri))
        with (rev (rev (WordBytes (nth registers0 ri)))).
      2: { apply vector_rev_rev_id. }
      rewrite nth_rev.
      rewrite (Block_Store_Spec pureOp_store_w_correct_lem
                                memory0
                                (bitvector_fin_big A)
                                wordSizeEighthFin
                                (rev (WordBytes (nth registers0 ri)))).
      reflexivity.
    Qed.

    Theorem pureOp_store_w_interp_imm {S} (k: itree E S) (ri : regId) 
                                  (A : Word) (m : MachineState) :
    interp_machine (denote_instruction (store_wI ri, inl A) ;; k) m
    ≈ interp_machine k (pureOp_store_w ri A m).
    Proof. tau_steps; destruct m; reflexivity. Qed.

    Theorem pureOp_store_w_interp_reg {S} (k: itree E S) (ri A : regId)
                                  (m : MachineState) :
    interp_machine (denote_instruction (store_wI ri, inr A) ;; k) m
    ≈ interp_machine k (pureOp_store_w ri (nth (registers m) A) m).
    Proof. tau_steps; destruct m; reflexivity. Qed.

    (*"""
    store into ri the word in memory that is aligned to the [A]w-th byte
    """*)
    Definition pureOp_load_w (ri : regId) (A : Word) :
      MachineState -> MachineState.
      intro ms; destruct ms; split.
      (* PC *)
      - exact (bv_succ programCounter0).
      (* Registers *)
      - apply (replace registers0 ri).
        apply (Memory_Word_Load_from_Reg memory0).
        exact A.
      (* Flag *)
      - exact flag0. 
      (* Memory *)
      - exact memory0.
      (* Main Tape *)
      - exact tapeMain0.
      (* Aux Tape *)
      - exact tapeAux0.
      (* Program *)
      - exact program0.
    Defined.

    Theorem pureOp_load_w_correct (ri : regId) (A : Word) (m : MachineState) :
      forall (bid : fin wordSizeEighth),
      nth (WordBytes (nth (registers (pureOp_load_w ri A m)) ri)) bid =
      nth (memory m) (exist _ ((wordSizeEighth - proj1_sig bid - 1 + bitvector_nat_big A) mod (2 ^ wordSize))
                              (PeanoNat.Nat.mod_upper_bound _ _ pureOp_store_w_correct_lem)).
    Proof.
      intros bid; destruct m; simpl.
      unfold Memory_Word_Load_from_Reg, Memory_Word_Load, Memory_Block_Load.
      rewrite nth_replace; unfold WordBytes; rewrite vector_concat_inv2, nth_rev.
      rewrite (Block_Load_Spec pureOp_store_w_correct_lem
                              memory0
                              (bitvector_fin_big A)
                              wordSizeEighthFin); simpl.
      reflexivity.
    Qed.

    Theorem pureOp_load_w_interp_imm {S} (k: itree E S) (ri : regId) 
                                  (A : Word) (m : MachineState) :
    interp_machine (denote_instruction (load_wI ri, inl A) ;; k) m
    ≈ interp_machine k (pureOp_load_w ri A m).
    Proof. tau_steps; destruct m; reflexivity. Qed.

    Theorem pureOp_load_w_interp_reg {S} (k: itree E S) (ri A : regId)
                                  (m : MachineState) :
    interp_machine (denote_instruction (load_wI ri, inr A) ;; k) m
    ≈ interp_machine k (pureOp_load_w ri (nth (registers m) A) m).
    Proof. tau_steps; destruct m; reflexivity. Qed.

    (* """ stores in ri the next W-bit word on the [A]u-th tape [...]
          and set flag = 0; """ *)
    (* """ if there are no remaining input words on the [A]u-th tape store
          0_W in ri and set flag = 1. """ *)
    Definition pureOp_read (ri : regId) (A : Word) :
      MachineState -> MachineState.
      intro ms; destruct ms; split.
      (* PC *)
      - exact (bv_succ programCounter0).
      (* Registers *)
      - apply (replace registers0 ri).
        destruct (bitvector_nat_big A).
        + destruct tapeMain0.
          * exact (const b0 _).
          * exact w.
        + destruct n.
          * destruct tapeAux0.
            -- exact (const b0 _).
            -- exact w.
          * exact (const b0 _).
      (* Flag *)
      - destruct (bitvector_nat_big A).
        + destruct tapeMain0.
          * exact b1.
          * exact b0.
        + destruct n.
          * destruct tapeAux0.
            -- exact b1.
            -- exact b0.
          * exact b1.
      (* Memory *)
      - exact memory0.
      (* Main Tape *)
      - destruct (bitvector_nat_big A).
        + destruct tapeMain0.
          * exact List.nil.
          * exact tapeMain0.
        + exact tapeMain0.
      (* Aux Tape *)
      - destruct (bitvector_nat_big A).
        + exact tapeAux0.
        + destruct n.
          * destruct tapeAux0.
            -- exact List.nil.
            -- exact tapeAux0.
          * exact tapeAux0.
      (* Program *)
      - exact program0.
    Defined.

    Lemma pureOp_read_correct_lem : 1 < 2 ^ wordSize.
    Proof.
      assert (wordSize = wordSize - 8 + 8); [ apply wordSize_expand | ].
      replace wordSize with (S (7 + (wordSize - 8))); [ | lia ].
      rewrite pow_succ_r'.
      assert (0 < 2 ^ (7 + (wordSize - 8))); [ apply zero2pow | lia ].
    Qed.

    Theorem pureOp_read_correct_main_0 (ri : regId) (m : MachineState) :
      tapeMain m = List.nil ->
      nth (registers (pureOp_read ri (nat_bitvector_big _ 0) m)) ri
      = const b0 _.
    Proof.
      destruct m; simpl; intro eq.
      rewrite nth_replace, nat_bitvector_big_inv;
      [ rewrite eq; reflexivity | apply zero2pow ].
    Qed.

    Theorem pureOp_read_correct_main_1 (ri : regId) (m : MachineState) :
      forall x xs,
      tapeMain m = List.cons x xs ->
      nth (registers (pureOp_read ri (nat_bitvector_big _ 0) m)) ri
      = x.
    Proof.
      destruct m; simpl; intros x xs eq.
      rewrite nth_replace, nat_bitvector_big_inv;
      [ rewrite eq; reflexivity | apply zero2pow ].
    Qed.

    Theorem pureOp_read_correct_main_updt (ri : regId) (m : MachineState) :
      forall x xs,
      tapeMain m = List.cons x xs ->
      tapeMain (pureOp_read ri (nat_bitvector_big _ 0) m) = xs.
    Proof.
      destruct m; simpl; intros x xs eq.
      rewrite nat_bitvector_big_inv;
      [ rewrite eq; reflexivity | apply zero2pow ].
    Qed.

    Theorem pureOp_read_correct_aux_0 (ri : regId) (m : MachineState) :
      tapeAux m = List.nil ->
      nth (registers (pureOp_read ri (nat_bitvector_big _ 1) m)) ri
      = const b0 _.
    Proof.
      destruct m; simpl; intro eq.
      rewrite nth_replace, nat_bitvector_big_inv; 
      [ rewrite eq; reflexivity | apply pureOp_read_correct_lem ].
    Qed.

    Theorem pureOp_read_correct_aux_1 (ri : regId) (m : MachineState) :
      forall x xs,
      tapeAux m = List.cons x xs ->
      nth (registers (pureOp_read ri (nat_bitvector_big _ 1) m)) ri
      = x.
    Proof.
      destruct m; simpl; intros x xs eq.
      rewrite nth_replace, nat_bitvector_big_inv;
      [ rewrite eq; reflexivity | apply pureOp_read_correct_lem ].
    Qed.

    Theorem pureOp_read_correct_aux_updt (ri : regId) (m : MachineState) :
      forall x xs,
      tapeAux m = List.cons x xs ->
      tapeAux (pureOp_read ri (nat_bitvector_big _ 1) m) = xs.
    Proof.
      destruct m; simpl; intros x xs eq.
      rewrite nat_bitvector_big_inv;
      [ rewrite eq; reflexivity | apply pureOp_read_correct_lem ].
    Qed.

    Theorem pureOp_read_correct_oob (ri : regId) (m : MachineState) :
      forall n, 1 < n < 2 ^ wordSize ->
      nth (registers (pureOp_read ri (nat_bitvector_big _ n) m)) ri
      = const b0 _.
    Proof.
      destruct m; simpl; intros n [n1 n2p].
      rewrite nth_replace, nat_bitvector_big_inv; [ | assumption ].
      replace n with (S (S (n - 2))); [ reflexivity | lia ].
    Qed.

    Theorem pureOp_read_correct_flag_main_0 (ri : regId) (m : MachineState) :
      forall x xs,
      tapeMain m = List.cons x xs ->
      flag (pureOp_read ri (nat_bitvector_big _ 0) m) = b0.
    Proof.
      destruct m; simpl; intros x xs eq.
      rewrite nat_bitvector_big_inv;
      [ rewrite eq; reflexivity | apply zero2pow ].
    Qed.

    Theorem pureOp_read_correct_flag_main_1 (ri : regId) (m : MachineState) :
      tapeMain m = List.nil ->
      flag (pureOp_read ri (nat_bitvector_big _ 0) m) = b1.
    Proof.
      destruct m; simpl; intro eq.
      rewrite nat_bitvector_big_inv;
      [ rewrite eq; reflexivity | apply zero2pow ].
    Qed.

    Theorem pureOp_read_correct_flag_aux_0 (ri : regId) (m : MachineState) :
      forall x xs,
      tapeAux m = List.cons x xs ->
      flag (pureOp_read ri (nat_bitvector_big _ 1) m) = b0.
    Proof.
      destruct m; simpl; intros x xs eq.
      rewrite nat_bitvector_big_inv;
      [ rewrite eq; reflexivity | apply pureOp_read_correct_lem ].
    Qed.

    Theorem pureOp_read_correct_flag_aux_1 (ri : regId) (m : MachineState) :
      tapeAux m = List.nil ->
      flag (pureOp_read ri (nat_bitvector_big _ 1) m) = b1.
    Proof.
      destruct m; simpl; intro eq.
      rewrite nat_bitvector_big_inv;
      [ rewrite eq; reflexivity | apply pureOp_read_correct_lem ].
    Qed.

    Theorem pureOp_read_correct_flag_oob (ri : regId) (m : MachineState) :
      forall n, 1 < n < 2 ^ wordSize ->
      flag (pureOp_read ri (nat_bitvector_big _ n) m) = b1.
    Proof.
      destruct m; simpl; intros n [n1 n2p].
      rewrite nat_bitvector_big_inv; [ | assumption ].
      replace n with (S (S (n - 2))); [ reflexivity | lia ].
    Qed.

    Theorem pureOp_read_interp_imm {S} (k: itree E S) (ri : regId) 
                                  (A : Word) (m : MachineState) :
    interp_machine (denote_instruction (readI ri, inl A) ;; k) m
    ≈ interp_machine k (pureOp_read ri A m).
    Proof. 
      tau_steps; destruct m; cbn.
      rewrite (bisimulation_is_eq _ _ (bind_ret_l _ _)).
      destruct (bitvector_nat_big A); tau_steps; cbn.
      - repeat change (ITree.subst ?k ?x) with (ITree.bind x k).
        repeat rewrite (bisimulation_is_eq _ _ (bind_ret_l _ _)).
        destruct tapeMain0; tau_steps; reflexivity.
      - destruct n; tau_steps; cbn.
        + repeat change (ITree.subst ?k ?x) with (ITree.bind x k).
          repeat rewrite (bisimulation_is_eq _ _ (bind_ret_l _ _)).
          destruct tapeAux0; tau_steps; reflexivity.
        + reflexivity. 
    Qed.

    Theorem pureOp_read_interp_reg {S} (k: itree E S) (ri A : regId) 
                                  (m : MachineState) :
    interp_machine (denote_instruction (readI ri, inr A) ;; k) m
    ≈ interp_machine k (pureOp_read ri (nth (registers m) A) m).
    Proof. 
      tau_steps; destruct m; cbn.
      repeat change (ITree.subst ?k ?x) with (ITree.bind x k);
      rewrite (bisimulation_is_eq _ _ (bind_ret_l _ _)).
      destruct (bitvector_nat_big (nth registers0 A)); tau_steps; cbn.
      - repeat change (ITree.subst ?k ?x) with (ITree.bind x k).
        repeat rewrite (bisimulation_is_eq _ _ (bind_ret_l _ _)).
        destruct tapeMain0; tau_steps; reflexivity.
      - destruct n; tau_steps; cbn.
        + repeat change (ITree.subst ?k ?x) with (ITree.bind x k).
          repeat rewrite (bisimulation_is_eq _ _ (bind_ret_l _ _)).
          destruct tapeAux0; tau_steps; reflexivity.
        + reflexivity. 
    Qed.

    (*When a program runs out of steps to run it halts with no answer*)
    Lemma interp_machine_run_for_halt_0:
      forall (s : MachineState),
        interp_machine (E := E') (run_for 0) s ≈ Ret (s, None).
    Proof.
      intros.
      tau_steps; reflexivity.
    Qed.

    (* When the program reaches an immediate answer, it halts. *)
    Lemma interp_machine_run_halt_imm:
      forall (s : MachineState) op r,
        (List.nth_error (program s)
                        (bitvector_nat_big (programCounter s)))
        = Some r ->
        uncurry InstructionDecode r = (answerI, inl op) ->
        interp_machine (E := E') run s ≈ Ret (s, op).
    Proof.
      intros.
      unfold run; rewrite unfold_iter; unfold run_step at 1.
      do 2 (rewrite interp_machine_bind); rewrite interp_machine_trigger.
      assert (machine_h (E := E') _ (subevent _ GetPC) s
        ≈ Ret (s, programCounter s)) as AH;
      [ tau_steps; reflexivity | ]; rewrite AH; clear AH.
      rewrite bind_ret_l; change bind with (ITree.bind (E := E) (T := Word * Word) (U := unit + Word));
      rewrite interp_machine_bind, interp_machine_trigger.
      assert (machine_h (E := E') _ (subevent _ (ReadInst (bitvector_nat_big (programCounter s)))) s
        ≈ Ret (s, r)) as AH;
      [ tau_steps; repeat change (ITree.subst ?k ?x) with (ITree.bind x k);
        rewrite (bisimulation_is_eq _ _ (bind_ret_l _ _)); rewrite H; reflexivity | ];
      rewrite AH; clear AH.
      rewrite bind_bind, bind_ret_l; rewrite H0.
      assert (interp_machine (E := E') (ITree.map (inr (A := unit)) (denote_operand (inl op))) s
        ≈ Ret (s, inr op)) as AH; [ tau_steps; reflexivity | ];
      rewrite AH; clear AH.
      rewrite bind_ret_l, interp_machine_ret.
      reflexivity.
    Qed.

    (* When the program reaches an immediate answer, it halts. *)
    Lemma interp_machine_run_for_halt_imm:
      forall n (s : MachineState) op r,
        (List.nth_error (program s)
                        (bitvector_nat_big (programCounter s)))
        = Some r ->
        uncurry InstructionDecode r = (answerI, inl op) ->
        interp_machine (E := E') (run_for (S n)) s ≈ Ret (s, Some op).
    Proof.
      intros.
      unfold run_for; rewrite unfold_iter; unfold run_step_lim, run_step at 1.
      do 3 (rewrite interp_machine_bind at 1); rewrite interp_machine_trigger.
      assert (machine_h (E := E') _ (subevent _ GetPC) s
        ≈ Ret (s, programCounter s)) as AH;
      [ tau_steps; reflexivity | ]; rewrite AH; clear AH.
      rewrite bind_ret_l; change bind with (ITree.bind (E := E) (T := Word * Word) (U := unit + Word));
      rewrite interp_machine_bind, interp_machine_trigger.
      assert (machine_h (E := E') _ (subevent _ (ReadInst (bitvector_nat_big (programCounter s)))) s
        ≈ Ret (s, r)) as AH;
      [ tau_steps; repeat change (ITree.subst ?k ?x) with (ITree.bind x k);
        rewrite (bisimulation_is_eq _ _ (bind_ret_l _ _)); rewrite H; reflexivity | ];
      rewrite AH; clear AH.
      rewrite bind_bind, bind_ret_l; rewrite H0.
      assert (interp_machine (E := E') (ITree.map (inr (A := unit)) (denote_operand (inl op))) s
        ≈ Ret (s, inr op)) as AH; [ tau_steps; reflexivity | ];
      rewrite AH; clear AH.
      rewrite bind_ret_l.
      tau_steps; reflexivity.
    Qed.

    (* When run gets a register answer, it halts with that value. *)
    Lemma interp_machine_run_halt_reg:
      forall (s : MachineState) op r,
        (List.nth_error (program s)
                        (bitvector_nat_big (programCounter s)))
        = Some r ->
        uncurry InstructionDecode r = (answerI, inr op) ->
        interp_machine (E := E') run s ≈ Ret (s, nth (registers s) op).
    Proof.
      intros.
      unfold run; rewrite unfold_iter; unfold run_step at 1.
      do 2 (rewrite interp_machine_bind); rewrite interp_machine_trigger.
      assert (machine_h (E := E') _ (subevent _ GetPC) s
        ≈ Ret (s, programCounter s)) as AH;
      [ tau_steps; reflexivity | ]; rewrite AH; clear AH.
      rewrite bind_ret_l; change bind with (ITree.bind (E := E) (T := Word * Word) (U := unit + Word));
      rewrite interp_machine_bind, interp_machine_trigger.
      assert (machine_h (E := E') _ (subevent _ (ReadInst (bitvector_nat_big (programCounter s)))) s
        ≈ Ret (s, r)) as AH;
      [ tau_steps; repeat change (ITree.subst ?k ?x) with (ITree.bind x k);
        rewrite (bisimulation_is_eq _ _ (bind_ret_l _ _)); rewrite H; reflexivity | ];
      rewrite AH; clear AH.
      rewrite bind_bind, bind_ret_l; rewrite H0.
      assert (interp_machine (E := E') (ITree.map (inr (A := unit)) (denote_operand (inr op))) s
        ≈ Ret (s, inr (nth (registers s) op))) as AH; [ tau_steps; reflexivity | ];
      rewrite AH; clear AH.
      rewrite bind_ret_l, interp_machine_ret.
      reflexivity.
    Qed.
 
    (* When run gets a register answer, it halts with that value. *)
    Lemma interp_machine_run_for_halt_reg:
      forall n (s : MachineState) op r,
        (List.nth_error (program s)
                        (bitvector_nat_big (programCounter s)))
        = Some r ->
        uncurry InstructionDecode r = (answerI, inr op) ->
        interp_machine (E := E') (run_for (S n)) s ≈ Ret (s, Some (nth (registers s) op)).
    Proof.
      intros.
      unfold run_for; rewrite unfold_iter; unfold run_step_lim, run_step at 1.
      do 3 (rewrite interp_machine_bind); rewrite interp_machine_trigger.
      assert (machine_h (E := E') _ (subevent _ GetPC) s
        ≈ Ret (s, programCounter s)) as AH;
      [ tau_steps; reflexivity | ]; rewrite AH; clear AH.
      rewrite bind_ret_l; change bind with (ITree.bind (E := E) (T := Word * Word) (U := unit + Word));
      rewrite interp_machine_bind, interp_machine_trigger.
      assert (machine_h (E := E') _ (subevent _ (ReadInst (bitvector_nat_big (programCounter s)))) s
        ≈ Ret (s, r)) as AH;
      [ tau_steps; repeat change (ITree.subst ?k ?x) with (ITree.bind x k);
        rewrite (bisimulation_is_eq _ _ (bind_ret_l _ _)); rewrite H; reflexivity | ];
      rewrite AH; clear AH.
      rewrite bind_bind, bind_ret_l; rewrite H0.
      assert (interp_machine (E := E') (ITree.map (inr (A := unit)) (denote_operand (inr op))) s
        ≈ Ret (s, inr (nth (registers s) op))) as AH; [ tau_steps; reflexivity | ];
      rewrite AH; clear AH.
      rewrite bind_ret_l.
      tau_steps; reflexivity.
    Qed.

    Lemma interp_machine_run_step:
      forall (s : MachineState) k op r,
        (List.nth_error (program s)
                        (bitvector_nat_big (programCounter s)))
        = Some r ->
        uncurry InstructionDecode r = (k, op) ->
        k <> answerI ->
        interp_machine (E := E') run s ≈
        interp_machine (denote_instruction (k, op) ;; run) s.
    Proof.
      intros.
      unfold run; rewrite unfold_iter; unfold run_step at 1.
      do 2 (rewrite interp_machine_bind); rewrite interp_machine_trigger.
      assert (machine_h (E := E') _ (subevent _ GetPC) s
        ≈ Ret (s, programCounter s)) as AH;
      [ tau_steps; reflexivity | ]; rewrite AH; clear AH.
      rewrite bind_ret_l;
      change bind with (ITree.bind (E := E) (T := Word * Word) (U := unit + Word)) at 1;
      rewrite interp_machine_bind, interp_machine_trigger.
      assert (machine_h (E := E') _ (subevent _ (ReadInst (bitvector_nat_big (programCounter s)))) s
        ≈ Ret (s, r)) as AH;
      [ tau_steps; repeat change (ITree.subst ?k ?x) with (ITree.bind x k);
        rewrite (bisimulation_is_eq _ _ (bind_ret_l _ _)); rewrite H; reflexivity | ];
      rewrite AH; clear AH.
      rewrite bind_bind, bind_ret_l. rewrite H0.
      remember (interp_machine _) as gg;
      replace gg with (interp_machine (E := E') (ITree.map (inl (B := Word)) (denote_instruction (k, op))));
      [ | rewrite Heqgg; f_equal; destruct k; try reflexivity; contradiction ]; clear Heqgg gg.
      unfold ITree.map.
      rewrite interp_machine_bind, bind_bind.
      change bind with (ITree.bind (E := E) (T := unit) (U := Word)).
      rewrite interp_machine_bind.
      apply eqit_bind; [ reflexivity | ].
      intros [s2 []].
      rewrite interp_machine_ret, bind_ret_l.
      rewrite tau_eutt.
      reflexivity.
    Qed.

    Lemma interp_machine_run_for_step:
      forall n (s : MachineState) k op r,
        (List.nth_error (program s)
                        (bitvector_nat_big (programCounter s)))
        = Some r ->
        uncurry InstructionDecode r = (k, op) ->
        k <> answerI ->
        interp_machine (E := E') (run_for (S n)) s ≈
        interp_machine (denote_instruction (k, op) ;; run_for n) s.
    Proof.
      intros.
      unfold run_for; rewrite unfold_iter; unfold run_step_lim, run_step at 1.
      do 3 (rewrite interp_machine_bind); rewrite interp_machine_trigger.
      assert (machine_h (E := E') _ (subevent _ GetPC) s
        ≈ Ret (s, programCounter s)) as AH;
      [ tau_steps; reflexivity | ]; rewrite AH; clear AH.
      rewrite bind_ret_l;
      change bind with (ITree.bind (E := E) (T := Word * Word) (U := unit + Word)) at 1;
      rewrite interp_machine_bind, interp_machine_trigger.
      assert (machine_h (E := E') _ (subevent _ (ReadInst (bitvector_nat_big (programCounter s)))) s
        ≈ Ret (s, r)) as AH;
      [ tau_steps; repeat change (ITree.subst ?k ?x) with (ITree.bind x k);
        rewrite (bisimulation_is_eq _ _ (bind_ret_l _ _)); rewrite H; reflexivity | ];
      rewrite AH; clear AH.
      rewrite bind_bind, bind_ret_l. rewrite H0.
      remember (interp_machine _) as gg;
      replace gg with (interp_machine (E := E') (ITree.map (inl (B := Word)) (denote_instruction (k, op))));
      [ | rewrite Heqgg; f_equal; destruct k; try reflexivity; contradiction ]; clear Heqgg gg.
      unfold ITree.map.
      rewrite interp_machine_bind, bind_bind.
      change bind with (ITree.bind (E := E) (T := unit) (U := Word)).
      rewrite interp_machine_bind.
      apply eqit_bind; [ reflexivity | ].
      intros [s2 []].
      rewrite interp_machine_ret, bind_ret_l.
      tau_steps; reflexivity.
    Qed.

  End with_event.

End TinyRAMInstThm.
