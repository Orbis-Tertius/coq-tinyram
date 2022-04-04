From Coq Require Import
  Lia Nat VectorDef VectorEq ProofIrrelevance FunctionalExtensionality.
Import VectorNotations.
From TinyRAM.Utils Require Import
  Vectors BitVectors Fin Arith.
Import PeanoNat.Nat(log2_up, ltb_lt).
From TinyRAM.Machine Require Import
  Parameters Words.

Module TinyRAMCoding (Params : TinyRAMParameters).
  Module TRWords := TinyRAMWords Params.
  Import TRWords.

  Definition paddingSize := wordSize - 6 - 2 * log2_up registerCount.

  Theorem interpSplitLemLeft : 
    wordSize =
      5 + 1 + (log2_up registerCount) + (log2_up registerCount) +
      paddingSize.
    assert (6 + 2 * log2_up registerCount <= wordSize).
    { apply encodingAxiom. }
    unfold paddingSize; lia.
  Qed.

  Lemma interpSplitLemRight : 
    wordSize =
    5 + (1 + ((log2_up registerCount) + ((log2_up registerCount) + paddingSize))).
  Proof.
    rewrite interpSplitLemLeft.
    lia.
  Qed.

  Definition interpSplit : Word ->
    (*"""
    Field #1. This field stores the instruction's opcode,
              which consists of 5 = (log2_up 29) bits.
    """*)
    Vector.t bool 5 * 
    (*"""
    Field #2. This field is a bit that is 0 if A is a
              register name and 1 if A is an immediate value.
    """*)
    bool * 
    (*"""
    Field #3. This field stores a register name operand, which consists
              of (log2_up [registerCount]) bits. It is all 0's when not
              used. This is the name of the instruction's destination
              register (i.e. the one to be modified) if any.
    """*)
    Vector.t bool (log2_up registerCount) *
    (*"""
    Field #4. This field stores a register name operand, which consists
              of (log2_up [registerCount]) bits. It is all 0's when not
              used. This is the name of a register operand (if any) that
              will *not* be modified by the instruction.
    """*)
    Vector.t bool (log2_up registerCount) *
    (*"""
    Field #5. This field consists of padding with any sequence of 
              W - 6 - 2|K| bits, so that the first five fields fit exactly
              in a string of W bits.
    """*)
    Vector.t bool paddingSize.
    intro w.
    unfold Word in w.
    rewrite interpSplitLemLeft in w.
    apply Vector.splitat in w; destruct w as [w f5].
    split. 2: { exact f5. }
    apply Vector.splitat in w; destruct w as [w f4].
    split. 2: { exact f4. }
    apply Vector.splitat in w; destruct w as [w f3].
    split. 2: { exact f3. }
    apply Vector.splitat in w; destruct w as [f1 f2].
    split. { exact f1. }
    destruct (vector_cons_split f2) as [b _].
    exact b.
  Defined.

  Theorem interpSplit_eval :
    forall (code : Vector.t bool 5)
           (b : bool)
           (ri rj : Vector.t bool (log2_up registerCount))
           (padding : Vector.t bool paddingSize),
    interpSplit (cast (code ++ [b] ++ ri ++ rj ++ padding
    ) (eq_sym interpSplitLemRight)) = (code, b, ri, rj, padding).
  Proof.
    intros code b ri rj padding.
    unfold interpSplit.
    replace (eq_rect _ _ _ _ _)
        with ((((code ++ [b]) ++ ri) ++ rj) ++ padding).
    { repeat rewrite Vector.splitat_append; reflexivity. }
    rewrite <- cast_rew.
    rewrite cast_trans.
    vector_simp.
    f_equal; apply proof_irrelevance.
  Qed.

  Variant OpcodeI : Type :=
  | andI : regId -> regId -> OpcodeI
  | orI : regId -> regId -> OpcodeI
  | xorI : regId -> regId -> OpcodeI
  | notI : regId -> OpcodeI
  | addI : regId -> regId -> OpcodeI
  | subI : regId -> regId -> OpcodeI
  | mullI : regId -> regId -> OpcodeI
  | umulhI : regId -> regId -> OpcodeI
  | smulhI : regId -> regId -> OpcodeI
  | udivI : regId -> regId -> OpcodeI
  | umodI : regId -> regId -> OpcodeI
  | shlI : regId -> regId -> OpcodeI
  | shrI : regId -> regId -> OpcodeI
  | cmpeI : regId -> OpcodeI
  | cmpaI : regId -> OpcodeI
  | cmpaeI : regId -> OpcodeI
  | cmpgI : regId -> OpcodeI
  | cmpgeI : regId -> OpcodeI
  | movI : regId -> OpcodeI
  | cmovI : regId -> OpcodeI
  | jmpI : OpcodeI
  | cjmpI : OpcodeI
  | cnjmpI : OpcodeI
  | store_bI : regId -> OpcodeI
  | load_bI : regId -> OpcodeI
  | store_wI : regId -> OpcodeI
  | load_wI : regId -> OpcodeI
  | readI : regId -> OpcodeI
  | answerI : OpcodeI.

  Definition operand : Type := Word + regId.

  Definition Opcode : Type := OpcodeI * operand.

  Definition ijTr (con : regId -> regId -> OpcodeI)
                   (ri rj : regId) (A : operand) : Opcode := (con ri rj, A).

  Definition iTr (con : regId -> OpcodeI)
                   (ri : regId) (A : operand) : Opcode := (con ri, A).

  Definition Tr (con : OpcodeI) (A : operand) : Opcode := (con, A).

  Definition oreg {n} (v : Vector.t bool n) : option regId.
    destruct (bitvector_fin_big v).
    destruct (x <? registerCount) eqn:xlt.
    - apply Some. 
      exists x.
      rewrite ltb_lt in xlt.
      assumption.
    - apply None.
  Defined.

  Definition reg2pow : 
    2 ^ log2_up registerCount = registerCount ->
    Vector.t bool (log2_up registerCount) ->
    regId.
    intros eq v.
    destruct (bitvector_fin_big v).
    rewrite eq in l.
    exists x.
    exact l.
  Defined.

  Lemma reg2powProp_lem :
    forall {B} {P : B -> Prop}
      (e : bool) (el : B) (f : e = true -> P el) (f' : P el),
    e = true ->
    ( if e as b
      return (e = b -> option {x : B | P x})
      then fun xlt : e = true => 
        Some (exist (fun x : B => P x) el (f xlt))
      else fun _ : e = false => None )
    = fun _ => Some (exist (fun x : B => P x) el f').
  Proof.
    intros B P e el f f' etru.
    apply functional_extensionality.
    intro ee.
    destruct e.
    - f_equal. 
      apply subset_eq_compat.
      reflexivity.
    - discriminate etru.
  Qed.

  Theorem oreg2powProp : forall
    (eq: 2 ^ log2_up registerCount = registerCount)
    (v: Vector.t bool (log2_up registerCount)),
    oreg v = Some (reg2pow eq v).
  Proof.
    intros eq v.
    unfold oreg, reg2pow.
    destruct (bitvector_fin_big v) as [bfv bfvProp].
    assert (bfv < registerCount) as bfvRC.
    { rewrite <- eq. assumption. }
    unfold regId, fin.
    rewrite (reg2powProp_lem (bfv <? registerCount) bfv _ bfvRC).
    2: { rewrite ltb_lt. assumption. }
    f_equal.
    apply subset_eq_compat.
    reflexivity.
  Qed.

  Definition regFit :
    forall {n} (v : Vector.t bool n),
    proj1_sig (bitvector_fin_big v) < registerCount -> 
    regId.
    intros n v ft.
    exists (proj1_sig (bitvector_fin_big v)).
    exact ft.
  Defined.

  Theorem regFitProp :
    forall {n} (v : Vector.t bool n)
    (lt : proj1_sig (bitvector_fin_big v) < registerCount),
    oreg v = Some (regFit v lt).
  Proof.
    intros n v lt.
    unfold oreg, regFit.
    destruct (bitvector_fin_big v) as [bfv bfvProp].
    simpl; simpl in lt.
    unfold regId, fin.
    rewrite (reg2powProp_lem (bfv <? registerCount) bfv _ lt).
    { reflexivity. }
    rewrite ltb_lt.
    exact lt.
  Qed.

  Definition answer1 : Opcode.
    split.
    - apply answerI.
    - apply inl, fin_bitvector_big.
      exists 1.
      transitivity wordSize.
      2: { apply PeanoNat.Nat.pow_gt_lin_r. lia. }
      assert (5 < wordSize). { apply wordSizeMin5. }
      lia.
  Defined.

  (* Important Note: The TinyRAM 2.000 spec does not seem to
     clearify what should be done if a register address is too
     big. I've made the opcode answer1 in this case, but this
     may not be intended behaviour.

     Such a situation is impossible if registerCount is a 
     power of 2 (see oreg2powProp above), except for decoding
     a word into a register address, which may be too big
     anyway.
  *)
  Definition OpcodeDecodeA : forall
    (code : operand -> Opcode)
    (isReg : bool) (w2: Word) (w2reg: option regId),
    Opcode.
    intros code isReg w2 w2reg.
    destruct isReg.
    + exact (code (inl w2)).
    + destruct w2reg as [w2reg|]. 2: { exact answer1. }
      exact (code (inr w2reg)).
  Defined.

  Definition OpcodeDecodeRiA : forall
    (code : regId -> operand -> Opcode)
    (isReg : bool) (ri : option regId)
    (w2: Word) (w2reg: option regId),
    Opcode.
    intros code isReg ri w2 w2reg.
    destruct ri as [ri|]. 2: { exact answer1. }
    destruct isReg.
    + exact (code ri (inl w2)).
    + destruct w2reg as [w2reg|]. 2: { exact answer1. }
      exact (code ri (inr w2reg)).
  Defined.

  Definition OpcodeDecodeRiRjA : forall
    (code : regId -> regId -> operand -> Opcode)
    (isReg : bool) (ri rj : option regId)
    (w2: Word) (w2reg: option regId),
    Opcode.
    intros code isReg ri rj w2 w2reg.
    destruct ri as [ri|]. 2: { exact answer1. }
    destruct rj as [rj|]. 2: { exact answer1. }
    destruct isReg.
    + exact (code ri rj (inl w2)).
    + destruct w2reg as [w2reg|]. 2: { exact answer1. }
      exact (code ri rj (inr w2reg)).
  Defined.

 (*"""
  the instruction is thus encoded using 2W bits
  """

  """
    Field #6. This is either the name of another register (which is not
              modified by the instruction) or an immediate value, as
              determined by field #2. The length of this field is W bits
              (which is the maximum between the length of a register name
              and of an immediate value).
  """*)
  Definition OpcodeDecode (w1 w2 : Word) : Opcode :=
    match interpSplit w1 with
    | (op, isReg, pri, prj, _) =>
      let ri := oreg pri in
      let rj := oreg prj in
      let ow := oreg w2 in
      match proj1_sig (bitvector_fin_big op) with
      | 0 =>  OpcodeDecodeRiRjA (ijTr andI  ) isReg ri rj w2 ow
      | 1 =>  OpcodeDecodeRiRjA (ijTr orI   ) isReg ri rj w2 ow
      | 2 =>  OpcodeDecodeRiRjA (ijTr xorI  ) isReg ri rj w2 ow
      | 3 =>  OpcodeDecodeRiA   (iTr  notI  ) isReg ri w2 ow
      | 4 =>  OpcodeDecodeRiRjA (ijTr addI  ) isReg ri rj w2 ow
      | 5 =>  OpcodeDecodeRiRjA (ijTr subI  ) isReg ri rj w2 ow
      | 6 =>  OpcodeDecodeRiRjA (ijTr mullI ) isReg ri rj w2 ow
      | 7 =>  OpcodeDecodeRiRjA (ijTr umulhI) isReg ri rj w2 ow
      | 8 =>  OpcodeDecodeRiRjA (ijTr smulhI) isReg ri rj w2 ow
      | 9 =>  OpcodeDecodeRiRjA (ijTr udivI ) isReg ri rj w2 ow
      | 10 => OpcodeDecodeRiRjA (ijTr umodI ) isReg ri rj w2 ow
      | 11 => OpcodeDecodeRiRjA (ijTr shlI  ) isReg ri rj w2 ow
      | 12 => OpcodeDecodeRiRjA (ijTr shrI  ) isReg ri rj w2 ow
      | 13 => OpcodeDecodeRiA   (iTr  cmpeI ) isReg rj w2 ow
      | 14 => OpcodeDecodeRiA   (iTr  cmpaI ) isReg rj w2 ow
      | 15 => OpcodeDecodeRiA   (iTr  cmpaeI) isReg rj w2 ow
      | 16 => OpcodeDecodeRiA   (iTr  cmpgI ) isReg rj w2 ow
      | 17 => OpcodeDecodeRiA   (iTr  cmpgeI) isReg rj w2 ow
      | 18 => OpcodeDecodeRiA   (iTr  movI  ) isReg ri w2 ow
      | 19 => OpcodeDecodeRiA   (iTr  cmovI ) isReg ri w2 ow
      | 20 => OpcodeDecodeA     (Tr   jmpI  ) isReg w2 ow
      | 21 => OpcodeDecodeA     (Tr   cjmpI ) isReg w2 ow
      | 22 => OpcodeDecodeA     (Tr   cnjmpI) isReg w2 ow
      | 23 => answer1
      | 24 => answer1
      | 25 => answer1
      | 26 => OpcodeDecodeRiA (iTr   store_bI) isReg ri w2 ow
      | 27 => OpcodeDecodeRiA (iTr   load_bI ) isReg ri w2 ow
      | 28 => OpcodeDecodeRiA (iTr   store_wI) isReg ri w2 ow
      | 29 => OpcodeDecodeRiA (iTr   load_wI ) isReg ri w2 ow
      | 30 => OpcodeDecodeRiA (iTr   readI   ) isReg ri w2 ow
      | 31 => OpcodeDecodeA   (Tr    answerI ) isReg w2 ow
      | _ => answer1
      end
    end.

  (***
    This section is based on Table 2 of pg. 16 in spec. 
  ***)

  Ltac rirjAProof_register :=
    intros ri rj lti ltj A ltA padding;
    unfold OpcodeDecode; rewrite interpSplit_eval;
    unfold bitvector_fin_big; vector_simp; simpl;
    rewrite (regFitProp ri lti), (regFitProp rj ltj), (regFitProp A ltA);
    reflexivity.

  Ltac rirjAProof_word :=
    intros ri rj lti ltj A padding;
    unfold OpcodeDecode; rewrite interpSplit_eval;
    unfold bitvector_fin_big; vector_simp; simpl;
    rewrite (regFitProp ri lti), (regFitProp rj ltj);
    reflexivity.

  Ltac riAProof_register :=
    intros ri pad lti A ltA padding;
    unfold OpcodeDecode; rewrite interpSplit_eval;
    unfold bitvector_fin_big; vector_simp; simpl;
    rewrite (regFitProp ri lti), (regFitProp A ltA);
    reflexivity.

  Ltac riAProof_word :=
    intros ri pad lti A padding;
    unfold OpcodeDecode; rewrite interpSplit_eval;
    unfold bitvector_fin_big; vector_simp; simpl;
    rewrite (regFitProp ri lti);
    reflexivity.

  Ltac rjAProof_register :=
    intros pad ri lti A ltA padding;
    unfold OpcodeDecode; rewrite interpSplit_eval;
    unfold bitvector_fin_big; vector_simp; simpl;
    rewrite (regFitProp ri lti), (regFitProp A ltA);
    reflexivity.

  Ltac rjAProof_word :=
    intros pad ri lti A padding;
    unfold OpcodeDecode; rewrite interpSplit_eval;
    unfold bitvector_fin_big; vector_simp; simpl;
    rewrite (regFitProp ri lti);
    reflexivity.

  Ltac AProof_register :=
    intros pad1 pad2 A ltA padding;
    unfold OpcodeDecode; rewrite interpSplit_eval;
    unfold bitvector_fin_big; vector_simp; simpl;
    rewrite (regFitProp A ltA);
    reflexivity.

  Ltac AProof_word :=
    intros pad1 pad2 A padding;
    unfold OpcodeDecode; rewrite interpSplit_eval;
    unfold bitvector_fin_big; vector_simp; simpl;
    reflexivity.

  Definition and_code := [b0; b0; b0; b0; b0].

  Theorem and_decode_register_correct :
    forall (ri rj : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (and_code ++ [b0] ++ ri ++ rj ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (andI (regFit ri lti) (regFit rj ltj), inr (regFit A ltA)).
  Proof. unfold and_code. rirjAProof_register. Qed.
 
  Theorem and_decode_word_correct :
    forall (ri rj : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (and_code ++ [b1] ++ ri ++ rj ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (andI (regFit ri lti) (regFit rj ltj), inl A).
  Proof. unfold and_code. rirjAProof_word. Qed.

Definition or_code := [b0; b0; b0; b0; b1].

Theorem or_decode_register_correct :
    forall (ri rj : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (or_code ++ [b0] ++ ri ++ rj ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (orI (regFit ri lti) (regFit rj ltj), inr (regFit A ltA)).
  Proof. unfold or_code. rirjAProof_register. Qed.
 
  Theorem or_decode_word_correct :
    forall (ri rj : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (or_code ++ [b1] ++ ri ++ rj ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (orI (regFit ri lti) (regFit rj ltj), inl A).
  Proof. unfold or_code. rirjAProof_word. Qed.

  Definition xor_code := [b0; b0; b0; b1; b0].

  Theorem xor_decode_register_correct :
    forall (ri rj : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (xor_code ++ [b0] ++ ri ++ rj ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (xorI (regFit ri lti) (regFit rj ltj), inr (regFit A ltA)).
  Proof. unfold xor_code. rirjAProof_register. Qed.
 
  Theorem xor_decode_word_correct :
    forall (ri rj : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (xor_code ++ [b1] ++ ri ++ rj ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (xorI (regFit ri lti) (regFit rj ltj), inl A).
  Proof. unfold xor_code. rirjAProof_word. Qed.

  Definition not_code := [b0; b0; b0; b1; b1].

  Theorem not_decode_register_correct :
    forall (ri pad : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (not_code ++ [b0] ++ ri ++ pad ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (notI (regFit ri lti), inr (regFit A ltA)).
  Proof. unfold not_code. riAProof_register. Qed.
 
  Theorem not_decode_word_correct :
    forall (ri pad : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (not_code ++ [b1] ++ ri ++ pad ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (notI (regFit ri lti), inl A).
  Proof. unfold not_code. riAProof_word. Qed.

  Definition add_code := [b0; b0; b1; b0; b0].

  Theorem add_decode_register_correct :
    forall (ri rj : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (add_code ++ [b0] ++ ri ++ rj ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (addI (regFit ri lti) (regFit rj ltj), inr (regFit A ltA)).
  Proof. unfold add_code. rirjAProof_register. Qed.
 
  Theorem add_decode_word_correct :
    forall (ri rj : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (add_code ++ [b1] ++ ri ++ rj ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (addI (regFit ri lti) (regFit rj ltj), inl A).
  Proof. unfold add_code. rirjAProof_word. Qed.

  Definition sub_code := [b0; b0; b1; b0; b1].

  Theorem sub_decode_register_correct :
    forall (ri rj : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (sub_code ++ [b0] ++ ri ++ rj ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (subI (regFit ri lti) (regFit rj ltj), inr (regFit A ltA)).
  Proof. unfold sub_code. rirjAProof_register. Qed.
 
  Theorem sub_decode_word_correct :
    forall (ri rj : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (sub_code ++ [b1] ++ ri ++ rj ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (subI (regFit ri lti) (regFit rj ltj), inl A).
  Proof. unfold sub_code. rirjAProof_word. Qed.

  Definition mull_code := [b0; b0; b1; b1; b0].

  Theorem mull_decode_register_correct :
    forall (ri rj : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (mull_code ++ [b0] ++ ri ++ rj ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (mullI (regFit ri lti) (regFit rj ltj), inr (regFit A ltA)).
  Proof. unfold mull_code. rirjAProof_register. Qed.
 
  Theorem mull_decode_word_correct :
    forall (ri rj : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (mull_code ++ [b1] ++ ri ++ rj ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (mullI (regFit ri lti) (regFit rj ltj), inl A).
  Proof. unfold mull_code. rirjAProof_word. Qed.

  Definition umulh_code := [b0; b0; b1; b1; b1].

  Theorem umulh_decode_register_correct :
    forall (ri rj : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (umulh_code ++ [b0] ++ ri ++ rj ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (umulhI (regFit ri lti) (regFit rj ltj), inr (regFit A ltA)).
  Proof. unfold umulh_code. rirjAProof_register. Qed.
 
  Theorem umulh_decode_word_correct :
    forall (ri rj : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (umulh_code ++ [b1] ++ ri ++ rj ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (umulhI (regFit ri lti) (regFit rj ltj), inl A).
  Proof. unfold umulh_code. rirjAProof_word. Qed.

  Definition smulh_code := [b0; b1; b0; b0; b0].

  Theorem smulh_decode_register_correct :
    forall (ri rj : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (smulh_code ++ [b0] ++ ri ++ rj ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (smulhI (regFit ri lti) (regFit rj ltj), inr (regFit A ltA)).
  Proof. unfold smulh_code. rirjAProof_register. Qed.
 
  Theorem smulh_decode_word_correct :
    forall (ri rj : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (smulh_code ++ [b1] ++ ri ++ rj ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (smulhI (regFit ri lti) (regFit rj ltj), inl A).
  Proof. unfold smulh_code. rirjAProof_word. Qed.

  Definition udiv_code := [b0; b1; b0; b0; b1].

  Theorem udiv_decode_register_correct :
    forall (ri rj : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (udiv_code ++ [b0] ++ ri ++ rj ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (udivI (regFit ri lti) (regFit rj ltj), inr (regFit A ltA)).
  Proof. unfold udiv_code. rirjAProof_register. Qed.
 
  Theorem udiv_decode_word_correct :
    forall (ri rj : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (udiv_code ++ [b1] ++ ri ++ rj ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (udivI (regFit ri lti) (regFit rj ltj), inl A).
  Proof. unfold udiv_code. rirjAProof_word. Qed.

  Definition umod_code := [b0; b1; b0; b1; b0].

  Theorem umod_decode_register_correct :
    forall (ri rj : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (umod_code ++ [b0] ++ ri ++ rj ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (umodI (regFit ri lti) (regFit rj ltj), inr (regFit A ltA)).
  Proof. unfold umod_code. rirjAProof_register. Qed.
 
  Theorem umod_decode_word_correct :
    forall (ri rj : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (umod_code ++ [b1] ++ ri ++ rj ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (umodI (regFit ri lti) (regFit rj ltj), inl A).
  Proof. unfold umod_code. rirjAProof_word. Qed.

  Definition shl_code := [b0; b1; b0; b1; b1].

  Theorem shl_decode_register_correct :
    forall (ri rj : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (shl_code ++ [b0] ++ ri ++ rj ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (shlI (regFit ri lti) (regFit rj ltj), inr (regFit A ltA)).
  Proof. unfold shl_code. rirjAProof_register. Qed.
 
  Theorem shl_decode_word_correct :
    forall (ri rj : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (shl_code ++ [b1] ++ ri ++ rj ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (shlI (regFit ri lti) (regFit rj ltj), inl A).
  Proof. unfold shl_code. rirjAProof_word. Qed.

  Definition shr_code := [b0; b1; b1; b0; b0].

  Theorem shr_decode_register_correct :
    forall (ri rj : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (shr_code ++ [b0] ++ ri ++ rj ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (shrI (regFit ri lti) (regFit rj ltj), inr (regFit A ltA)).
  Proof. unfold shr_code. rirjAProof_register. Qed.
 
  Theorem shr_decode_word_correct :
    forall (ri rj : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (shr_code ++ [b1] ++ ri ++ rj ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (shrI (regFit ri lti) (regFit rj ltj), inl A).
  Proof. unfold shr_code. rirjAProof_word. Qed.

  Definition cmpe_code := [b0; b1; b1; b0; b1].

  Theorem cmpe_decode_register_correct :
    forall (pad ri : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (cmpe_code ++ [b0] ++ pad ++ ri ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (cmpeI (regFit ri lti), inr (regFit A ltA)).
  Proof. unfold cmpe_code. rjAProof_register. Qed.

  Theorem cmpe_decode_word_correct :
    forall (pad ri : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (cmpe_code ++ [b1] ++ pad ++ ri ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (cmpeI (regFit ri lti), inl A).
  Proof. unfold cmpe_code. rjAProof_word. Qed.

  Definition cmpa_code := [b0; b1; b1; b1; b0].

  Theorem cmpa_decode_register_correct :
    forall (pad ri : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (cmpa_code ++ [b0] ++ pad ++ ri ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (cmpaI (regFit ri lti), inr (regFit A ltA)).
  Proof. unfold cmpa_code. rjAProof_register. Qed.
 
  Theorem cmpa_decode_word_correct :
    forall (pad ri : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (cmpa_code ++ [b1] ++ pad ++ ri ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (cmpaI (regFit ri lti), inl A).
  Proof. unfold cmpa_code. rjAProof_word. Qed.

  Definition cmpae_code := [b0; b1; b1; b1; b1].

  Theorem cmpae_decode_register_correct :
    forall (pad ri : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (cmpae_code ++ [b0] ++ pad ++ ri ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (cmpaeI (regFit ri lti), inr (regFit A ltA)).
  Proof. unfold cmpae_code. rjAProof_register. Qed.
 
  Theorem cmpae_decode_word_correct :
    forall (pad ri : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (cmpae_code ++ [b1] ++ pad ++ ri ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (cmpaeI (regFit ri lti), inl A).
  Proof. unfold cmpae_code. rjAProof_word. Qed.

  Definition cmpg_code := [b1; b0; b0; b0; b0].

  Theorem cmpg_decode_register_correct :
    forall (pad ri : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (cmpg_code ++ [b0] ++ pad ++ ri ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (cmpgI (regFit ri lti), inr (regFit A ltA)).
  Proof. unfold cmpg_code. rjAProof_register. Qed.
 
  Theorem cmpg_decode_word_correct :
    forall (pad ri : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (cmpg_code ++ [b1] ++ pad ++ ri ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (cmpgI (regFit ri lti), inl A).
  Proof. unfold cmpg_code. rjAProof_word. Qed.

  Definition cmpge_code := [b1; b0; b0; b0; b1].

  Theorem cmpge_decode_register_correct :
    forall (pad ri : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (cmpge_code ++ [b0] ++ pad ++ ri ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (cmpgeI (regFit ri lti), inr (regFit A ltA)).
  Proof. unfold cmpge_code. rjAProof_register. Qed.
 
  Theorem cmpge_decode_word_correct :
    forall (pad ri : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (cmpge_code ++ [b1] ++ pad ++ ri ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (cmpgeI (regFit ri lti), inl A).
  Proof. unfold cmpge_code. rjAProof_word. Qed.

  Definition mov_code := [b1; b0; b0; b1; b0].

  Theorem mov_decode_register_correct :
    forall (ri pad : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (mov_code ++ [b0] ++ ri ++ pad ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (movI (regFit ri lti), inr (regFit A ltA)).
  Proof. unfold mov_code. riAProof_register. Qed.

  Theorem mov_decode_word_correct :
    forall (ri pad : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (mov_code ++ [b1] ++ ri ++ pad ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (movI (regFit ri lti), inl A).
  Proof. unfold mov_code. riAProof_word. Qed.

  Definition cmov_code := [b1; b0; b0; b1; b1].

  Theorem cmov_decode_register_correct :
    forall (ri pad : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (cmov_code ++ [b0] ++ ri ++ pad ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (cmovI (regFit ri lti), inr (regFit A ltA)).
  Proof. unfold cmov_code. riAProof_register. Qed.
 
  Theorem cmov_decode_word_correct :
    forall (ri pad : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (cmov_code ++ [b1] ++ ri ++ pad ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (cmovI (regFit ri lti), inl A).
  Proof. unfold cmov_code. riAProof_word. Qed.

  Definition jmp_code := [b1; b0; b1; b0; b0].

  Theorem jmp_decode_register_correct :
    forall (pad1 pad2 : Vector.t bool (log2_up registerCount))
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (jmp_code ++ [b0] ++ pad1 ++ pad2 ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (jmpI, inr (regFit A ltA)).
  Proof. unfold jmp_code. AProof_register. Qed.
 
  Theorem jmp_decode_word_correct :
    forall (pad1 pad2 : Vector.t bool (log2_up registerCount))
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (jmp_code ++ [b1] ++ pad1 ++ pad2 ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (jmpI, inl A).
  Proof. unfold jmp_code. AProof_word. Qed.

  Definition cjmp_code := [b1; b0; b1; b0; b1].

  Theorem cjmp_decode_register_correct :
    forall (pad1 pad2 : Vector.t bool (log2_up registerCount))
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (cjmp_code ++ [b0] ++ pad1 ++ pad2 ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (cjmpI, inr (regFit A ltA)).
  Proof. unfold cjmp_code. AProof_register. Qed.
 
  Theorem cjmp_decode_word_correct :
    forall (pad1 pad2 : Vector.t bool (log2_up registerCount))
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (cjmp_code ++ [b1] ++ pad1 ++ pad2 ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (cjmpI, inl A).
  Proof. unfold cjmp_code. AProof_word. Qed.

  Definition cnjmp_code := [b1; b0; b1; b1; b0].

  Theorem cnjmp_decode_register_correct :
    forall (pad1 pad2 : Vector.t bool (log2_up registerCount))
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (cnjmp_code ++ [b0] ++ pad1 ++ pad2 ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (cnjmpI, inr (regFit A ltA)).
  Proof. unfold cnjmp_code. AProof_register. Qed.
 
  Theorem cnjmp_decode_word_correct :
    forall (pad1 pad2 : Vector.t bool (log2_up registerCount))
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (cnjmp_code ++ [b1] ++ pad1 ++ pad2 ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (cnjmpI, inl A).
  Proof. unfold cnjmp_code. AProof_word. Qed.

  Definition store_b_code := [b1; b1; b0; b1; b0].

  Theorem store_b_decode_register_correct :
    forall (ri pad : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (store_b_code ++ [b0] ++ ri ++ pad ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (store_bI (regFit ri lti), inr (regFit A ltA)).
  Proof. unfold store_b_code. riAProof_register. Qed.
 
  Theorem store_b_decode_word_correct :
    forall (ri pad : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (store_b_code ++ [b1] ++ ri ++ pad ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (store_bI (regFit ri lti), inl A).
  Proof. unfold store_b_code. riAProof_word. Qed.

  Definition load_b_code := [b1; b1; b0; b1; b1].

  Theorem load_b_decode_register_correct :
    forall (ri pad : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (load_b_code ++ [b0] ++ ri ++ pad ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (load_bI (regFit ri lti), inr (regFit A ltA)).
  Proof. unfold load_b_code. riAProof_register. Qed.
 
  Theorem load_b_decode_word_correct :
    forall (ri pad : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (load_b_code ++ [b1] ++ ri ++ pad ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (load_bI (regFit ri lti), inl A).
  Proof. unfold load_b_code. riAProof_word. Qed.

  Definition store_w_code := [b1; b1; b1; b0; b0].

  Theorem store_w_decode_register_correct :
    forall (ri pad : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (store_w_code ++ [b0] ++ ri ++ pad ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (store_wI (regFit ri lti), inr (regFit A ltA)).
  Proof. unfold store_w_code. riAProof_register. Qed.
 
  Theorem store_w_decode_word_correct :
    forall (ri pad : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (store_w_code ++ [b1] ++ ri ++ pad ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (store_wI (regFit ri lti), inl A).
  Proof. unfold store_w_code. riAProof_word. Qed.

  Definition load_w_code := [b1; b1; b1; b0; b1].

  Theorem load_w_decode_register_correct :
    forall (ri pad : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (load_w_code ++ [b0] ++ ri ++ pad ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (load_wI (regFit ri lti), inr (regFit A ltA)).
  Proof. unfold load_w_code. riAProof_register. Qed.
 
  Theorem load_w_decode_word_correct :
    forall (ri pad : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (load_w_code ++ [b1] ++ ri ++ pad ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (load_wI (regFit ri lti), inl A).
  Proof. unfold load_w_code. riAProof_word. Qed.

  Definition read_code := [b1; b1; b1; b1; b0].

  Theorem read_decode_register_correct :
    forall (ri pad : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (read_code ++ [b0] ++ ri ++ pad ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (readI (regFit ri lti), inr (regFit A ltA)).
  Proof. unfold read_code. riAProof_register. Qed.
 
  Theorem read_decode_word_correct :
    forall (ri pad : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (read_code ++ [b1] ++ ri ++ pad ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (readI (regFit ri lti), inl A).
  Proof. unfold read_code. riAProof_word. Qed.

  Definition answer_code := [b1; b1; b1; b1; b1].

  Theorem answer_decode_register_correct :
    forall (pad1 pad2 : Vector.t bool (log2_up registerCount))
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (answer_code ++ [b0] ++ pad1 ++ pad2 ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (answerI, inr (regFit A ltA)).
  Proof. unfold answer_code. AProof_register. Qed.
 
  Theorem answer_decode_word_correct :
    forall (pad1 pad2 : Vector.t bool (log2_up registerCount))
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (cast (answer_code ++ [b1] ++ pad1 ++ pad2 ++ padding)
                       (eq_sym interpSplitLemRight)) A =
    (answerI, inl A).
  Proof. unfold answer_code. AProof_word. Qed.

  Definition option_word : operand -> Word.
    intros [w|[rid ridp]].
    - exact w. 
    - apply fin_bitvector_big.
      exists rid.
      transitivity registerCount. { assumption. }
      apply registerCount_lt_2powwordSize2.
      lia.
  Defined.

  Definition option_bool (o : operand) : bool :=
    if o then b1 else b0.

  Definition reg_vect : regId -> t bool (log2_up registerCount).
    intros [r rprp].
    apply fin_bitvector_big.
    exists r.
    apply (PeanoNat.Nat.lt_le_trans _ registerCount). { assumption. }
    rewrite PeanoNat.Nat.log2_up_le_pow2; lia.
  Defined.

  Definition OpcodeEncode (o : Opcode) : Word * Word :=
    match o with
    | (andI ri rj, op) =>
      (cast (and_code ++ [option_bool op] ++ reg_vect ri ++ reg_vect rj ++ const b0 _)
            (eq_sym interpSplitLemRight),
      option_word op)
    | (orI ri rj, op) =>
      (cast (or_code ++ [option_bool op] ++ reg_vect ri ++ reg_vect rj ++ const b0 _)
            (eq_sym interpSplitLemRight),
      option_word op)
    | (xorI ri rj, op) =>
      (cast (xor_code ++ [option_bool op] ++ reg_vect ri ++ reg_vect rj ++ const b0 _)
            (eq_sym interpSplitLemRight),
      option_word op)
    | (notI ri, op) =>
      (cast (not_code ++ [option_bool op] ++ reg_vect ri ++ const b0 _ ++ const b0 _)
            (eq_sym interpSplitLemRight),
      option_word op)
    | (addI ri rj, op) =>
      (cast (add_code ++ [option_bool op] ++ reg_vect ri ++ reg_vect rj ++ const b0 _)
            (eq_sym interpSplitLemRight),
      option_word op)
    | (subI ri rj, op) =>
      (cast (sub_code ++ [option_bool op] ++ reg_vect ri ++ reg_vect rj ++ const b0 _)
            (eq_sym interpSplitLemRight),
      option_word op)
    | (mullI ri rj, op) =>
      (cast (mull_code ++ [option_bool op] ++ reg_vect ri ++ reg_vect rj ++ const b0 _)
            (eq_sym interpSplitLemRight),
      option_word op)
    | (umulhI ri rj, op) =>
      (cast (umulh_code ++ [option_bool op] ++ reg_vect ri ++ reg_vect rj ++ const b0 _)
            (eq_sym interpSplitLemRight),
      option_word op)
    | (smulhI ri rj, op) =>
      (cast (smulh_code ++ [option_bool op] ++ reg_vect ri ++ reg_vect rj ++ const b0 _)
            (eq_sym interpSplitLemRight),
      option_word op)
    | (udivI ri rj, op) =>
      (cast (udiv_code ++ [option_bool op] ++ reg_vect ri ++ reg_vect rj ++ const b0 _)
            (eq_sym interpSplitLemRight),
      option_word op)
    | (umodI ri rj, op) =>
      (cast (umod_code ++ [option_bool op] ++ reg_vect ri ++ reg_vect rj ++ const b0 _)
            (eq_sym interpSplitLemRight),
      option_word op)
    | (shlI ri rj, op) =>
      (cast (shl_code ++ [option_bool op] ++ reg_vect ri ++ reg_vect rj ++ const b0 _)
            (eq_sym interpSplitLemRight),
      option_word op)
    | (shrI ri rj, op) =>
      (cast (shr_code ++ [option_bool op] ++ reg_vect ri ++ reg_vect rj ++ const b0 _)
            (eq_sym interpSplitLemRight),
      option_word op)
    | (cmpeI ri, op) =>
      (cast (cmpe_code ++ [option_bool op] ++ const b0 _ ++ reg_vect ri ++ const b0 _)
            (eq_sym interpSplitLemRight),
      option_word op)
    | (cmpaI ri, op) =>
      (cast (cmpa_code ++ [option_bool op] ++ const b0 _ ++ reg_vect ri ++ const b0 _)
            (eq_sym interpSplitLemRight),
      option_word op)
    | (cmpaeI ri, op) =>
      (cast (cmpae_code ++ [option_bool op] ++ const b0 _ ++ reg_vect ri ++ const b0 _)
            (eq_sym interpSplitLemRight),
      option_word op)
    | (cmpgI ri, op) =>
      (cast (cmpg_code ++ [option_bool op] ++ const b0 _ ++ reg_vect ri ++ const b0 _)
            (eq_sym interpSplitLemRight),
      option_word op)
    | (cmpgeI ri, op) =>
      (cast (cmpge_code ++ [option_bool op] ++ const b0 _ ++ reg_vect ri ++ const b0 _)
            (eq_sym interpSplitLemRight),
      option_word op)
    | (movI ri, op) =>
      (cast (mov_code ++ [option_bool op] ++ reg_vect ri ++ const b0 _ ++ const b0 _)
            (eq_sym interpSplitLemRight),
      option_word op)
    | (cmovI ri, op) =>
      (cast (cmov_code ++ [option_bool op] ++ reg_vect ri ++ const b0 _ ++ const b0 _)
            (eq_sym interpSplitLemRight),
      option_word op)
    | (jmpI, op) =>
      (cast (jmp_code ++ [option_bool op] ++ const b0 _ ++ const b0 _ ++ const b0 _)
            (eq_sym interpSplitLemRight),
      option_word op)
    | (cjmpI, op) =>
      (cast (cjmp_code ++ [option_bool op] ++ const b0 _ ++ const b0 _ ++ const b0 _)
            (eq_sym interpSplitLemRight),
      option_word op)
    | (cnjmpI, op) =>
      (cast (cnjmp_code ++ [option_bool op] ++ const b0 _ ++ const b0 _ ++ const b0 _)
            (eq_sym interpSplitLemRight),
      option_word op)
    | (store_bI ri, op) =>
      (cast (store_b_code ++ [option_bool op] ++ reg_vect ri ++ const b0 _ ++ const b0 _)
            (eq_sym interpSplitLemRight),
      option_word op)
    | (load_bI ri, op) =>
      (cast (load_b_code ++ [option_bool op] ++ reg_vect ri ++ const b0 _ ++ const b0 _)
            (eq_sym interpSplitLemRight),
      option_word op)
    | (store_wI ri, op) =>
      (cast (store_w_code ++ [option_bool op] ++ reg_vect ri ++ const b0 _ ++ const b0 _)
            (eq_sym interpSplitLemRight),
      option_word op)
    | (load_wI ri, op) =>
      (cast (load_w_code ++ [option_bool op] ++ reg_vect ri ++ const b0 _ ++ const b0 _)
            (eq_sym interpSplitLemRight),
      option_word op)
    | (readI ri, op) =>
      (cast (read_code ++ [option_bool op] ++ reg_vect ri ++ const b0 _ ++ const b0 _)
            (eq_sym interpSplitLemRight),
      option_word op)
    | (answerI, op) =>
      (cast (answer_code ++ [option_bool op] ++ const b0 _ ++ const b0 _ ++ const b0 _)
            (eq_sym interpSplitLemRight),
      option_word op)
    end.

  Theorem reg_vect_bitvector_fin_big_id_sig : forall r,
      proj1_sig (bitvector_fin_big (reg_vect r)) =
      proj1_sig r.
  Proof.
    intros [r rprp].
    unfold reg_vect.
    rewrite fin_bitvector_big_inv.
    reflexivity.
  Qed.

  Theorem reg_vect_bitvector_fin_big_id_lem : forall r,
      proj1_sig (bitvector_fin_big (reg_vect r)) < registerCount.
  Proof.
    intros [r rprp].
    rewrite reg_vect_bitvector_fin_big_id_sig.
    exact rprp.
  Qed.

  (* Cleanup beurocracy at end of each case. *)
  Ltac encode_decode_fin :=
      f_equal; unfold regFit, reg_vect, option_word; f_equal;
      apply subset_eq_compat; rewrite fin_bitvector_big_inv; reflexivity.

  (* try proving that r is in bounds/is a valid register. *)
  Ltac reg_bound r rprp rDef H :=
    assert (proj1_sig (bitvector_fin_big (reg_vect r)) < registerCount) as H;
    try (rewrite reg_vect_bitvector_fin_big_id_sig, rDef; exact rprp);
    rewrite rDef in H.

  (* try proving that the word r is in bounds/is a valid register. *)
  Ltac reg_bound_word r rprp rDef H :=
    assert (proj1_sig (bitvector_fin_big (option_word (inr r))) < registerCount) as H;
    try (rewrite rDef; unfold option_word; rewrite fin_bitvector_big_inv; exact rprp);
    rewrite rDef in H.

  Theorem encode_decode_id : forall o, 
    uncurry OpcodeDecode (OpcodeEncode o) = o.
  Proof.
    intro o; destruct o as [o op]; destruct o;
    unfold OpcodeEncode, uncurry;
    destruct op; unfold option_bool;
    try (destruct r as [r' rprp] eqn:rDef);
    try (destruct r0 as [r0' r0prp] eqn:r0Def);
    try (destruct r1 as [r1' r1prp] eqn:r1Def);
    try reg_bound r rprp rDef H;
    try reg_bound r0 r0prp r0Def H0;
    try ( reg_bound_word r1 r1prp r1Def H1 ||
          reg_bound_word r0 r0prp r0Def H1 ||
          reg_bound_word r rprp rDef H1 ).
    - rewrite (and_decode_word_correct _ _ H H0); encode_decode_fin.
    - rewrite (and_decode_register_correct _ _ H H0 _ H1); encode_decode_fin.
    - rewrite (or_decode_word_correct _ _ H H0); encode_decode_fin.
    - rewrite (or_decode_register_correct _ _ H H0 _ H1); encode_decode_fin.
    - rewrite (xor_decode_word_correct _ _ H H0); encode_decode_fin.
    - rewrite (xor_decode_register_correct _ _ H H0 _ H1); encode_decode_fin.
    - rewrite (not_decode_word_correct _ _ H); encode_decode_fin.
    - rewrite (not_decode_register_correct _ _ H _ H1); encode_decode_fin.
    - rewrite (add_decode_word_correct _ _ H H0); encode_decode_fin.
    - rewrite (add_decode_register_correct _ _ H H0 _ H1); encode_decode_fin.
    - rewrite (sub_decode_word_correct _ _ H H0); encode_decode_fin.
    - rewrite (sub_decode_register_correct _ _ H H0 _ H1); encode_decode_fin.
    - rewrite (mull_decode_word_correct _ _ H H0); encode_decode_fin.
    - rewrite (mull_decode_register_correct _ _ H H0 _ H1); encode_decode_fin.
    - rewrite (umulh_decode_word_correct _ _ H H0); encode_decode_fin.
    - rewrite (umulh_decode_register_correct _ _ H H0 _ H1); encode_decode_fin.
    - rewrite (smulh_decode_word_correct _ _ H H0); encode_decode_fin.
    - rewrite (smulh_decode_register_correct _ _ H H0 _ H1); encode_decode_fin.
    - rewrite (udiv_decode_word_correct _ _ H H0); encode_decode_fin.
    - rewrite (udiv_decode_register_correct _ _ H H0 _ H1); encode_decode_fin.
    - rewrite (umod_decode_word_correct _ _ H H0); encode_decode_fin.
    - rewrite (umod_decode_register_correct _ _ H H0 _ H1); encode_decode_fin.
    - rewrite (shl_decode_word_correct _ _ H H0); encode_decode_fin.
    - rewrite (shl_decode_register_correct _ _ H H0 _ H1); encode_decode_fin.
    - rewrite (shr_decode_word_correct _ _ H H0); encode_decode_fin.
    - rewrite (shr_decode_register_correct _ _ H H0 _ H1); encode_decode_fin.
    - rewrite (cmpe_decode_word_correct _ _ H); encode_decode_fin.
    - rewrite (cmpe_decode_register_correct _ _ H _ H1); encode_decode_fin.
    - rewrite (cmpa_decode_word_correct _ _ H); encode_decode_fin.
    - rewrite (cmpa_decode_register_correct _ _ H _ H1); encode_decode_fin.
    - rewrite (cmpae_decode_word_correct _ _ H); encode_decode_fin.
    - rewrite (cmpae_decode_register_correct _ _ H _ H1); encode_decode_fin.
    - rewrite (cmpg_decode_word_correct _ _ H); encode_decode_fin.
    - rewrite (cmpg_decode_register_correct _ _ H _ H1); encode_decode_fin.
    - rewrite (cmpge_decode_word_correct _ _ H); encode_decode_fin.
    - rewrite (cmpge_decode_register_correct _ _ H _ H1); encode_decode_fin.
    - rewrite (mov_decode_word_correct _ _ H); encode_decode_fin.
    - rewrite (mov_decode_register_correct _ _ H _ H1); encode_decode_fin.
    - rewrite (cmov_decode_word_correct _ _ H); encode_decode_fin.
    - rewrite (cmov_decode_register_correct _ _ H _ H1); encode_decode_fin.
    - rewrite jmp_decode_word_correct; encode_decode_fin.
    - rewrite (jmp_decode_register_correct _ _ _ H1); encode_decode_fin.
    - rewrite cjmp_decode_word_correct; encode_decode_fin.
    - rewrite (cjmp_decode_register_correct _ _ _ H1); encode_decode_fin.
    - rewrite cnjmp_decode_word_correct; encode_decode_fin.
    - rewrite (cnjmp_decode_register_correct _ _ _ H1); encode_decode_fin.
    - rewrite (store_b_decode_word_correct _ _ H); encode_decode_fin.
    - rewrite (store_b_decode_register_correct _ _ H _ H1); encode_decode_fin.
    - rewrite (load_b_decode_word_correct _ _ H); encode_decode_fin.
    - rewrite (load_b_decode_register_correct _ _ H _ H1); encode_decode_fin.
    - rewrite (store_w_decode_word_correct _ _ H); encode_decode_fin.
    - rewrite (store_w_decode_register_correct _ _ H _ H1); encode_decode_fin.
    - rewrite (load_w_decode_word_correct _ _ H); encode_decode_fin.
    - rewrite (load_w_decode_register_correct _ _ H _ H1); encode_decode_fin.
    - rewrite (read_decode_word_correct _ _ H); encode_decode_fin.
    - rewrite (read_decode_register_correct _ _ H _ H1); encode_decode_fin.
    - rewrite answer_decode_word_correct; encode_decode_fin.
    - rewrite (answer_decode_register_correct _ _ _ H1); encode_decode_fin.
  Qed.

End TinyRAMCoding.
