From Coq Require Import
  Lia.
From TinyRAM.Utils Require Import
  Vectors.
From TinyRAM.Utils Require Import
  BitVectors.
From TinyRAM.Utils Require Import
  Fin.
From TinyRAM.Utils Require Import
  Arith.
Import PeanoNat.Nat.
From TinyRAM.Machine Require Import
  Parameters.
From TinyRAM.Machine Require Import
  Words.
Require Import ProofIrrelevance.
Require Import FunctionalExtensionality.
Require Import VectorDef.
Import VectorNotations.

Module TinyRAMDecodOps (Params : TinyRAMParameters).
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
    interpSplit (vector_length_coerce (eq_sym interpSplitLemRight) (
      code ++ [b] ++ ri ++ rj ++ padding
    )) = (code, b, ri, rj, padding).
  Proof.
    intros code b ri rj padding.
    unfold interpSplit.
    replace (eq_rect _ _ _ _ _)
        with ((((code ++ [b]) ++ ri) ++ rj) ++ padding).
    { repeat rewrite Vector.splitat_append; reflexivity. }
    change (eq_rect wordSize _ _ _ _)
      with (vector_length_coerce interpSplitLemLeft
              (vector_length_coerce (eq_sym interpSplitLemRight)
              (code ++ [b] ++ ri ++ rj ++ padding))).
    repeat rewrite <- vector_length_coerce_app_assoc_2.
    repeat rewrite vector_length_coerce_trans.
    repeat rewrite vector_length_coerce_app_l.
    rewrite vector_length_coerce_id.
    reflexivity.
  Qed.

  Variant OpcodeI : Type :=
  | andI : regId -> regId -> regId + Word -> OpcodeI
  | orI : regId -> regId -> regId + Word -> OpcodeI
  | xorI : regId -> regId -> regId + Word -> OpcodeI
  | notI : regId -> regId + Word -> OpcodeI
  | addI : regId -> regId -> regId + Word -> OpcodeI
  | subI : regId -> regId -> regId + Word -> OpcodeI
  | mullI : regId -> regId -> regId + Word -> OpcodeI
  | umulhI : regId -> regId -> regId + Word -> OpcodeI
  | smulhI : regId -> regId -> regId + Word -> OpcodeI
  | udivI : regId -> regId -> regId + Word -> OpcodeI
  | umodI : regId -> regId -> regId + Word -> OpcodeI
  | shlI : regId -> regId -> regId + Word -> OpcodeI
  | shrI : regId -> regId -> regId + Word -> OpcodeI
  | cmpeI : regId -> regId + Word -> OpcodeI
  | cmpaI : regId -> regId + Word -> OpcodeI
  | cmpaeI : regId -> regId + Word -> OpcodeI
  | cmpgI : regId -> regId + Word -> OpcodeI
  | cmpgeI : regId -> regId + Word -> OpcodeI
  | movI : regId -> regId + Word -> OpcodeI
  | cmovI : regId -> regId + Word -> OpcodeI
  | jmpI : regId + Word -> OpcodeI
  | cjmpI : regId + Word -> OpcodeI
  | cnjmpI : regId + Word -> OpcodeI
  | store_bI : regId -> regId + Word -> OpcodeI
  | load_bI : regId -> regId + Word -> OpcodeI
  | store_wI : regId -> regId + Word -> OpcodeI
  | load_wI : regId -> regId + Word -> OpcodeI
  | readI : regId -> regId + Word -> OpcodeI
  | answerI : regId + Word -> OpcodeI.

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

  Definition answer1 : OpcodeI.
    apply answerI.
    apply inr.
    apply fin_bitvector_big.
    exists 1.
    transitivity wordSize.
    2: { apply pow_gt_lin_r. lia. }
    assert (5 < wordSize). { apply wordSizeMin. }
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
    (code : regId + Word -> OpcodeI)
    (isReg : bool) (w2: Word) (w2reg: option regId),
    OpcodeI.
    intros code isReg w2 w2reg.
    destruct isReg.
    + destruct w2reg as [w2reg|]. 2: { exact answer1. }
      exact (code (inl w2reg)).
    + exact (code (inr w2)).
  Defined.

  Definition OpcodeDecodeRiA : forall
    (code : regId -> regId + Word -> OpcodeI)
    (isReg : bool) (ri : option regId)
    (w2: Word) (w2reg: option regId),
    OpcodeI.
    intros code isReg ri w2 w2reg.
    destruct ri as [ri|]. 2: { exact answer1. }
    destruct isReg.
    + destruct w2reg as [w2reg|]. 2: { exact answer1. }
      exact (code ri (inl w2reg)).
    + exact (code ri (inr w2)).
  Defined.

  Definition OpcodeDecodeRiRjA : forall
    (code : regId -> regId -> regId + Word -> OpcodeI)
    (isReg : bool) (ri rj : option regId)
    (w2: Word) (w2reg: option regId),
    OpcodeI.
    intros code isReg ri rj w2 w2reg.
    destruct ri as [ri|]. 2: { exact answer1. }
    destruct rj as [rj|]. 2: { exact answer1. }
    destruct isReg.
    + destruct w2reg as [w2reg|]. 2: { exact answer1. }
      exact (code ri rj (inl w2reg)).
    + exact (code ri rj (inr w2)).
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
  Definition OpcodeDecode (w1 w2 : Word) : OpcodeI :=
    match interpSplit w1 with
    | (op, isReg, pri, prj, _) =>
      let ri := oreg pri in
      let rj := oreg prj in
      let ow := oreg w2 in
      match proj1_sig (bitvector_fin_big op) with
      | 0 =>  OpcodeDecodeRiRjA andI   isReg ri rj w2 ow
      | 1 =>  OpcodeDecodeRiRjA orI    isReg ri rj w2 ow
      | 2 =>  OpcodeDecodeRiRjA xorI   isReg ri rj w2 ow
      | 3 =>  OpcodeDecodeRiA   notI   isReg ri w2 ow
      | 4 =>  OpcodeDecodeRiRjA addI   isReg ri rj w2 ow
      | 5 =>  OpcodeDecodeRiRjA subI   isReg ri rj w2 ow
      | 6 =>  OpcodeDecodeRiRjA mullI  isReg ri rj w2 ow
      | 7 =>  OpcodeDecodeRiRjA umulhI isReg ri rj w2 ow
      | 8 =>  OpcodeDecodeRiRjA smulhI isReg ri rj w2 ow
      | 9 =>  OpcodeDecodeRiRjA udivI  isReg ri rj w2 ow
      | 10 => OpcodeDecodeRiRjA umodI  isReg ri rj w2 ow
      | 11 => OpcodeDecodeRiRjA shlI   isReg ri rj w2 ow
      | 12 => OpcodeDecodeRiRjA shrI   isReg ri rj w2 ow
      | 13 => OpcodeDecodeRiA   cmpeI  isReg rj w2 ow
      | 14 => OpcodeDecodeRiA   cmpaI  isReg rj w2 ow
      | 15 => OpcodeDecodeRiA   cmpaeI isReg rj w2 ow
      | 16 => OpcodeDecodeRiA   cmpgI  isReg rj w2 ow
      | 17 => OpcodeDecodeRiA   cmpgeI isReg rj w2 ow
      | 18 => OpcodeDecodeRiA   movI   isReg ri w2 ow
      | 19 => OpcodeDecodeRiA   cmovI  isReg ri w2 ow
      | 20 => OpcodeDecodeA     jmpI   isReg w2 ow
      | 21 => OpcodeDecodeA     cjmpI  isReg w2 ow
      | 22 => OpcodeDecodeA     cnjmpI isReg w2 ow
      | 23 => answer1
      | 24 => answer1
      | 25 => answer1
      | 26 => OpcodeDecodeRiA   store_bI isReg ri w2 ow
      | 27 => OpcodeDecodeRiA   load_bI  isReg ri w2 ow
      | 28 => OpcodeDecodeRiA   store_wI isReg ri w2 ow
      | 29 => OpcodeDecodeRiA   load_wI  isReg ri w2 ow
      | 30 => OpcodeDecodeRiA   readI    isReg ri w2 ow
      | 31 => OpcodeDecodeA     answerI  isReg w2 ow
      | _ => answer1
      end
    end.

  (***
    This section is based on Table 2 of pg. 16 in spec. 
  ***)
 
  Definition b1 := true.
  Definition b0 := false.

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
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (and_code ++ [b1] ++ ri ++ rj ++ padding))) A =
    andI (regFit ri lti) (regFit rj ltj) (inl (regFit A ltA)).
  Proof. unfold and_code. rirjAProof_register. Qed.
 
  Theorem and_decode_word_correct :
    forall (ri rj : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (and_code ++ [b0] ++ ri ++ rj ++ padding))) A =
    andI (regFit ri lti) (regFit rj ltj) (inr A).
  Proof. unfold and_code. rirjAProof_word. Qed.

Definition or_code := [b0; b0; b0; b0; b1].

Theorem or_decode_register_correct :
    forall (ri rj : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (or_code ++ [b1] ++ ri ++ rj ++ padding))) A =
    orI (regFit ri lti) (regFit rj ltj) (inl (regFit A ltA)).
  Proof. unfold or_code. rirjAProof_register. Qed.
 
  Theorem or_decode_word_correct :
    forall (ri rj : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (or_code ++ [b0] ++ ri ++ rj ++ padding))) A =
    orI (regFit ri lti) (regFit rj ltj) (inr A).
  Proof. unfold or_code. rirjAProof_word. Qed.

  Definition xor_code := [b0; b0; b0; b1; b0].

  Theorem xor_decode_register_correct :
    forall (ri rj : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (xor_code ++ [b1] ++ ri ++ rj ++ padding))) A =
    xorI (regFit ri lti) (regFit rj ltj) (inl (regFit A ltA)).
  Proof. unfold xor_code. rirjAProof_register. Qed.
 
  Theorem xor_decode_word_correct :
    forall (ri rj : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (xor_code ++ [b0] ++ ri ++ rj ++ padding ))) A =
    xorI (regFit ri lti) (regFit rj ltj) (inr A).
  Proof. unfold xor_code. rirjAProof_word. Qed.

  Definition not_code := [b0; b0; b0; b1; b1].

  Theorem not_decode_register_correct :
    forall (ri pad : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (not_code ++ [b1] ++ ri ++ pad ++ padding))) A =
    notI (regFit ri lti) (inl (regFit A ltA)).
  Proof. unfold not_code. riAProof_register. Qed.
 
  Theorem not_decode_word_correct :
    forall (ri pad : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (not_code ++ [b0] ++ ri ++ pad ++ padding))) A =
    notI (regFit ri lti) (inr A).
  Proof. unfold not_code. riAProof_word. Qed.

  Definition add_code := [b0; b0; b1; b0; b0].

  Theorem add_decode_register_correct :
    forall (ri rj : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (add_code ++ [b1] ++ ri ++ rj ++ padding))) A =
    addI (regFit ri lti) (regFit rj ltj) (inl (regFit A ltA)).
  Proof. unfold add_code. rirjAProof_register. Qed.
 
  Theorem add_decode_word_correct :
    forall (ri rj : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (add_code ++ [b0] ++ ri ++ rj ++ padding))) A =
    addI (regFit ri lti) (regFit rj ltj) (inr A).
  Proof. unfold add_code. rirjAProof_word. Qed.

  Definition sub_code := [b0; b0; b1; b0; b1].

  Theorem sub_decode_register_correct :
    forall (ri rj : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (sub_code ++ [b1] ++ ri ++ rj ++ padding))) A =
    subI (regFit ri lti) (regFit rj ltj) (inl (regFit A ltA)).
  Proof. unfold sub_code. rirjAProof_register. Qed.
 
  Theorem sub_decode_word_correct :
    forall (ri rj : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (sub_code ++ [b0] ++ ri ++ rj ++ padding))) A =
    subI (regFit ri lti) (regFit rj ltj) (inr A).
  Proof. unfold sub_code. rirjAProof_word. Qed.

  Definition mull_code := [b0; b0; b1; b1; b0].

  Theorem mull_decode_register_correct :
    forall (ri rj : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (mull_code ++ [b1] ++ ri ++ rj ++ padding))) A =
    mullI (regFit ri lti) (regFit rj ltj) (inl (regFit A ltA)).
  Proof. unfold mull_code. rirjAProof_register. Qed.
 
  Theorem mull_decode_word_correct :
    forall (ri rj : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (mull_code ++ [b0] ++ ri ++ rj ++ padding))) A =
    mullI (regFit ri lti) (regFit rj ltj) (inr A).
  Proof. unfold mull_code. rirjAProof_word. Qed.

  Definition umulh_code := [b0; b0; b1; b1; b1].

  Theorem umulh_decode_register_correct :
    forall (ri rj : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (umulh_code ++ [b1] ++ ri ++ rj ++ padding))) A =
    umulhI (regFit ri lti) (regFit rj ltj) (inl (regFit A ltA)).
  Proof. unfold umulh_code. rirjAProof_register. Qed.
 
  Theorem umulh_decode_word_correct :
    forall (ri rj : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (umulh_code ++ [b0] ++ ri ++ rj ++ padding))) A =
    umulhI (regFit ri lti) (regFit rj ltj) (inr A).
  Proof. unfold umulh_code. rirjAProof_word. Qed.

  Definition smulh_code := [b0; b1; b0; b0; b0].

  Theorem smulh_decode_register_correct :
    forall (ri rj : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (smulh_code ++ [b1] ++ ri ++ rj ++ padding))) A =
    smulhI (regFit ri lti) (regFit rj ltj) (inl (regFit A ltA)).
  Proof. unfold smulh_code. rirjAProof_register. Qed.
 
  Theorem smulh_decode_word_correct :
    forall (ri rj : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (smulh_code ++ [b0] ++ ri ++ rj ++ padding))) A =
    smulhI (regFit ri lti) (regFit rj ltj) (inr A).
  Proof. unfold smulh_code. rirjAProof_word. Qed.

  Definition udiv_code := [b0; b1; b0; b0; b1].

  Theorem udiv_decode_register_correct :
    forall (ri rj : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (udiv_code ++ [b1] ++ ri ++ rj ++ padding))) A =
    udivI (regFit ri lti) (regFit rj ltj) (inl (regFit A ltA)).
  Proof. unfold udiv_code. rirjAProof_register. Qed.
 
  Theorem udiv_decode_word_correct :
    forall (ri rj : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (udiv_code ++ [b0] ++ ri ++ rj ++ padding))) A =
    udivI (regFit ri lti) (regFit rj ltj) (inr A).
  Proof. unfold udiv_code. rirjAProof_word. Qed.

  Definition umod_code := [b0; b1; b0; b1; b0].

  Theorem umod_decode_register_correct :
    forall (ri rj : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (umod_code ++ [b1] ++ ri ++ rj ++ padding))) A =
    umodI (regFit ri lti) (regFit rj ltj) (inl (regFit A ltA)).
  Proof. unfold umod_code. rirjAProof_register. Qed.
 
  Theorem umod_decode_word_correct :
    forall (ri rj : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (umod_code ++ [b0] ++ ri ++ rj ++ padding))) A =
    umodI (regFit ri lti) (regFit rj ltj) (inr A).
  Proof. unfold umod_code. rirjAProof_word. Qed.

  Definition shl_code := [b0; b1; b0; b1; b1].

  Theorem shl_decode_register_correct :
    forall (ri rj : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (shl_code ++ [b1] ++ ri ++ rj ++ padding))) A =
    shlI (regFit ri lti) (regFit rj ltj) (inl (regFit A ltA)).
  Proof. unfold shl_code. rirjAProof_register. Qed.
 
  Theorem shl_decode_word_correct :
    forall (ri rj : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (shl_code ++ [b0] ++ ri ++ rj ++ padding))) A =
    shlI (regFit ri lti) (regFit rj ltj) (inr A).
  Proof. unfold shl_code. rirjAProof_word. Qed.

  Definition shr_code := [b0; b1; b1; b0; b0].

  Theorem shr_decode_register_correct :
    forall (ri rj : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (shr_code ++ [b1] ++ ri ++ rj ++ padding))) A =
    shrI (regFit ri lti) (regFit rj ltj) (inl (regFit A ltA)).
  Proof. unfold shr_code. rirjAProof_register. Qed.
 
  Theorem shr_decode_word_correct :
    forall (ri rj : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (shr_code ++ [b0] ++ ri ++ rj ++ padding))) A =
    shrI (regFit ri lti) (regFit rj ltj) (inr A).
  Proof. unfold shr_code. rirjAProof_word. Qed.

  Definition cmpe_code := [b0; b1; b1; b0; b1].

  Theorem cmpe_decode_register_correct :
    forall (pad ri : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (cmpe_code ++ [b1] ++ pad ++ ri ++ padding))) A =
    cmpeI (regFit ri lti) (inl (regFit A ltA)).
  Proof. unfold cmpe_code. rjAProof_register. Qed.

  Theorem cmpe_decode_word_correct :
    forall (pad ri : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (cmpe_code ++ [b0] ++ pad ++ ri ++ padding))) A =
    cmpeI (regFit ri lti) (inr A).
  Proof. unfold cmpe_code. rjAProof_word. Qed.

  Definition cmpa_code := [b0; b1; b1; b1; b0].

  Theorem cmpa_decode_register_correct :
    forall (pad ri : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (cmpa_code ++ [b1] ++ pad ++ ri ++ padding))) A =
    cmpaI (regFit ri lti) (inl (regFit A ltA)).
  Proof. unfold cmpa_code. rjAProof_register. Qed.
 
  Theorem cmpa_decode_word_correct :
    forall (pad ri : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (cmpa_code ++ [b0] ++ pad ++ ri ++ padding))) A =
    cmpaI (regFit ri lti) (inr A).
  Proof. unfold cmpa_code. rjAProof_word. Qed.

  Definition cmpae_code := [b0; b1; b1; b1; b1].

  Theorem cmpae_decode_register_correct :
    forall (pad ri : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (cmpae_code ++ [b1] ++ pad ++ ri ++ padding))) A =
    cmpaeI (regFit ri lti) (inl (regFit A ltA)).
  Proof. unfold cmpae_code. rjAProof_register. Qed.
 
  Theorem cmpae_decode_word_correct :
    forall (pad ri : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (cmpae_code ++ [b0] ++ pad ++ ri ++ padding))) A =
    cmpaeI (regFit ri lti) (inr A).
  Proof. unfold cmpae_code. rjAProof_word. Qed.

  Definition cmpg_code := [b1; b0; b0; b0; b0].

  Theorem cmpg_decode_register_correct :
    forall (pad ri : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (cmpg_code ++ [b1] ++ pad ++ ri ++ padding))) A =
    cmpgI (regFit ri lti) (inl (regFit A ltA)).
  Proof. unfold cmpg_code. rjAProof_register. Qed.
 
  Theorem cmpg_decode_word_correct :
    forall (pad ri : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (cmpg_code ++ [b0] ++ pad ++ ri ++ padding))) A =
    cmpgI (regFit ri lti) (inr A).
  Proof. unfold cmpg_code. rjAProof_word. Qed.

  Definition cmpge_code := [b1; b0; b0; b0; b1].

  Theorem cmpge_decode_register_correct :
    forall (pad ri : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (cmpge_code ++ [b1] ++ pad ++ ri ++ padding))) A =
    cmpgeI (regFit ri lti) (inl (regFit A ltA)).
  Proof. unfold cmpge_code. rjAProof_register. Qed.
 
  Theorem cmpge_decode_word_correct :
    forall (pad ri : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (cmpge_code ++ [b0] ++ pad ++ ri ++ padding))) A =
    cmpgeI (regFit ri lti) (inr A).
  Proof. unfold cmpge_code. rjAProof_word. Qed.

  Definition mov_code := [b1; b0; b0; b1; b0].

  Theorem mov_decode_register_correct :
    forall (ri pad : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (mov_code ++ [b1] ++ ri ++ pad ++ padding))) A =
    movI (regFit ri lti) (inl (regFit A ltA)).
  Proof. unfold mov_code. riAProof_register. Qed.

  Theorem mov_decode_word_correct :
    forall (ri pad : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (mov_code ++ [b0] ++ ri ++ pad ++ padding))) A =
    movI (regFit ri lti) (inr A).
  Proof. unfold mov_code. riAProof_word. Qed.

  Definition cmov_code := [b1; b0; b0; b1; b1].

  Theorem cmov_decode_register_correct :
    forall (ri pad : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (cmov_code ++ [b1] ++ ri ++ pad ++ padding))) A =
    cmovI (regFit ri lti) (inl (regFit A ltA)).
  Proof. unfold cmov_code. riAProof_register. Qed.
 
  Theorem cmov_decode_word_correct :
    forall (ri pad : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (cmov_code ++ [b0] ++ ri ++ pad ++ padding))) A =
    cmovI (regFit ri lti) (inr A).
  Proof. unfold cmov_code. riAProof_word. Qed.

  Definition jmp_code := [b1; b0; b1; b0; b0].

  Theorem jmp_decode_register_correct :
    forall (pad1 pad2 : Vector.t bool (log2_up registerCount))
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (jmp_code ++ [b1] ++ pad1 ++ pad2 ++ padding))) A =
    jmpI (inl (regFit A ltA)).
  Proof. unfold jmp_code. AProof_register. Qed.
 
  Theorem jmp_decode_word_correct :
    forall (pad1 pad2 : Vector.t bool (log2_up registerCount))
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (jmp_code ++ [b0] ++ pad1 ++ pad2 ++ padding))) A =
    jmpI (inr A).
  Proof. unfold jmp_code. AProof_word. Qed.

  Definition cjmp_code := [b1; b0; b1; b0; b1].

  Theorem cjmp_decode_register_correct :
    forall (pad1 pad2 : Vector.t bool (log2_up registerCount))
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (cjmp_code ++ [b1] ++ pad1 ++ pad2 ++ padding))) A =
    cjmpI (inl (regFit A ltA)).
  Proof. unfold cjmp_code. AProof_register. Qed.
 
  Theorem cjmp_decode_word_correct :
    forall (pad1 pad2 : Vector.t bool (log2_up registerCount))
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (cjmp_code ++ [b0] ++ pad1 ++ pad2 ++ padding))) A =
    cjmpI (inr A).
  Proof. unfold cjmp_code. AProof_word. Qed.

  Definition cnjmp_code := [b1; b0; b1; b1; b0].

  Theorem cnjmp_decode_register_correct :
    forall (pad1 pad2 : Vector.t bool (log2_up registerCount))
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (cnjmp_code ++ [b1] ++ pad1 ++ pad2 ++ padding))) A =
    cnjmpI (inl (regFit A ltA)).
  Proof. unfold cnjmp_code. AProof_register. Qed.
 
  Theorem cnjmp_decode_word_correct :
    forall (pad1 pad2 : Vector.t bool (log2_up registerCount))
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (cnjmp_code ++ [b0] ++ pad1 ++ pad2 ++ padding))) A =
    cnjmpI (inr A).
  Proof. unfold cnjmp_code. AProof_word. Qed.

  Definition store_b_code := [b1; b1; b0; b1; b0].

  Theorem store_b_decode_register_correct :
    forall (ri pad : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (store_b_code ++ [b1] ++ ri ++ pad ++ padding))) A =
    store_bI (regFit ri lti) (inl (regFit A ltA)).
  Proof. unfold store_b_code. riAProof_register. Qed.
 
  Theorem store_b_decode_word_correct :
    forall (ri pad : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (store_b_code ++ [b0] ++ ri ++ pad ++ padding))) A =
    store_bI (regFit ri lti) (inr A).
  Proof. unfold store_b_code. riAProof_word. Qed.

  Definition load_b_code := [b1; b1; b0; b1; b1].

  Theorem load_b_decode_register_correct :
    forall (ri pad : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (load_b_code ++ [b1] ++ ri ++ pad ++ padding))) A =
    load_bI (regFit ri lti) (inl (regFit A ltA)).
  Proof. unfold load_b_code. riAProof_register. Qed.
 
  Theorem load_b_decode_word_correct :
    forall (ri pad : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (load_b_code ++ [b0] ++ ri ++ pad ++ padding))) A =
    load_bI (regFit ri lti) (inr A).
  Proof. unfold load_b_code. riAProof_word. Qed.

  Definition store_w_code := [b1; b1; b1; b0; b0].

  Theorem store_w_decode_register_correct :
    forall (ri pad : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (store_w_code ++ [b1] ++ ri ++ pad ++ padding))) A =
    store_wI (regFit ri lti) (inl (regFit A ltA)).
  Proof. unfold store_w_code. riAProof_register. Qed.
 
  Theorem store_w_decode_word_correct :
    forall (ri pad : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (store_w_code ++ [b0] ++ ri ++ pad ++ padding))) A =
    store_wI (regFit ri lti) (inr A).
  Proof. unfold store_w_code. riAProof_word. Qed.

  Definition load_w_code := [b1; b1; b1; b0; b1].

  Theorem load_w_decode_register_correct :
    forall (ri pad : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (load_w_code ++ [b1] ++ ri ++ pad ++ padding))) A =
    load_wI (regFit ri lti) (inl (regFit A ltA)).
  Proof. unfold load_w_code. riAProof_register. Qed.
 
  Theorem load_w_decode_word_correct :
    forall (ri pad : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (load_w_code ++ [b0] ++ ri ++ pad ++ padding))) A =
    load_wI (regFit ri lti) (inr A).
  Proof. unfold load_w_code. riAProof_word. Qed.

  Definition read_code := [b1; b1; b1; b1; b0].

  Theorem read_decode_register_correct :
    forall (ri pad : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (read_code ++ [b1] ++ ri ++ pad ++ padding))) A =
    readI (regFit ri lti) (inl (regFit A ltA)).
  Proof. unfold read_code. riAProof_register. Qed.
 
  Theorem read_decode_word_correct :
    forall (ri pad : Vector.t bool (log2_up registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (read_code ++ [b0] ++ ri ++ pad ++ padding))) A =
    readI (regFit ri lti) (inr A).
  Proof. unfold read_code. riAProof_word. Qed.

  Definition answer_code := [b1; b1; b1; b1; b1].

  Theorem answer_decode_register_correct :
    forall (pad1 pad2 : Vector.t bool (log2_up registerCount))
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (answer_code ++ [b1] ++ pad1 ++ pad2 ++ padding))) A =
    answerI (inl (regFit A ltA)).
  Proof. unfold answer_code. AProof_register. Qed.
 
  Theorem answer_decode_word_correct :
    forall (pad1 pad2 : Vector.t bool (log2_up registerCount))
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      (answer_code ++ [b0] ++ pad1 ++ pad2 ++ padding))) A =
    answerI (inr A).
  Proof. unfold answer_code. AProof_word. Qed.

  Definition option_word : regId + Word -> Word.
    intros [[rid ridp]|w].
    - apply fin_bitvector_big.
      exists rid.
      transitivity registerCount. { assumption. }
      apply registerCount_lt_2powwordSize2.
      lia.
    - exact w. 
  Defined.

  Definition option_bool (o : regId + Word) : bool :=
    if o then b1 else b0.

  Definition reg_vect : regId -> t bool (log2_up registerCount).
    intros [r rprp].
    apply fin_bitvector_big.
    exists r.
    apply (lt_le_trans _ registerCount). { assumption. }
    rewrite log2_up_le_pow2; lia.
  Defined.

  Definition OpcodeEncode (o : OpcodeI) : Word * Word :=
    match o with
    | andI ri rj op => (vector_length_coerce (eq_sym interpSplitLemRight)
      (and_code ++ [option_bool op] ++ reg_vect ri ++ reg_vect rj ++ const b0 _),
      option_word op)
    | orI ri rj op => (vector_length_coerce (eq_sym interpSplitLemRight)
      (or_code ++ [option_bool op] ++ reg_vect ri ++ reg_vect rj ++ const b0 _),
      option_word op)
    | xorI ri rj op => (vector_length_coerce (eq_sym interpSplitLemRight)
      (xor_code ++ [option_bool op] ++ reg_vect ri ++ reg_vect rj ++ const b0 _),
      option_word op)
    | notI ri op => (vector_length_coerce (eq_sym interpSplitLemRight)
      (not_code ++ [option_bool op] ++ reg_vect ri ++ const b0 _ ++ const b0 _),
      option_word op)
    | addI ri rj op => (vector_length_coerce (eq_sym interpSplitLemRight)
      (add_code ++ [option_bool op] ++ reg_vect ri ++ reg_vect rj ++ const b0 _),
      option_word op)
    | subI ri rj op => (vector_length_coerce (eq_sym interpSplitLemRight)
      (sub_code ++ [option_bool op] ++ reg_vect ri ++ reg_vect rj ++ const b0 _),
      option_word op)
    | mullI ri rj op => (vector_length_coerce (eq_sym interpSplitLemRight)
      (mull_code ++ [option_bool op] ++ reg_vect ri ++ reg_vect rj ++ const b0 _),
      option_word op)
    | umulhI ri rj op => (vector_length_coerce (eq_sym interpSplitLemRight)
      (umulh_code ++ [option_bool op] ++ reg_vect ri ++ reg_vect rj ++ const b0 _),
      option_word op)
    | smulhI ri rj op => (vector_length_coerce (eq_sym interpSplitLemRight)
      (smulh_code ++ [option_bool op] ++ reg_vect ri ++ reg_vect rj ++ const b0 _),
      option_word op)
    | udivI ri rj op => (vector_length_coerce (eq_sym interpSplitLemRight)
      (udiv_code ++ [option_bool op] ++ reg_vect ri ++ reg_vect rj ++ const b0 _),
      option_word op)
    | umodI ri rj op => (vector_length_coerce (eq_sym interpSplitLemRight)
      (umod_code ++ [option_bool op] ++ reg_vect ri ++ reg_vect rj ++ const b0 _),
      option_word op)
    | shlI ri rj op => (vector_length_coerce (eq_sym interpSplitLemRight)
      (shl_code ++ [option_bool op] ++ reg_vect ri ++ reg_vect rj ++ const b0 _),
      option_word op)
    | shrI ri rj op => (vector_length_coerce (eq_sym interpSplitLemRight)
      (shr_code ++ [option_bool op] ++ reg_vect ri ++ reg_vect rj ++ const b0 _),
      option_word op)
    | cmpeI ri op => (vector_length_coerce (eq_sym interpSplitLemRight)
      (cmpe_code ++ [option_bool op] ++ const b0 _ ++ reg_vect ri ++ const b0 _),
      option_word op)
    | cmpaI ri op => (vector_length_coerce (eq_sym interpSplitLemRight)
      (cmpa_code ++ [option_bool op] ++ const b0 _ ++ reg_vect ri ++ const b0 _),
      option_word op)
    | cmpaeI ri op => (vector_length_coerce (eq_sym interpSplitLemRight)
      (cmpae_code ++ [option_bool op] ++ const b0 _ ++ reg_vect ri ++ const b0 _),
      option_word op)
    | cmpgI ri op => (vector_length_coerce (eq_sym interpSplitLemRight)
      (cmpg_code ++ [option_bool op] ++ const b0 _ ++ reg_vect ri ++ const b0 _),
      option_word op)
    | cmpgeI ri op => (vector_length_coerce (eq_sym interpSplitLemRight)
      (cmpge_code ++ [option_bool op] ++ const b0 _ ++ reg_vect ri ++ const b0 _),
      option_word op)
    | movI ri op => (vector_length_coerce (eq_sym interpSplitLemRight)
      (mov_code ++ [option_bool op] ++ reg_vect ri ++ const b0 _ ++ const b0 _),
      option_word op)
    | cmovI ri op => (vector_length_coerce (eq_sym interpSplitLemRight)
      (cmov_code ++ [option_bool op] ++ reg_vect ri ++ const b0 _ ++ const b0 _),
      option_word op)
    | jmpI op => (vector_length_coerce (eq_sym interpSplitLemRight)
      (jmp_code ++ [option_bool op] ++ const b0 _ ++ const b0 _ ++ const b0 _),
      option_word op)
    | cjmpI op => (vector_length_coerce (eq_sym interpSplitLemRight)
      (cjmp_code ++ [option_bool op] ++ const b0 _ ++ const b0 _ ++ const b0 _),
      option_word op)
    | cnjmpI op => (vector_length_coerce (eq_sym interpSplitLemRight)
      (cnjmp_code ++ [option_bool op] ++ const b0 _ ++ const b0 _ ++ const b0 _),
      option_word op)
    | store_bI ri op => (vector_length_coerce (eq_sym interpSplitLemRight)
      (store_b_code ++ [option_bool op] ++ reg_vect ri ++ const b0 _ ++ const b0 _),
      option_word op)
    | load_bI ri op => (vector_length_coerce (eq_sym interpSplitLemRight)
      (load_b_code ++ [option_bool op] ++ reg_vect ri ++ const b0 _ ++ const b0 _),
      option_word op)
    | store_wI ri op => (vector_length_coerce (eq_sym interpSplitLemRight)
      (store_w_code ++ [option_bool op] ++ reg_vect ri ++ const b0 _ ++ const b0 _),
      option_word op)
    | load_wI ri op => (vector_length_coerce (eq_sym interpSplitLemRight)
      (load_w_code ++ [option_bool op] ++ reg_vect ri ++ const b0 _ ++ const b0 _),
      option_word op)
    | readI ri op => (vector_length_coerce (eq_sym interpSplitLemRight)
      (read_code ++ [option_bool op] ++ reg_vect ri ++ const b0 _ ++ const b0 _),
      option_word op)
    | answerI op => (vector_length_coerce (eq_sym interpSplitLemRight)
      (answer_code ++ [option_bool op] ++ const b0 _ ++ const b0 _ ++ const b0 _),
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

  Ltac encode_decode_fin :=
      f_equal; unfold regFit, reg_vect, option_word; f_equal;
      apply subset_eq_compat; rewrite fin_bitvector_big_inv; reflexivity.

  Theorem encode_decode_id : forall o, 
    uncurry OpcodeDecode (OpcodeEncode o) = o.
  Proof.
    intro o; destruct o;
    unfold OpcodeEncode, uncurry;
    destruct s; unfold option_bool;
    try (destruct r as [r' rprp] eqn:rDef);
    try (destruct r0 as [r0' r0prp] eqn:r0Def);
    try (destruct r1 as [r1' r1prp] eqn:r1Def);
    try (assert (proj1_sig (bitvector_fin_big (reg_vect r)) < registerCount) as H0;
         try (rewrite reg_vect_bitvector_fin_big_id_sig, rDef; exact rprp);
         rewrite rDef in H0);
    try (assert (proj1_sig (bitvector_fin_big (reg_vect r0)) < registerCount) as H1;
         try (rewrite reg_vect_bitvector_fin_big_id_sig, r0Def; exact r0prp);
         rewrite r0Def in H1);
    try ( (assert (proj1_sig (bitvector_fin_big (option_word (inl r1))) < registerCount) as H2;
           try (rewrite r1Def; unfold option_word; rewrite fin_bitvector_big_inv; exact r1prp);
           rewrite r1Def in H2)
        ||(assert (proj1_sig (bitvector_fin_big (option_word (inl r0))) < registerCount) as H2;
           try (rewrite r0Def; unfold option_word; rewrite fin_bitvector_big_inv; exact r0prp);
           rewrite r0Def in H2)
        ||(assert (proj1_sig (bitvector_fin_big (option_word (inl r))) < registerCount) as H2;
           try (rewrite rDef; unfold option_word; rewrite fin_bitvector_big_inv; exact rprp);
           rewrite rDef in H2)).
    - rewrite (and_decode_register_correct _ _ H0 H1 _ H2); encode_decode_fin.
    - rewrite (and_decode_word_correct _ _ H0 H1); encode_decode_fin.
    - rewrite (or_decode_register_correct _ _ H0 H1 _ H2); encode_decode_fin.
    - rewrite (or_decode_word_correct _ _ H0 H1); encode_decode_fin.
    - rewrite (xor_decode_register_correct _ _ H0 H1 _ H2); encode_decode_fin.
    - rewrite (xor_decode_word_correct _ _ H0 H1); encode_decode_fin.
    - rewrite (not_decode_register_correct _ _ H0 _ H2); encode_decode_fin.
    - rewrite (not_decode_word_correct _ _ H0); encode_decode_fin.
    - rewrite (add_decode_register_correct _ _ H0 H1 _ H2); encode_decode_fin.
    - rewrite (add_decode_word_correct _ _ H0 H1); encode_decode_fin.
    - rewrite (sub_decode_register_correct _ _ H0 H1 _ H2); encode_decode_fin.
    - rewrite (sub_decode_word_correct _ _ H0 H1); encode_decode_fin.
    - rewrite (mull_decode_register_correct _ _ H0 H1 _ H2); encode_decode_fin.
    - rewrite (mull_decode_word_correct _ _ H0 H1); encode_decode_fin.
    - rewrite (umulh_decode_register_correct _ _ H0 H1 _ H2); encode_decode_fin.
    - rewrite (umulh_decode_word_correct _ _ H0 H1); encode_decode_fin.
    - rewrite (smulh_decode_register_correct _ _ H0 H1 _ H2); encode_decode_fin.
    - rewrite (smulh_decode_word_correct _ _ H0 H1); encode_decode_fin.
    - rewrite (udiv_decode_register_correct _ _ H0 H1 _ H2); encode_decode_fin.
    - rewrite (udiv_decode_word_correct _ _ H0 H1); encode_decode_fin.
    - rewrite (umod_decode_register_correct _ _ H0 H1 _ H2); encode_decode_fin.
    - rewrite (umod_decode_word_correct _ _ H0 H1); encode_decode_fin.
    - rewrite (shl_decode_register_correct _ _ H0 H1 _ H2); encode_decode_fin.
    - rewrite (shl_decode_word_correct _ _ H0 H1); encode_decode_fin.
    - rewrite (shr_decode_register_correct _ _ H0 H1 _ H2); encode_decode_fin.
    - rewrite (shr_decode_word_correct _ _ H0 H1); encode_decode_fin.
    - rewrite (cmpe_decode_register_correct _ _ H0 _ H2); encode_decode_fin.
    - rewrite (cmpe_decode_word_correct _ _ H0); encode_decode_fin.
    - rewrite (cmpa_decode_register_correct _ _ H0 _ H2); encode_decode_fin.
    - rewrite (cmpa_decode_word_correct _ _ H0); encode_decode_fin.
    - rewrite (cmpae_decode_register_correct _ _ H0 _ H2); encode_decode_fin.
    - rewrite (cmpae_decode_word_correct _ _ H0); encode_decode_fin.
    - rewrite (cmpg_decode_register_correct _ _ H0 _ H2); encode_decode_fin.
    - rewrite (cmpg_decode_word_correct _ _ H0); encode_decode_fin.
    - rewrite (cmpge_decode_register_correct _ _ H0 _ H2); encode_decode_fin.
    - rewrite (cmpge_decode_word_correct _ _ H0); encode_decode_fin.
    - rewrite (mov_decode_register_correct _ _ H0 _ H2); encode_decode_fin.
    - rewrite (mov_decode_word_correct _ _ H0); encode_decode_fin.
    - rewrite (cmov_decode_register_correct _ _ H0 _ H2); encode_decode_fin.
    - rewrite (cmov_decode_word_correct _ _ H0); encode_decode_fin.
    - rewrite (jmp_decode_register_correct _ _ _ H2); encode_decode_fin.
    - rewrite jmp_decode_word_correct; encode_decode_fin.
    - rewrite (cjmp_decode_register_correct _ _ _ H2); encode_decode_fin.
    - rewrite cjmp_decode_word_correct; encode_decode_fin.
    - rewrite (cnjmp_decode_register_correct _ _ _ H2); encode_decode_fin.
    - rewrite cnjmp_decode_word_correct; encode_decode_fin.
    - rewrite (store_b_decode_register_correct _ _ H0 _ H2); encode_decode_fin.
    - rewrite (store_b_decode_word_correct _ _ H0); encode_decode_fin.
    - rewrite (load_b_decode_register_correct _ _ H0 _ H2); encode_decode_fin.
    - rewrite (load_b_decode_word_correct _ _ H0); encode_decode_fin.
    - rewrite (store_w_decode_register_correct _ _ H0 _ H2); encode_decode_fin.
    - rewrite (store_w_decode_word_correct _ _ H0); encode_decode_fin.
    - rewrite (load_w_decode_register_correct _ _ H0 _ H2); encode_decode_fin.
    - rewrite (load_w_decode_word_correct _ _ H0); encode_decode_fin.
    - rewrite (read_decode_register_correct _ _ H0 _ H2); encode_decode_fin.
    - rewrite (read_decode_word_correct _ _ H0); encode_decode_fin.
    - rewrite (answer_decode_register_correct _ _ _ H2); encode_decode_fin.
    - rewrite answer_decode_word_correct; encode_decode_fin.
  Qed.

End TinyRAMDecodOps.


