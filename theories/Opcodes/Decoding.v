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

  Definition paddingSize := wordSize - 6 - 2 * clog2 registerCount.

  Theorem interpSplitLemLeft : 
    wordSize =
      5 + 1 + (clog2 registerCount) + (clog2 registerCount) +
      paddingSize.
    assert (6 + 2 * clog2 registerCount <= wordSize).
    { apply encodingAxiom. }
    unfold paddingSize; lia.
  Qed.

  Lemma interpSplitLemRight : 
    wordSize =
    5 + (1 + ((clog2 registerCount) + ((clog2 registerCount) + paddingSize))).
  Proof.
    rewrite interpSplitLemLeft.
    lia.
  Qed.

  Definition interpSplit : Word ->
    (*"""
    Field #1. This field stores the instruction's opcode,
              which consists of 5 = (clog2 29) bits.
    """*)
    Vector.t bool 5 * 
    (*"""
    Field #2. This field is a bit that is 0 if A is a
              register name and 1 if A is an immediate value.
    """*)
    bool * 
    (*"""
    Field #3. This field stores a register name operand, which consists
              of (clog2 [registerCount]) bits. It is all 0's when not
              used. This is the name of the instruction's destination
              register (i.e. the one to be modified) if any.
    """*)
    Vector.t bool (clog2 registerCount) *
    (*"""
    Field #4. This field stores a register name operand, which consists
              of (clog2 [registerCount]) bits. It is all 0's when not
              used. This is the name of a register operand (if any) that
              will *not* be modified by the instruction.
    """*)
    Vector.t bool (clog2 registerCount) *
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
           (ri rj : Vector.t bool (clog2 registerCount))
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
    2 ^ clog2 registerCount = registerCount ->
    Vector.t bool (clog2 registerCount) ->
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
    (eq: 2 ^ clog2 registerCount = registerCount)
    (v: Vector.t bool (clog2 registerCount)),
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
     clearify what should be done if a register Id is too big.
     I've made the opcode answer1 in this case, but this may 
     not be intended behaviour.

     Such a situation is impossible if registerCount is a 
     power of 2 (see oreg2powProp above).
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
    | ((((op, isReg), pri), prj), _) =>
      let ri := oreg pri in
      let rj := oreg prj in
      let ow := oreg w2 in
      match proj1_sig (bitvector_fin_big op) with
      | 0 =>  OpcodeDecodeRiRjA andI isReg ri rj w2 ow
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

  Theorem and_decode_register_correct :
    forall (ri rj : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b0; b0; b0; b0; b0] ++ [b1] ++ ri ++ rj ++ padding))) A =
    andI (regFit ri lti) (regFit rj ltj) (inl (regFit A ltA)).
  Proof. rirjAProof_register. Qed.
 
  Theorem and_decode_word_correct :
    forall (ri rj : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b0; b0; b0; b0; b0] ++ [b0] ++ ri ++ rj ++ padding))) A =
    andI (regFit ri lti) (regFit rj ltj) (inr A).
  Proof. rirjAProof_word. Qed.

Theorem or_decode_register_correct :
    forall (ri rj : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b0; b0; b0; b0; b1] ++ [b1] ++ ri ++ rj ++ padding))) A =
    orI (regFit ri lti) (regFit rj ltj) (inl (regFit A ltA)).
  Proof. rirjAProof_register. Qed.
 
  Theorem or_decode_word_correct :
    forall (ri rj : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b0; b0; b0; b0; b1] ++ [b0] ++ ri ++ rj ++ padding))) A =
    orI (regFit ri lti) (regFit rj ltj) (inr A).
  Proof. rirjAProof_word. Qed.

  Theorem xor_decode_register_correct :
    forall (ri rj : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b0; b0; b0; b1; b0] ++ [b1] ++ ri ++ rj ++ padding))) A =
    xorI (regFit ri lti) (regFit rj ltj) (inl (regFit A ltA)).
  Proof. rirjAProof_register. Qed.
 
  Theorem xor_decode_word_correct :
    forall (ri rj : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b0; b0; b0; b1; b0] ++ [b0] ++ ri ++ rj ++ padding ))) A =
    xorI (regFit ri lti) (regFit rj ltj) (inr A).
  Proof. rirjAProof_word. Qed.
      
  Theorem not_decode_register_correct :
    forall (ri pad : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b0; b0; b0; b1; b1] ++ [b1] ++ ri ++ pad ++ padding))) A =
    notI (regFit ri lti) (inl (regFit A ltA)).
  Proof. riAProof_register. Qed.
 
  Theorem not_decode_word_correct :
    forall (ri pad : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b0; b0; b0; b1; b1] ++ [b0] ++ ri ++ pad ++ padding))) A =
    notI (regFit ri lti) (inr A).
  Proof. riAProof_word. Qed.

Theorem add_decode_register_correct :
    forall (ri rj : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b0; b0; b1; b0; b0] ++ [b1] ++ ri ++ rj ++ padding))) A =
    addI (regFit ri lti) (regFit rj ltj) (inl (regFit A ltA)).
  Proof. rirjAProof_register. Qed.
 
  Theorem add_decode_word_correct :
    forall (ri rj : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b0; b0; b1; b0; b0] ++ [b0] ++ ri ++ rj ++ padding))) A =
    addI (regFit ri lti) (regFit rj ltj) (inr A).
  Proof. rirjAProof_word. Qed.

Theorem sub_decode_register_correct :
    forall (ri rj : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b0; b0; b1; b0; b1] ++ [b1] ++ ri ++ rj ++ padding))) A =
    subI (regFit ri lti) (regFit rj ltj) (inl (regFit A ltA)).
  Proof. rirjAProof_register. Qed.
 
  Theorem sub_decode_word_correct :
    forall (ri rj : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b0; b0; b1; b0; b1] ++ [b0] ++ ri ++ rj ++ padding))) A =
    subI (regFit ri lti) (regFit rj ltj) (inr A).
  Proof. rirjAProof_word. Qed.

  Theorem mull_decode_register_correct :
    forall (ri rj : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b0; b0; b1; b1; b0] ++ [b1] ++ ri ++ rj ++ padding))) A =
    mullI (regFit ri lti) (regFit rj ltj) (inl (regFit A ltA)).
  Proof. rirjAProof_register. Qed.
 
  Theorem mull_decode_word_correct :
    forall (ri rj : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b0; b0; b1; b1; b0] ++ [b0] ++ ri ++ rj ++ padding))) A =
    mullI (regFit ri lti) (regFit rj ltj) (inr A).
  Proof. rirjAProof_word. Qed.

  Theorem umulh_decode_register_correct :
    forall (ri rj : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b0; b0; b1; b1; b1] ++ [b1] ++ ri ++ rj ++ padding))) A =
    umulhI (regFit ri lti) (regFit rj ltj) (inl (regFit A ltA)).
  Proof. rirjAProof_register. Qed.
 
  Theorem umulh_decode_word_correct :
    forall (ri rj : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b0; b0; b1; b1; b1] ++ [b0] ++ ri ++ rj ++ padding))) A =
    umulhI (regFit ri lti) (regFit rj ltj) (inr A).
  Proof. rirjAProof_word. Qed.

  Theorem smulh_decode_register_correct :
    forall (ri rj : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b0; b1; b0; b0; b0] ++ [b1] ++ ri ++ rj ++ padding))) A =
    smulhI (regFit ri lti) (regFit rj ltj) (inl (regFit A ltA)).
  Proof. rirjAProof_register. Qed.
 
  Theorem smulh_decode_word_correct :
    forall (ri rj : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b0; b1; b0; b0; b0] ++ [b0] ++ ri ++ rj ++ padding))) A =
    smulhI (regFit ri lti) (regFit rj ltj) (inr A).
  Proof. rirjAProof_word. Qed.

  Theorem udiv_decode_register_correct :
    forall (ri rj : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b0; b1; b0; b0; b1] ++ [b1] ++ ri ++ rj ++ padding))) A =
    udivI (regFit ri lti) (regFit rj ltj) (inl (regFit A ltA)).
  Proof. rirjAProof_register. Qed.
 
  Theorem udiv_decode_word_correct :
    forall (ri rj : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b0; b1; b0; b0; b1] ++ [b0] ++ ri ++ rj ++ padding))) A =
    udivI (regFit ri lti) (regFit rj ltj) (inr A).
  Proof. rirjAProof_word. Qed.

  Theorem umod_decode_register_correct :
    forall (ri rj : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b0; b1; b0; b1; b0] ++ [b1] ++ ri ++ rj ++ padding))) A =
    umodI (regFit ri lti) (regFit rj ltj) (inl (regFit A ltA)).
  Proof. rirjAProof_register. Qed.
 
  Theorem umod_decode_word_correct :
    forall (ri rj : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b0; b1; b0; b1; b0] ++ [b0] ++ ri ++ rj ++ padding))) A =
    umodI (regFit ri lti) (regFit rj ltj) (inr A).
  Proof. rirjAProof_word. Qed.

  Theorem shl_decode_register_correct :
    forall (ri rj : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b0; b1; b0; b1; b1] ++ [b1] ++ ri ++ rj ++ padding))) A =
    shlI (regFit ri lti) (regFit rj ltj) (inl (regFit A ltA)).
  Proof. rirjAProof_register. Qed.
 
  Theorem shl_decode_word_correct :
    forall (ri rj : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b0; b1; b0; b1; b1] ++ [b0] ++ ri ++ rj ++ padding))) A =
    shlI (regFit ri lti) (regFit rj ltj) (inr A).
  Proof. rirjAProof_word. Qed.

  Theorem shr_decode_register_correct :
    forall (ri rj : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b0; b1; b1; b0; b0] ++ [b1] ++ ri ++ rj ++ padding))) A =
    shrI (regFit ri lti) (regFit rj ltj) (inl (regFit A ltA)).
  Proof. rirjAProof_register. Qed.
 
  Theorem shr_decode_word_correct :
    forall (ri rj : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin_big rj) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b0; b1; b1; b0; b0] ++ [b0] ++ ri ++ rj ++ padding))) A =
    shrI (regFit ri lti) (regFit rj ltj) (inr A).
  Proof. rirjAProof_word. Qed.

  Theorem cmpe_decode_register_correct :
    forall (pad ri : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b0; b1; b1; b0; b1] ++ [b1] ++ pad ++ ri ++ padding))) A =
    cmpeI (regFit ri lti) (inl (regFit A ltA)).
  Proof. rjAProof_register. Qed.

  Theorem cmpe_decode_word_correct :
    forall (pad ri : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b0; b1; b1; b0; b1] ++ [b0] ++ pad ++ ri ++ padding))) A =
    cmpeI (regFit ri lti) (inr A).
  Proof. rjAProof_word. Qed.

  Theorem cmpa_decode_register_correct :
    forall (pad ri : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b0; b1; b1; b1; b0] ++ [b1] ++ pad ++ ri ++ padding))) A =
    cmpaI (regFit ri lti) (inl (regFit A ltA)).
  Proof. rjAProof_register. Qed.
 
  Theorem cmpa_decode_word_correct :
    forall (pad ri : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b0; b1; b1; b1; b0] ++ [b0] ++ pad ++ ri ++ padding))) A =
    cmpaI (regFit ri lti) (inr A).
  Proof. rjAProof_word. Qed.

  Theorem cmpae_decode_register_correct :
    forall (pad ri : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b0; b1; b1; b1; b1] ++ [b1] ++ pad ++ ri ++ padding))) A =
    cmpaeI (regFit ri lti) (inl (regFit A ltA)).
  Proof. rjAProof_register. Qed.
 
  Theorem cmpae_decode_word_correct :
    forall (pad ri : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b0; b1; b1; b1; b1] ++ [b0] ++ pad ++ ri ++ padding))) A =
    cmpaeI (regFit ri lti) (inr A).
  Proof. rjAProof_word. Qed.

  Theorem cmpg_decode_register_correct :
    forall (pad ri : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b1; b0; b0; b0; b0] ++ [b1] ++ pad ++ ri ++ padding))) A =
    cmpgI (regFit ri lti) (inl (regFit A ltA)).
  Proof. rjAProof_register. Qed.
 
  Theorem cmpg_decode_word_correct :
    forall (pad ri : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b1; b0; b0; b0; b0] ++ [b0] ++ pad ++ ri ++ padding))) A =
    cmpgI (regFit ri lti) (inr A).
  Proof. rjAProof_word. Qed.

  Theorem cmpge_decode_register_correct :
    forall (pad ri : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b1; b0; b0; b0; b1] ++ [b1] ++ pad ++ ri ++ padding))) A =
    cmpgeI (regFit ri lti) (inl (regFit A ltA)).
  Proof. rjAProof_register. Qed.
 
  Theorem cmpge_decode_word_correct :
    forall (pad ri : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b1; b0; b0; b0; b1] ++ [b0] ++ pad ++ ri ++ padding))) A =
    cmpgeI (regFit ri lti) (inr A).
  Proof. rjAProof_word. Qed.
      
  Theorem mov_decode_register_correct :
    forall (ri pad : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b1; b0; b0; b1; b0] ++ [b1] ++ ri ++ pad ++ padding))) A =
    movI (regFit ri lti) (inl (regFit A ltA)).
  Proof. riAProof_register. Qed.

  Theorem mov_decode_word_correct :
    forall (ri pad : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b1; b0; b0; b1; b0] ++ [b0] ++ ri ++ pad ++ padding))) A =
    movI (regFit ri lti) (inr A).
  Proof. riAProof_word. Qed.

  Theorem cmov_decode_register_correct :
    forall (ri pad : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b1; b0; b0; b1; b1] ++ [b1] ++ ri ++ pad ++ padding))) A =
    cmovI (regFit ri lti) (inl (regFit A ltA)).
  Proof. riAProof_register. Qed.
 
  Theorem cmov_decode_word_correct :
    forall (ri pad : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b1; b0; b0; b1; b1] ++ [b0] ++ ri ++ pad ++ padding))) A =
    cmovI (regFit ri lti) (inr A).
  Proof. riAProof_word. Qed.

  Theorem jmp_decode_register_correct :
    forall (pad1 pad2 : Vector.t bool (clog2 registerCount))
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b1; b0; b1; b0; b0] ++ [b1] ++ pad1 ++ pad2 ++ padding))) A =
    jmpI (inl (regFit A ltA)).
  Proof. AProof_register. Qed.
 
  Theorem jmp_decode_word_correct :
    forall (pad1 pad2 : Vector.t bool (clog2 registerCount))
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b1; b0; b1; b0; b0] ++ [b0] ++ pad1 ++ pad2 ++ padding))) A =
    jmpI (inr A).
  Proof. AProof_word. Qed.

  Theorem cjmp_decode_register_correct :
    forall (pad1 pad2 : Vector.t bool (clog2 registerCount))
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b1; b0; b1; b0; b1] ++ [b1] ++ pad1 ++ pad2 ++ padding))) A =
    cjmpI (inl (regFit A ltA)).
  Proof. AProof_register. Qed.
 
  Theorem cjmp_decode_word_correct :
    forall (pad1 pad2 : Vector.t bool (clog2 registerCount))
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b1; b0; b1; b0; b1] ++ [b0] ++ pad1 ++ pad2 ++ padding))) A =
    cjmpI (inr A).
  Proof. AProof_word. Qed.

  Theorem cnjmp_decode_register_correct :
    forall (pad1 pad2 : Vector.t bool (clog2 registerCount))
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b1; b0; b1; b1; b0] ++ [b1] ++ pad1 ++ pad2 ++ padding))) A =
    cnjmpI (inl (regFit A ltA)).
  Proof. AProof_register. Qed.
 
  Theorem cnjmp_decode_word_correct :
    forall (pad1 pad2 : Vector.t bool (clog2 registerCount))
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b1; b0; b1; b1; b0] ++ [b0] ++ pad1 ++ pad2 ++ padding))) A =
    cnjmpI (inr A).
  Proof. AProof_word. Qed.

  Theorem store_b_decode_register_correct :
    forall (ri pad : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b1; b1; b0; b1; b0] ++ [b1] ++ ri ++ pad ++ padding))) A =
    store_bI (regFit ri lti) (inl (regFit A ltA)).
  Proof. riAProof_register. Qed.
 
  Theorem store_b_decode_word_correct :
    forall (ri pad : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b1; b1; b0; b1; b0] ++ [b0]    ++ ri  ++ pad ++ padding))) A =
    store_bI (regFit ri lti) (inr A).
  Proof. riAProof_word. Qed.

  Theorem load_b_decode_register_correct :
    forall (ri pad : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b1; b1; b0; b1; b1] ++ [b1] ++ ri ++ pad ++ padding))) A =
    load_bI (regFit ri lti) (inl (regFit A ltA)).
  Proof. riAProof_register. Qed.
 
  Theorem load_b_decode_word_correct :
    forall (ri pad : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b1; b1; b0; b1; b1] ++ [b0]    ++ ri  ++ pad ++ padding))) A =
    load_bI (regFit ri lti) (inr A).
  Proof. riAProof_word. Qed.

  Theorem store_w_decode_register_correct :
    forall (ri pad : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b1; b1; b1; b0; b0] ++ [b1] ++ ri ++ pad ++ padding))) A =
    store_wI (regFit ri lti) (inl (regFit A ltA)).
  Proof. riAProof_register. Qed.
 
  Theorem store_w_decode_word_correct :
    forall (ri pad : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b1; b1; b1; b0; b0] ++ [b0]    ++ ri  ++ pad ++ padding))) A =
    store_wI (regFit ri lti) (inr A).
  Proof. riAProof_word. Qed.

  Theorem load_w_decode_register_correct :
    forall (ri pad : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b1; b1; b1; b0; b1] ++ [b1] ++ ri ++ pad ++ padding))) A =
    load_wI (regFit ri lti) (inl (regFit A ltA)).
  Proof. riAProof_register. Qed.
 
  Theorem load_w_decode_word_correct :
    forall (ri pad : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b1; b1; b1; b0; b1] ++ [b0]    ++ ri  ++ pad ++ padding))) A =
    load_wI (regFit ri lti) (inr A).
  Proof. riAProof_word. Qed.

  Theorem read_decode_register_correct :
    forall (ri pad : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b1; b1; b1; b1; b0] ++ [b1] ++ ri ++ pad ++ padding))) A =
    readI (regFit ri lti) (inl (regFit A ltA)).
  Proof. riAProof_register. Qed.
 
  Theorem read_decode_word_correct :
    forall (ri pad : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin_big ri) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b1; b1; b1; b1; b0] ++ [b0] ++ ri  ++ pad ++ padding))) A =
    readI (regFit ri lti) (inr A).
  Proof. riAProof_word. Qed.

  Theorem answer_decode_register_correct :
    forall (pad1 pad2 : Vector.t bool (clog2 registerCount))
           (A : Word)
           (ltA : proj1_sig (bitvector_fin_big A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b1; b1; b1; b1; b1] ++ [b1] ++ pad1 ++ pad2 ++ padding))) A =
    answerI (inl (regFit A ltA)).
  Proof. AProof_register. Qed.
 
  Theorem answer_decode_word_correct :
    forall (pad1 pad2 : Vector.t bool (clog2 registerCount))
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ([b1; b1; b1; b1; b1] ++ [b0] ++ pad1 ++ pad2 ++ padding))) A =
    answerI (inr A).
  Proof. AProof_word. Qed.

End TinyRAMDecodOps.


