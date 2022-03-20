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
      code ++ (b :: []) ++ ri ++ rj ++ padding
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
    destruct (bitvector_fin v).
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
    destruct (bitvector_fin v).
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
    destruct (bitvector_fin v) as [bfv bfvProp].
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
    proj1_sig (bitvector_fin v) < registerCount -> 
    regId.
    intros n v ft.
    exists (proj1_sig (bitvector_fin v)).
    exact ft.
  Defined.

  Theorem regFitProp :
    forall {n} (v : Vector.t bool n)
    (lt : proj1_sig (bitvector_fin v) < registerCount),
    oreg v = Some (regFit v lt).
  Proof.
    intros n v lt.
    unfold oreg, regFit.
    destruct (bitvector_fin v) as [bfv bfvProp].
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
    apply fin_bitvector.
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
  Definition OpcodeDecode (w1 w2 : Word) : OpcodeI.
    apply interpSplit in w1;
    destruct w1 as [[[[op isReg] ri] rj] _].
    apply oreg in ri, rj. apply oreg in w2 as w2reg.
    apply bitvector_fin in op; destruct op.
    destruct x. { exact (OpcodeDecodeRiRjA andI isReg ri rj w2 w2reg). }
    destruct x. { exact (OpcodeDecodeRiA cmpgI isReg rj w2 w2reg). }
    destruct x. { exact (OpcodeDecodeRiRjA smulhI isReg ri rj w2 w2reg). }
    (*"""
    If pc is not an integer in [...] the number of instructions in P,
    then the instruction answer 1 is fetched as default.)
    """*)
    destruct x. { exact answer1. }
    destruct x. { exact (OpcodeDecodeRiRjA addI isReg ri rj w2 w2reg). }
    destruct x. { exact (OpcodeDecodeA jmpI isReg w2 w2reg). }
    destruct x. { exact (OpcodeDecodeRiRjA shrI isReg ri rj w2 w2reg). }
    destruct x. { exact (OpcodeDecodeRiA store_wI isReg ri w2 w2reg). }
    destruct x. { exact (OpcodeDecodeRiRjA xorI isReg ri rj w2 w2reg). }
    destruct x. { exact (OpcodeDecodeRiA movI isReg ri w2 w2reg). }
    destruct x. { exact (OpcodeDecodeRiRjA umodI isReg ri rj w2 w2reg). }
    destruct x. { exact (OpcodeDecodeRiA store_bI isReg ri w2 w2reg). }
    destruct x. { exact (OpcodeDecodeRiRjA mullI isReg ri rj w2 w2reg). }
    destruct x. { exact (OpcodeDecodeA cnjmpI isReg w2 w2reg). }
    destruct x. { exact (OpcodeDecodeRiA cmpaI isReg rj w2 w2reg). }
    destruct x. { exact (OpcodeDecodeRiA readI isReg ri w2 w2reg). }
    destruct x. { exact (OpcodeDecodeRiRjA orI isReg ri rj w2 w2reg). }
    destruct x. { exact (OpcodeDecodeRiA cmpgeI isReg rj w2 w2reg). }
    destruct x. { exact (OpcodeDecodeRiRjA udivI isReg ri rj w2 w2reg). }
    destruct x. { exact answer1. }
    destruct x. { exact (OpcodeDecodeRiRjA subI isReg ri rj w2 w2reg). }
    destruct x. { exact (OpcodeDecodeA cjmpI isReg w2 w2reg). }
    destruct x. { exact (OpcodeDecodeRiA cmpeI isReg rj w2 w2reg). }
    destruct x. { exact (OpcodeDecodeRiA load_wI isReg ri w2 w2reg). }
    destruct x. { exact (OpcodeDecodeRiA notI isReg ri w2 w2reg). }
    destruct x. { exact (OpcodeDecodeRiA cmovI isReg ri w2 w2reg). }
    destruct x. { exact (OpcodeDecodeRiRjA shlI isReg ri rj w2 w2reg). }
    destruct x. { exact (OpcodeDecodeRiA load_bI isReg ri w2 w2reg). }
    destruct x. { exact (OpcodeDecodeRiRjA umulhI isReg ri rj w2 w2reg). }
    destruct x. { exact answer1. }
    destruct x. { exact (OpcodeDecodeRiA cmpaeI isReg rj w2 w2reg). }
    exact (OpcodeDecodeA answerI isReg w2 w2reg).
  Defined.

  (***
    This section is based on Table 2 of pg. 16 in spec. 
  ***)
 
  Theorem and_decode_register_correct :
    forall (ri rj : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin rj) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((false :: false :: false :: false :: false :: []) ++
       (true :: [])                                     ++
       ri                                                ++
       rj                                                ++
       padding
      ))) A =
    andI (regFit ri lti) (regFit rj ltj) (inl (regFit A ltA)).
  Proof.
    intros ri rj lti ltj A ltA padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp ri lti), (regFitProp rj ltj), (regFitProp A ltA).
    reflexivity.
  Qed.
 
  Theorem and_decode_word_correct :
    forall (ri rj : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin rj) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((false :: false :: false :: false :: false :: []) ++
       (false :: [])                                     ++
       ri                                                ++
       rj                                                ++
       padding
      ))) A =
    andI (regFit ri lti) (regFit rj ltj) (inr A).
  Proof.
    intros ri rj lti ltj A padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp ri lti), (regFitProp rj ltj).
    reflexivity.
  Qed.

Theorem or_decode_register_correct :
    forall (ri rj : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin rj) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((false :: false :: false :: false :: true :: []) ++
       (true :: [])                                     ++
       ri                                                ++
       rj                                                ++
       padding
      ))) A =
    orI (regFit ri lti) (regFit rj ltj) (inl (regFit A ltA)).
  Proof.
    intros ri rj lti ltj A ltA padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp ri lti), (regFitProp rj ltj), (regFitProp A ltA).
    reflexivity.
  Qed.
 
  Theorem or_decode_word_correct :
    forall (ri rj : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin rj) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((false :: false :: false :: false :: true :: []) ++
       (false :: [])                                     ++
       ri                                                ++
       rj                                                ++
       padding
      ))) A =
    orI (regFit ri lti) (regFit rj ltj) (inr A).
  Proof.
    intros ri rj lti ltj A padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp ri lti), (regFitProp rj ltj).
    reflexivity.
  Qed.

Theorem xor_decode_register_correct :
    forall (ri rj : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin rj) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((false :: false :: false :: true :: false :: []) ++
       (true :: [])                                     ++
       ri                                                ++
       rj                                                ++
       padding
      ))) A =
    xorI (regFit ri lti) (regFit rj ltj) (inl (regFit A ltA)).
  Proof.
    intros ri rj lti ltj A ltA padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp ri lti), (regFitProp rj ltj), (regFitProp A ltA).
    reflexivity.
  Qed.
 
  Theorem xor_decode_word_correct :
    forall (ri rj : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin rj) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((false :: false :: false :: true :: false :: []) ++
       (false :: [])                                     ++
       ri                                                ++
       rj                                                ++
       padding
      ))) A =
    xorI (regFit ri lti) (regFit rj ltj) (inr A).
  Proof.
    intros ri rj lti ltj A padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp ri lti), (regFitProp rj ltj).
    reflexivity.
  Qed.
      
  Theorem not_decode_register_correct :
    forall (ri pad : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((false :: false :: false :: true :: true :: [])  ++
       (true :: [])                                     ++
       ri                                               ++
       pad                                              ++
       padding
      ))) A =
    notI (regFit ri lti) (inl (regFit A ltA)).
  Proof.
    intros ri pad lti A ltA padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp ri lti), (regFitProp A ltA).
    reflexivity.
  Qed.
 
  Theorem not_decode_word_correct :
    forall (ri rj : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin rj) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((false :: false :: false :: true :: true :: []) ++
       (false :: [])                                     ++
       ri                                                ++
       rj                                                ++
       padding
      ))) A =
    notI (regFit ri lti) (inr A).
  Proof.
    intros ri rj lti ltj A padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp ri lti).
    reflexivity.
  Qed.

Theorem add_decode_register_correct :
    forall (ri rj : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin rj) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((false :: false :: true :: false :: false :: []) ++
       (true :: [])                                     ++
       ri                                                ++
       rj                                                ++
       padding
      ))) A =
    addI (regFit ri lti) (regFit rj ltj) (inl (regFit A ltA)).
  Proof.
    intros ri rj lti ltj A ltA padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp ri lti), (regFitProp rj ltj), (regFitProp A ltA).
    reflexivity.
  Qed.
 
  Theorem add_decode_word_correct :
    forall (ri rj : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin rj) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((false :: false :: true :: false :: false :: []) ++
       (false :: [])                                     ++
       ri                                                ++
       rj                                                ++
       padding
      ))) A =
    addI (regFit ri lti) (regFit rj ltj) (inr A).
  Proof.
    intros ri rj lti ltj A padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp ri lti), (regFitProp rj ltj).
    reflexivity.
  Qed.

Theorem sub_decode_register_correct :
    forall (ri rj : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin rj) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((false :: false :: true :: false :: true :: []) ++
       (true :: [])                                     ++
       ri                                                ++
       rj                                                ++
       padding
      ))) A =
    subI (regFit ri lti) (regFit rj ltj) (inl (regFit A ltA)).
  Proof.
    intros ri rj lti ltj A ltA padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp ri lti), (regFitProp rj ltj), (regFitProp A ltA).
    reflexivity.
  Qed.
 
  Theorem sub_decode_word_correct :
    forall (ri rj : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin rj) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((false :: false :: true :: false :: true :: []) ++
       (false :: [])                                     ++
       ri                                                ++
       rj                                                ++
       padding
      ))) A =
    subI (regFit ri lti) (regFit rj ltj) (inr A).
  Proof.
    intros ri rj lti ltj A padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp ri lti), (regFitProp rj ltj).
    reflexivity.
  Qed.

  Theorem mull_decode_register_correct :
    forall (ri rj : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin rj) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((false :: false :: true :: true :: false :: []) ++
       (true :: [])                                     ++
       ri                                                ++
       rj                                                ++
       padding
      ))) A =
    mullI (regFit ri lti) (regFit rj ltj) (inl (regFit A ltA)).
  Proof.
    intros ri rj lti ltj A ltA padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp ri lti), (regFitProp rj ltj), (regFitProp A ltA).
    reflexivity.
  Qed.
 
  Theorem mull_decode_word_correct :
    forall (ri rj : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin rj) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((false :: false :: true :: true :: false :: []) ++
       (false :: [])                                     ++
       ri                                                ++
       rj                                                ++
       padding
      ))) A =
    mullI (regFit ri lti) (regFit rj ltj) (inr A).
  Proof.
    intros ri rj lti ltj A padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp ri lti), (regFitProp rj ltj).
    reflexivity.
  Qed.

  Theorem umulh_decode_register_correct :
    forall (ri rj : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin rj) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((false :: false :: true :: true :: true :: []) ++
       (true :: [])                                     ++
       ri                                                ++
       rj                                                ++
       padding
      ))) A =
    umulhI (regFit ri lti) (regFit rj ltj) (inl (regFit A ltA)).
  Proof.
    intros ri rj lti ltj A ltA padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp ri lti), (regFitProp rj ltj), (regFitProp A ltA).
    reflexivity.
  Qed.
 
  Theorem umulh_decode_word_correct :
    forall (ri rj : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin rj) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((false :: false :: true :: true :: true :: []) ++
       (false :: [])                                     ++
       ri                                                ++
       rj                                                ++
       padding
      ))) A =
    umulhI (regFit ri lti) (regFit rj ltj) (inr A).
  Proof.
    intros ri rj lti ltj A padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp ri lti), (regFitProp rj ltj).
    reflexivity.
  Qed.

  Theorem smulh_decode_register_correct :
    forall (ri rj : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin rj) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((false :: true :: false :: false :: false :: []) ++
       (true :: [])                                     ++
       ri                                                ++
       rj                                                ++
       padding
      ))) A =
    smulhI (regFit ri lti) (regFit rj ltj) (inl (regFit A ltA)).
  Proof.
    intros ri rj lti ltj A ltA padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp ri lti), (regFitProp rj ltj), (regFitProp A ltA).
    reflexivity.
  Qed.
 
  Theorem smulh_decode_word_correct :
    forall (ri rj : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin rj) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((false :: true :: false :: false :: false :: []) ++
       (false :: [])                                     ++
       ri                                                ++
       rj                                                ++
       padding
      ))) A =
    smulhI (regFit ri lti) (regFit rj ltj) (inr A).
  Proof.
    intros ri rj lti ltj A padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp ri lti), (regFitProp rj ltj).
    reflexivity.
  Qed.

  Theorem udiv_decode_register_correct :
    forall (ri rj : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin rj) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((false :: true :: false :: false :: true :: []) ++
       (true :: [])                                     ++
       ri                                                ++
       rj                                                ++
       padding
      ))) A =
    udivI (regFit ri lti) (regFit rj ltj) (inl (regFit A ltA)).
  Proof.
    intros ri rj lti ltj A ltA padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp ri lti), (regFitProp rj ltj), (regFitProp A ltA).
    reflexivity.
  Qed.
 
  Theorem udiv_decode_word_correct :
    forall (ri rj : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin rj) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((false :: true :: false :: false :: true :: []) ++
       (false :: [])                                     ++
       ri                                                ++
       rj                                                ++
       padding
      ))) A =
    udivI (regFit ri lti) (regFit rj ltj) (inr A).
  Proof.
    intros ri rj lti ltj A padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp ri lti), (regFitProp rj ltj).
    reflexivity.
  Qed.

  Theorem umod_decode_register_correct :
    forall (ri rj : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin rj) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((false :: true :: false :: true :: false :: []) ++
       (true :: [])                                     ++
       ri                                                ++
       rj                                                ++
       padding
      ))) A =
    umodI (regFit ri lti) (regFit rj ltj) (inl (regFit A ltA)).
  Proof.
    intros ri rj lti ltj A ltA padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp ri lti), (regFitProp rj ltj), (regFitProp A ltA).
    reflexivity.
  Qed.
 
  Theorem umod_decode_word_correct :
    forall (ri rj : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin rj) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((false :: true :: false :: true :: false :: []) ++
       (false :: [])                                     ++
       ri                                                ++
       rj                                                ++
       padding
      ))) A =
    umodI (regFit ri lti) (regFit rj ltj) (inr A).
  Proof.
    intros ri rj lti ltj A padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp ri lti), (regFitProp rj ltj).
    reflexivity.
  Qed.

  Theorem shl_decode_register_correct :
    forall (ri rj : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin rj) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((false :: true :: false :: true :: true :: []) ++
       (true :: [])                                     ++
       ri                                                ++
       rj                                                ++
       padding
      ))) A =
    shlI (regFit ri lti) (regFit rj ltj) (inl (regFit A ltA)).
  Proof.
    intros ri rj lti ltj A ltA padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp ri lti), (regFitProp rj ltj), (regFitProp A ltA).
    reflexivity.
  Qed.
 
  Theorem shl_decode_word_correct :
    forall (ri rj : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin rj) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((false :: true :: false :: true :: true :: []) ++
       (false :: [])                                     ++
       ri                                                ++
       rj                                                ++
       padding
      ))) A =
    shlI (regFit ri lti) (regFit rj ltj) (inr A).
  Proof.
    intros ri rj lti ltj A padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp ri lti), (regFitProp rj ltj).
    reflexivity.
  Qed.

  Theorem shr_decode_register_correct :
    forall (ri rj : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin rj) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((false :: true :: true :: false :: false :: []) ++
       (true :: [])                                     ++
       ri                                                ++
       rj                                                ++
       padding
      ))) A =
    shrI (regFit ri lti) (regFit rj ltj) (inl (regFit A ltA)).
  Proof.
    intros ri rj lti ltj A ltA padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp ri lti), (regFitProp rj ltj), (regFitProp A ltA).
    reflexivity.
  Qed.
 
  Theorem shr_decode_word_correct :
    forall (ri rj : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin ri) < registerCount)
           (ltj : proj1_sig (bitvector_fin rj) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((false :: true :: true :: false :: false :: []) ++
       (false :: [])                                     ++
       ri                                                ++
       rj                                                ++
       padding
      ))) A =
    shrI (regFit ri lti) (regFit rj ltj) (inr A).
  Proof.
    intros ri rj lti ltj A padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp ri lti), (regFitProp rj ltj).
    reflexivity.
  Qed.

  Theorem cmpe_decode_register_correct :
    forall (pad ri : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((false :: true :: true :: false :: true :: [])  ++
       (true :: [])                                     ++
       pad                                              ++
       ri                                               ++
       padding
      ))) A =
    cmpeI (regFit ri lti) (inl (regFit A ltA)).
  Proof.
    intros pad ri lti A ltA padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp ri lti), (regFitProp A ltA).
    reflexivity.
  Qed.
 
  Theorem cmpe_decode_word_correct :
    forall (pad ri : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin ri) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((false :: true :: true :: false :: true :: []) ++
       (false :: [])                                     ++
       pad                                                ++
       ri                                                ++
       padding
      ))) A =
    cmpeI (regFit ri lti) (inr A).
  Proof.
    intros pad ri lti A padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp ri lti).
    reflexivity.
  Qed.

  Theorem cmpa_decode_register_correct :
    forall (pad ri : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((false :: true :: true :: true :: false :: [])  ++
       (true :: [])                                     ++
       pad                                              ++
       ri                                               ++
       padding
      ))) A =
    cmpaI (regFit ri lti) (inl (regFit A ltA)).
  Proof.
    intros pad ri lti A ltA padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp ri lti), (regFitProp A ltA).
    reflexivity.
  Qed.
 
  Theorem cmpa_decode_word_correct :
    forall (pad ri : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin ri) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((false :: true :: true :: true :: false :: []) ++
       (false :: [])                                     ++
       pad                                                ++
       ri                                                ++
       padding
      ))) A =
    cmpaI (regFit ri lti) (inr A).
  Proof.
    intros pad ri lti A padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp ri lti).
    reflexivity.
  Qed.

  Theorem cmpae_decode_register_correct :
    forall (pad ri : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((false :: true :: true :: true :: true :: [])  ++
       (true :: [])                                     ++
       pad                                              ++
       ri                                               ++
       padding
      ))) A =
    cmpaeI (regFit ri lti) (inl (regFit A ltA)).
  Proof.
    intros pad ri lti A ltA padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp ri lti), (regFitProp A ltA).
    reflexivity.
  Qed.
 
  Theorem cmpae_decode_word_correct :
    forall (pad ri : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin ri) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((false :: true :: true :: true :: true :: []) ++
       (false :: [])                                     ++
       pad                                                ++
       ri                                                ++
       padding
      ))) A =
    cmpaeI (regFit ri lti) (inr A).
  Proof.
    intros pad ri lti A padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp ri lti).
    reflexivity.
  Qed.

  Theorem cmpg_decode_register_correct :
    forall (pad ri : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((true :: false :: false :: false :: false :: [])  ++
       (true :: [])                                     ++
       pad                                              ++
       ri                                               ++
       padding
      ))) A =
    cmpgI (regFit ri lti) (inl (regFit A ltA)).
  Proof.
    intros pad ri lti A ltA padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp ri lti), (regFitProp A ltA).
    reflexivity.
  Qed.
 
  Theorem cmpg_decode_word_correct :
    forall (pad ri : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin ri) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((true :: false :: false :: false :: false :: []) ++
       (false :: [])                                     ++
       pad                                                ++
       ri                                                ++
       padding
      ))) A =
    cmpgI (regFit ri lti) (inr A).
  Proof.
    intros pad ri lti A padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp ri lti).
    reflexivity.
  Qed.

  Theorem cmpge_decode_register_correct :
    forall (pad ri : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((true :: false :: false :: false :: true :: [])  ++
       (true :: [])                                     ++
       pad                                              ++
       ri                                               ++
       padding
      ))) A =
    cmpgeI (regFit ri lti) (inl (regFit A ltA)).
  Proof.
    intros pad ri lti A ltA padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp ri lti), (regFitProp A ltA).
    reflexivity.
  Qed.
 
  Theorem cmpge_decode_word_correct :
    forall (pad ri : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin ri) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((true :: false :: false :: false :: true :: []) ++
       (false :: [])                                     ++
       pad                                                ++
       ri                                                ++
       padding
      ))) A =
    cmpgeI (regFit ri lti) (inr A).
  Proof.
    intros pad ri lti A padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp ri lti).
    reflexivity.
  Qed.
      
  Theorem mov_decode_register_correct :
    forall (ri pad : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((true :: false :: false :: true :: false :: [])  ++
       (true :: [])                                     ++
       ri                                               ++
       pad                                              ++
       padding
      ))) A =
    movI (regFit ri lti) (inl (regFit A ltA)).
  Proof.
    intros ri pad lti A ltA padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp ri lti), (regFitProp A ltA).
    reflexivity.
  Qed.
 
  Theorem mov_decode_word_correct :
    forall (ri pad : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin ri) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((true :: false :: false :: true :: false :: []) ++
       (false :: [])                                     ++
       ri                                                ++
       pad                                                ++
       padding
      ))) A =
    movI (regFit ri lti) (inr A).
  Proof.
    intros ri pad lti A padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp ri lti).
    reflexivity.
  Qed.

  Theorem cmov_decode_register_correct :
    forall (ri pad : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((true :: false :: false :: true :: true :: [])  ++
       (true :: [])                                     ++
       ri                                               ++
       pad                                              ++
       padding
      ))) A =
    cmovI (regFit ri lti) (inl (regFit A ltA)).
  Proof.
    intros ri pad lti A ltA padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp ri lti), (regFitProp A ltA).
    reflexivity.
  Qed.
 
  Theorem cmov_decode_word_correct :
    forall (ri pad : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin ri) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((true :: false :: false :: true :: true :: []) ++
       (false :: [])                                     ++
       ri                                                ++
       pad                                                ++
       padding
      ))) A =
    cmovI (regFit ri lti) (inr A).
  Proof.
    intros ri pad lti A padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp ri lti).
    reflexivity.
  Qed.

  Theorem jmp_decode_register_correct :
    forall (pad1 pad2 : Vector.t bool (clog2 registerCount))
           (A : Word)
           (ltA : proj1_sig (bitvector_fin A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((true :: false :: true :: false :: false :: [])  ++
       (true :: [])                                    ++
       pad1                                            ++
       pad2                                            ++
       padding
      ))) A =
    jmpI (inl (regFit A ltA)).
  Proof.
    intros pad1 pad2 A ltA padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp A ltA).
    reflexivity.
  Qed.
 
  Theorem jmp_decode_word_correct :
    forall (pad1 pad2 : Vector.t bool (clog2 registerCount))
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((true :: false :: true :: false :: false :: []) ++
       (false :: [])                                   ++
       pad1                                            ++
       pad2                                            ++
       padding
      ))) A =
    jmpI (inr A).
  Proof.
    intros pad1 pad2 A padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    reflexivity.
  Qed.

  Theorem cjmp_decode_register_correct :
    forall (pad1 pad2 : Vector.t bool (clog2 registerCount))
           (A : Word)
           (ltA : proj1_sig (bitvector_fin A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((true :: false :: true :: false :: true :: [])  ++
       (true :: [])                                    ++
       pad1                                            ++
       pad2                                            ++
       padding
      ))) A =
    cjmpI (inl (regFit A ltA)).
  Proof.
    intros pad1 pad2 A ltA padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp A ltA).
    reflexivity.
  Qed.
 
  Theorem cjmp_decode_word_correct :
    forall (pad1 pad2 : Vector.t bool (clog2 registerCount))
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((true :: false :: true :: false :: true :: []) ++
       (false :: [])                                   ++
       pad1                                            ++
       pad2                                            ++
       padding
      ))) A =
    cjmpI (inr A).
  Proof.
    intros pad1 pad2 A padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    reflexivity.
  Qed.

  Theorem cnjmp_decode_register_correct :
    forall (pad1 pad2 : Vector.t bool (clog2 registerCount))
           (A : Word)
           (ltA : proj1_sig (bitvector_fin A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((true :: false :: true :: true :: false :: [])  ++
       (true :: [])                                    ++
       pad1                                            ++
       pad2                                            ++
       padding
      ))) A =
    cnjmpI (inl (regFit A ltA)).
  Proof.
    intros pad1 pad2 A ltA padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp A ltA).
    reflexivity.
  Qed.
 
  Theorem cnjmp_decode_word_correct :
    forall (pad1 pad2 : Vector.t bool (clog2 registerCount))
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((true :: false :: true :: true :: false :: []) ++
       (false :: [])                                   ++
       pad1                                            ++
       pad2                                            ++
       padding
      ))) A =
    cnjmpI (inr A).
  Proof.
    intros pad1 pad2 A padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    reflexivity.
  Qed.

  Theorem store_b_decode_register_correct :
    forall (ri pad : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((true :: true :: false :: true :: false :: [])  ++
       (true :: [])                                     ++
       ri                                               ++
       pad                                              ++
       padding
      ))) A =
    store_bI (regFit ri lti) (inl (regFit A ltA)).
  Proof.
    intros ri pad lti A ltA padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp ri lti), (regFitProp A ltA).
    reflexivity.
  Qed.
 
  Theorem store_b_decode_word_correct :
    forall (ri pad : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin ri) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((true :: true :: false :: true :: false :: []) ++
       (false :: [])                                  ++
       ri                                             ++
       pad                                            ++
       padding
      ))) A =
    store_bI (regFit ri lti) (inr A).
  Proof.
    intros ri pad lti A padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp ri lti).
    reflexivity.
  Qed.

  Theorem load_b_decode_register_correct :
    forall (ri pad : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((true :: true :: false :: true :: true :: [])  ++
       (true :: [])                                     ++
       ri                                               ++
       pad                                              ++
       padding
      ))) A =
    load_bI (regFit ri lti) (inl (regFit A ltA)).
  Proof.
    intros ri pad lti A ltA padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp ri lti), (regFitProp A ltA).
    reflexivity.
  Qed.
 
  Theorem load_b_decode_word_correct :
    forall (ri pad : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin ri) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((true :: true :: false :: true :: true :: []) ++
       (false :: [])                                  ++
       ri                                             ++
       pad                                            ++
       padding
      ))) A =
    load_bI (regFit ri lti) (inr A).
  Proof.
    intros ri pad lti A padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp ri lti).
    reflexivity.
  Qed.

  Theorem store_w_decode_register_correct :
    forall (ri pad : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((true :: true :: true :: false :: false :: [])  ++
       (true :: [])                                     ++
       ri                                               ++
       pad                                              ++
       padding
      ))) A =
    store_wI (regFit ri lti) (inl (regFit A ltA)).
  Proof.
    intros ri pad lti A ltA padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp ri lti), (regFitProp A ltA).
    reflexivity.
  Qed.
 
  Theorem store_w_decode_word_correct :
    forall (ri pad : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin ri) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((true :: true :: true :: false :: false :: []) ++
       (false :: [])                                  ++
       ri                                             ++
       pad                                            ++
       padding
      ))) A =
    store_wI (regFit ri lti) (inr A).
  Proof.
    intros ri pad lti A padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp ri lti).
    reflexivity.
  Qed.

  Theorem load_w_decode_register_correct :
    forall (ri pad : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((true :: true :: true :: false :: true :: [])  ++
       (true :: [])                                     ++
       ri                                               ++
       pad                                              ++
       padding
      ))) A =
    load_wI (regFit ri lti) (inl (regFit A ltA)).
  Proof.
    intros ri pad lti A ltA padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp ri lti), (regFitProp A ltA).
    reflexivity.
  Qed.
 
  Theorem load_w_decode_word_correct :
    forall (ri pad : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin ri) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((true :: true :: true :: false :: true :: []) ++
       (false :: [])                                  ++
       ri                                             ++
       pad                                            ++
       padding
      ))) A =
    load_wI (regFit ri lti) (inr A).
  Proof.
    intros ri pad lti A padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp ri lti).
    reflexivity.
  Qed.

  Theorem read_decode_register_correct :
    forall (ri pad : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin ri) < registerCount)
           (A : Word)
           (ltA : proj1_sig (bitvector_fin A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((true :: true :: true :: true :: false :: [])  ++
       (true :: [])                                     ++
       ri                                               ++
       pad                                              ++
       padding
      ))) A =
    readI (regFit ri lti) (inl (regFit A ltA)).
  Proof.
    intros ri pad lti A ltA padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp ri lti), (regFitProp A ltA).
    reflexivity.
  Qed.
 
  Theorem read_decode_word_correct :
    forall (ri pad : Vector.t bool (clog2 registerCount))
           (lti : proj1_sig (bitvector_fin ri) < registerCount)
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((true :: true :: true :: true :: false :: []) ++
       (false :: [])                                ++
       ri                                           ++
       pad                                          ++
       padding
      ))) A =
    readI (regFit ri lti) (inr A).
  Proof.
    intros ri pad lti A padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp ri lti).
    reflexivity.
  Qed.

  Theorem answer_decode_register_correct :
    forall (pad1 pad2 : Vector.t bool (clog2 registerCount))
           (A : Word)
           (ltA : proj1_sig (bitvector_fin A) < registerCount)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((true :: true :: true :: true :: true :: [])  ++
       (true :: [])                                    ++
       pad1                                            ++
       pad2                                            ++
       padding
      ))) A =
    answerI (inl (regFit A ltA)).
  Proof.
    intros pad1 pad2 A ltA padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    rewrite (regFitProp A ltA).
    reflexivity.
  Qed.
 
  Theorem answer_decode_word_correct :
    forall (pad1 pad2 : Vector.t bool (clog2 registerCount))
           (A : Word)
           (padding : Vector.t bool paddingSize),
    OpcodeDecode (vector_length_coerce (eq_sym interpSplitLemRight) (
      ((true :: true :: true :: true :: true :: []) ++
       (false :: [])                                   ++
       pad1                                            ++
       pad2                                            ++
       padding
      ))) A =
    answerI (inr A).
  Proof.
    intros pad1 pad2 A padding.
    unfold OpcodeDecode; rewrite interpSplit_eval; simpl.
    reflexivity.
  Qed.

End TinyRAMDecodOps.


