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
Import EqNotations.

Module TinyRAMState (Params : TinyRAMParameters).
  Module TRWords := TinyRAMWords Params.
  Import TRWords.

  Theorem interpSplitLem : 
    wordSize =
      5 + 1 + (clog2 registerCount) + (clog2 registerCount) +
      (wordSize - 6 - 2 * clog2 registerCount).
    assert (6 + 2 * clog2 registerCount <= wordSize).
    { apply encodingAxiom. }
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
    Vector.t bool (wordSize - 6 - 2 * clog2 registerCount).
    intro w.
    unfold Word in w.
    rewrite interpSplitLem in w.
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
     power of 2.
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
    destruct x. { exact (OpcodeDecodeRiRjA orI isReg ri rj w2 w2reg). }
    destruct x. { exact (OpcodeDecodeRiRjA xorI isReg ri rj w2 w2reg). }
    destruct x. { exact (OpcodeDecodeRiA notI isReg ri w2 w2reg). }
    destruct x. { exact (OpcodeDecodeRiRjA addI isReg ri rj w2 w2reg). }
    destruct x. { exact (OpcodeDecodeRiRjA subI isReg ri rj w2 w2reg). }
    destruct x. { exact (OpcodeDecodeRiRjA mullI isReg ri rj w2 w2reg). }
    destruct x. { exact (OpcodeDecodeRiRjA umulhI isReg ri rj w2 w2reg). }
    destruct x. { exact (OpcodeDecodeRiRjA smulhI isReg ri rj w2 w2reg). }
    destruct x. { exact (OpcodeDecodeRiRjA udivI isReg ri rj w2 w2reg). }
    destruct x. { exact (OpcodeDecodeRiRjA umodI isReg ri rj w2 w2reg). }
    destruct x. { exact (OpcodeDecodeRiRjA shlI isReg ri rj w2 w2reg). }
    destruct x. { exact (OpcodeDecodeRiRjA shrI isReg ri rj w2 w2reg). }
    destruct x. { exact (OpcodeDecodeRiA cmpeI isReg ri w2 w2reg). }
    destruct x. { exact (OpcodeDecodeRiA cmpaI isReg ri w2 w2reg). }
    destruct x. { exact (OpcodeDecodeRiA cmpaeI isReg ri w2 w2reg). }
    destruct x. { exact (OpcodeDecodeRiA cmpgI isReg ri w2 w2reg). }
    destruct x. { exact (OpcodeDecodeRiA cmpgeI isReg ri w2 w2reg). }
    destruct x. { exact (OpcodeDecodeRiA movI isReg ri w2 w2reg). }
    destruct x. { exact (OpcodeDecodeRiA cmovI isReg ri w2 w2reg). }
    destruct x. { exact (OpcodeDecodeA jmpI isReg w2 w2reg). }
    destruct x. { exact (OpcodeDecodeA cjmpI isReg w2 w2reg). }
    destruct x. { exact (OpcodeDecodeA cnjmpI isReg w2 w2reg). }
    destruct x. { exact (OpcodeDecodeRiA store_bI isReg ri w2 w2reg). }
    destruct x. { exact (OpcodeDecodeRiA load_bI isReg ri w2 w2reg). }
    destruct x. { exact (OpcodeDecodeRiA store_wI isReg ri w2 w2reg). }
    destruct x. { exact (OpcodeDecodeRiA load_wI isReg ri w2 w2reg). }
    destruct x. { exact (OpcodeDecodeRiA readI isReg ri w2 w2reg). }
    destruct x. { exact (OpcodeDecodeA answerI isReg w2 w2reg). }
    (*"""
    If pc is not an integer in [...] the number of instructions in P,
    then the instruction answer 1 is fetched as default.)
    """*)
    exact answer1.
  Defined.




