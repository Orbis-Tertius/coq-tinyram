From Coq Require Import
     Lia VectorDef VectorEq List ZArith ProofIrrelevance.
From TinyRAM.Utils Require Import
     Fin Vectors BitVectors.
From TinyRAM.Machine Require Import
     Parameters InstructionTheorems.
Import PeanoNat.Nat VectorNotations.

From ITree Require Import
     ITree
     ITreeFacts
     Events.State
     Events.StateFacts.

(* This file contains the implementation and formal verification of 
   a TinyRAM implementation of the Fibonacci function. *)

(* As a preamble, we first define an obviously correct implementation
   to be used as a specification. *)

Fixpoint fib (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n =>
    match n with
    | 0 => 1
    | S n' => fib n' + fib n
    end
  end.

(* Our implementation is going to use modular arithmetic since
   the output comes in the form of a fixed-length bitvector.

   We also generalize the base arguments to aid in reasoining about
   the main loop later.

   We relate fib to its moded version.
*)

Fixpoint mfib (i j m n : nat) : nat :=
  match n with
  | 0 => i
  | S n =>
    match n with
    | 0 => j
    | S n' => (mfib i j m n' + mfib i j m n) mod m
    end
  end.

Theorem mfib_mod : forall m n, 1 < m ->
  mfib 0 1 m n = fib n mod m.
Proof.
  intros m n lt.
  assert ( (mfib 0 1 m n, mfib 0 1 m (S n))
         = (fib n mod m, fib (S n) mod m) ).
  { induction n.
    - simpl.
      rewrite mod_0_l, mod_small; try lia; reflexivity.
    - change (mfib 0 1 m (S (S n))) 
        with ((mfib 0 1 m n + mfib 0 1 m (S n)) mod m).
      change (fib (S (S n))) 
        with (fib n + fib (S n)).
      f_equal.
      + injection IHn; auto.
      + rewrite (add_mod (fib n)); [|lia].
        injection IHn; auto. }
  rewrite pair_equal_spec in H; destruct H.
  assumption.
Qed.

Theorem mfib_upper_bound: forall i j m n, 
  i < m -> j < m -> m <> 0 ->
  mfib i j m n < m.
Proof.
  intros i j m n.
  destruct n.
  - unfold mfib; auto.
  - destruct n; unfold mfib; fold mfib.
    + auto.
    + intros; apply mod_upper_bound; auto.
Qed.

Theorem mfib_rebase: forall i j m n, 
  mfib i j m (S n) = mfib (mfib i j m 1) (mfib i j m 2) m n.
Proof.
  intros i j m n.
  assert ( (mfib i j m (S n), mfib i j m (S (S n)))
         = (mfib (mfib i j m 1) (mfib i j m 2) m n
           ,mfib (mfib i j m 1) (mfib i j m 2) m (S n))).
  { induction n.
    - reflexivity.
    - change (mfib i j m (S (S (S n))))
        with ((mfib i j m (S n) + mfib i j m (S (S n))) mod m).
      rewrite pair_equal_spec in IHn; destruct IHn.
      rewrite H, H0; clear H H0.
      reflexivity. }
  rewrite pair_equal_spec in H; destruct H.
  assumption.
Qed.

(* Example archetecture with 4 registers and a wordsize of 16 bits. *)
Module SixteenFour <: TinyRAMParameters.
  Definition wordSizeEighth : nat := 2.
  Definition registerCount : nat := 4.
  Definition wordSize := wordSizeEighth * 8.
  Definition wordSizeLength : nat := 4.
  Theorem wordSizePow2 : wordSize = 2 ^ wordSizeLength.
  Proof. unfold wordSize. simpl. reflexivity. Qed.
  Theorem encodingAxiom : 6 + 2 * log2_up registerCount <= wordSize.
  Proof. unfold registerCount. unfold wordSize. simpl. lia. Qed.
End SixteenFour.

Module TR := TinyRAMInstThm SixteenFour.
Import TR.

(* We can create the actual assembly program now. 
   
   The program begins by doing the folloing;
     the input, n, is read from the main tape into register 00.
     the address blocks starting at 0 and 2 are set to 0 and 1.

   Over the course of the program, fib n will be stored at block
   0 and fib (S n) will be stored at block 2.

   During each loop, block 0 is set to the value of block 2 and
   block 2 is set to the value of block 0 plus block 2.

   during this procedure, the value of block 0 (e.g. fib n) will
   be stored in register 10 while block 2 (e.g. fib (S n)) will
   be stored in register 01.

   Each loop begins by seeing if [00] is 0.
   If it is, halt and give [10] as output.
   If it is not, then continue through the loop.
   At the end of the loop [00] is decremented before the PC is
   reset to the begining of the loop.
*)

(*The actual assembly program.*)
Definition FibProgram : Program.
  apply (List.map InstructionEncode).

  (* This works by manipulating the values at addresses 0 and 2 *)
  (* n is sored in register 00, and is decremented every loop until 0 *)

  (* Initialization *)
  (* Store 1 into address 0010 *)
    (*0: Store 1 into register 00 *)
  apply (cons (movI (bitvector_fin_big [b0; b0]), inl (nat_bitvector_big _ 1))).
    (*1: Store [00] at address 2 *)
  apply (cons (store_wI (bitvector_fin_big [b0; b0]), inl (nat_bitvector_big _ wordSizeEighth))).

  (*2: Read input from main tape into register 00. *)
  apply (cons (readI (bitvector_fin_big [b0; b0]), inl (nat_bitvector_big _ 0))).

  (* Main Loop *)
  (*3: Check if 00 is 0*)
  apply (cons (cmpeI (bitvector_fin_big [b0; b0]), inl (nat_bitvector_big _ 0))).

  (*4: If flag is set, jump.*)
  apply (cons (cjmpI, inl (nat_bitvector_big _ 12))).

  (* Read two addresses into registers *)
  (*5: read address 0 into 01 *)
  apply (cons (load_wI (bitvector_fin_big [b0; b1]), inl (nat_bitvector_big _ 0))).
  (*6: read address 2 into 10  *)
  apply (cons (load_wI (bitvector_fin_big [b1; b0]), inl (nat_bitvector_big _ wordSizeEighth))).

  (*7: add two registers together; [01] := [01] + [10] *)
  apply (cons (addI (bitvector_fin_big [b0; b1]) (bitvector_fin_big [b0; b1]),
                    (inr (bitvector_fin_big [b1; b0])))).

  (* Store both registers *)
  (*8: store [10] into adress 0 *)
  apply (cons (store_wI (bitvector_fin_big [b1; b0]), inl (nat_bitvector_big _ 0))).
  (*9: store [01] into adress 2 *)
  apply (cons (store_wI (bitvector_fin_big [b0; b1]), inl (nat_bitvector_big _ wordSizeEighth))).

  (*10: decriment [00] *)
  apply (cons (subI (bitvector_fin_big [b0; b0]) (bitvector_fin_big [b0; b0]),
                    (inl (nat_bitvector_big _ 1)))).

  (*11: jump back to 0 check. *)
  apply (cons (jmpI, inl (nat_bitvector_big _ 3))).

  (*12: Return *)
  apply (cons (answerI, inr (bitvector_fin_big [b1; b0]))).

  apply nil.
Defined.

(* The program proper is the following. *)
Definition fib_asm (n : nat) : itree void1 Word :=
  interp_program FibProgram (nat_bitvector_big _ n :: nil)%list nil.

(* However, reasoning about this directly is not practical. Instead,
   we divierge a bit to describe some functions which perform the
   same state manipulations. This will factor out the itrees giving
   making things simpler.
*)

(*Firstly, we want to describe the sequence of pure state manipulations.*)
(*initialize 1 into address 2 and read tape into reg 0.*)
Definition fib_init (m : MachineState) : MachineState :=
  (pureOp_read (bitvector_fin_big [b0; b0]) (nat_bitvector_big _ 0) 
  (pureOp_store_w (bitvector_fin_big [b0; b0]) (nat_bitvector_big _ 2) 
  (pureOp_mov (bitvector_fin_big [b0; b0]) (nat_bitvector_big _ 1)
  m))).

(*The recursive step of the fib function*)
Definition fib_step (m : MachineState) : MachineState :=
  let m0 := 
      (pureOp_load_w (bitvector_fin_big [b1; b0]) (nat_bitvector_big _ 2)
      (pureOp_load_w (bitvector_fin_big [b0; b1]) (nat_bitvector_big _ 0)
      (pureOp_cjmp (nat_bitvector_big _ 12)
      (pureOp_cmpe (bitvector_fin_big [b0; b0]) (nat_bitvector_big _ 0)
      m)))) in
    (pureOp_jmp (nat_bitvector_big _ 3)
    (pureOp_sub (bitvector_fin_big [b0; b0]) (bitvector_fin_big [b0; b0])
                (nat_bitvector_big _ 1)
    (pureOp_store_w (bitvector_fin_big [b0; b1]) (nat_bitvector_big _ 2) 
    (pureOp_store_w (bitvector_fin_big [b1; b0]) (nat_bitvector_big _ 0) 
    (pureOp_add (bitvector_fin_big [b0; b1]) (bitvector_fin_big [b0; b1])
                (nth (registers m0) (bitvector_fin_big [b1; b0]))
    m0))))).

(*The loop as a terminating program*)
Fixpoint fib_step_r (n : nat) (m : MachineState) : MachineState :=
  match n with
  | 0 => m
  | S n => fib_step_r n (fib_step m)
  end.

(*The final step before halting.*)
Definition fib_finish (m : MachineState) : MachineState :=
  (pureOp_cjmp (nat_bitvector_big _ 12)
  (pureOp_cmpe (bitvector_fin_big [b0; b0]) (nat_bitvector_big _ 0)
  m)).

(*The full program. *)
Definition fib_full (m : MachineState) : MachineState :=
  let m0 := fib_init m in
  let m1 := fib_step_r (bitvector_nat_big (nth (registers m0) (bitvector_fin_big [b0; b0]))) m0 in
  fib_finish m1.

(* We can verify that these functions do, in fact, do the same thing 
   as out program by showing the state manipulations generated by
   run are the same as that generated by fib_full. *)

(* Note: the strategies used here are essentially automatic. They 
   can definitely be turned into tactics, but that's for the future. *)

(* Before getting into that, here are a few theorems which may be 
   useful. *)
Lemma program_fib_init : 
  forall m, (program (fib_init m)) = program m.
Proof. destruct m; reflexivity. Qed.

Lemma program_fib_step : 
  forall m, (program (fib_step m)) = program m.
Proof. destruct m; reflexivity. Qed.

Lemma program_fib_step_r : 
  forall n m, (program (fib_step_r n m)) = program m.
Proof. 
  induction n; destruct m; [ reflexivity | ].
  unfold fib_step_r; fold fib_step_r.
  rewrite IHn, program_fib_step.
  reflexivity.
Qed.

Lemma program_fib_finish : 
  forall m, (program (fib_finish m)) = program m.
Proof. destruct m; reflexivity. Qed.

Lemma program_fib_full : 
  forall m, (program (fib_full m)) = program m.
Proof. 
  intro.
  unfold fib_full. 
  rewrite program_fib_finish, program_fib_step_r, program_fib_init.
  reflexivity.
Qed.

Lemma programCounter_fib_init : 
  forall m, 
  (programCounter m) = (nat_bitvector_big _ 0) ->
  (programCounter (fib_init m)) = 
  (nat_bitvector_big _ 3).
Proof.
  destruct m; intro H; unfold programCounter in H; rewrite H.
  unfold fib_init, pureOp_mov, pureOp_store_w, pureOp_read, programCounter.
  assert (255 < 2 ^ wordSize);[apply address_min|].
  pc_simpl; reflexivity.
Qed.

Lemma programCounter_fib_step : 
  forall m, (programCounter (fib_step m)) = 
  (nat_bitvector_big _ 3).
Proof. destruct m; reflexivity. Qed.

Lemma fib_step_r_unfold_out : forall n m,
  fib_step_r (S n) m = fib_step (fib_step_r n m).
Proof. 
  induction n;[destruct m;reflexivity|intro].
  unfold fib_step_r at 2; fold fib_step_r.
  change (fib_step_r (S (S n)) m)
     with (fib_step_r (S n) (fib_step m)).
  rewrite IHn.
  reflexivity.
Qed.

Lemma programCounter_fib_step_r : 
  forall m n, (programCounter (fib_step_r (S n) m)) = 
  (nat_bitvector_big _ 3).
Proof.
  intros.
  rewrite fib_step_r_unfold_out, programCounter_fib_step.
  reflexivity.
Qed.

Lemma programCounter_fib_finish : forall m,
  nth (registers m) (bitvector_fin_big [b0; b0])
  = (nat_bitvector_big wordSize 0) ->
  (programCounter (fib_finish m)) = 
  (nat_bitvector_big _ 12).
Proof.
  intros m H.
  destruct m.
  unfold fib_finish, pureOp_cmpe, pureOp_cjmp.
  unfold registers in H; rewrite H.
  reflexivity.
Qed.

(* fib_step decrements register 00 *)
Lemma fib_step_index_dec : forall m,
  nth (registers (fib_step m)) (bitvector_fin_big [b0; b0])
  = VectorDef.tl (bv_sub (nth (registers m) (bitvector_fin_big [b0; b0]))
                      (nat_bitvector_big _ 1)).
Proof.
  destruct m.
  unfold fib_step.
  unfold registers.
  unfold pureOp_cmpe, pureOp_cjmp, pureOp_load_w.
  unfold pureOp_add, pureOp_store_w, pureOp_sub, pureOp_jmp.
  repeat (rewrite replace_swap; [ | simpl; lia ];
          rewrite replace_nth_irr; [ | simpl; lia ]).
  rewrite nth_replace.
  reflexivity.
Qed.

(*fib_step_r will always make register 00 0. 
  (precondition for assembly always halting)*)
Lemma fib_step_r_halt_lem : 
  forall n m,
  n < 2 ^ wordSize ->
  nth (registers m) (bitvector_fin_big [b0; b0]) = (nat_bitvector_big _ n) ->
  nth (registers (fib_step_r n m)) (bitvector_fin_big [b0; b0]) 
  = (nat_bitvector_big _ 0).
Proof.
  induction n; destruct m; intros lt Eq; unfold registers in Eq.
  - unfold fib_step_r, fib_finish, pureOp_cmpe, pureOp_cjmp, programCounter.
    assumption.
  - unfold fib_step_r; fold fib_step_r.
    assert (n < 2 ^ wordSize); [lia|].
    rewrite (IHn _ H); [ reflexivity | ].
    rewrite fib_step_index_dec.
    unfold registers.
    rewrite Eq.
    rewrite bv_sub_correct_pos; try lia.
    f_equal; lia.
Qed.

(* The assembly produced by FibProgram starts with fib_init *)
Lemma fib_runs_init : forall n, 
  (interp_machine (E := void1) run
     (initialState FibProgram
        (nat_bitvector_big wordSize n :: nil)%list nil))
  ≈ (interp_machine (E := void1) run
      (fib_init (initialState FibProgram
        (nat_bitvector_big wordSize n :: nil)%list nil))).
Proof.
  assert (255 < 2 ^ wordSize);[apply address_min|].
  intro n.
  unfold initialState.
  change (const b0 wordSize) with (nat_bitvector_big wordSize 0).
  rewrite interp_machine_run_step;
  [|unfold programCounter; rewrite nat_bitvector_big_inv;[reflexivity|lia]
   |apply encode_decode_id|intro HAH; discriminate HAH].
  rewrite pureOp_mov_interp_imm; unfold pureOp_mov.
  pc_simpl; rewrite interp_machine_run_step;
  [|unfold programCounter; rewrite nat_bitvector_big_inv;[reflexivity|lia]
   |apply encode_decode_id|intro HAH; discriminate HAH].
  rewrite pureOp_store_w_interp_imm; unfold pureOp_store_w.
  pc_simpl; rewrite interp_machine_run_step;
  [|unfold programCounter; rewrite nat_bitvector_big_inv;[reflexivity|lia]
   |apply encode_decode_id|intro HAH; discriminate HAH].
  rewrite pureOp_read_interp_imm.
  unfold pureOp_read.
  unfold fib_init, pureOp_mov, pureOp_store_w, pureOp_read, programCounter.
  pc_simpl; reflexivity.
Qed.

(* After initialization, the assembly produced by FibProgram's main
   loop corresponds to fib_step *)
Lemma fib_runs_step : forall n m,
  S n < 2 ^ wordSize ->
  programCounter m = nat_bitvector_big _ 3 ->
  nth (registers m) (bitvector_fin_big [b0; b0]) = nat_bitvector_big _ (S n) ->
  program m = FibProgram ->
  interp_machine (E := void1) run m
  ≈ interp_machine (E := void1) run (fib_step m).
Proof.
  assert (255 < 2 ^ wordSize);[apply address_min|].
  intros n m lt eq1 eq2 eq3; destruct m.
  unfold registers in eq2.
  unfold programCounter in eq1; rewrite eq1.
  unfold program in eq3; rewrite eq3.
  unfold fib_step.
  rewrite interp_machine_run_step;
  [|change (bitvector_nat_big _) with 3;reflexivity|apply encode_decode_id|intro HAH; discriminate HAH].
  rewrite pureOp_cmpe_interp_imm; unfold pureOp_cmpe.
  replace (bv_eq _ _) with b0; [|
  rewrite eq2, bv_eq_big_conv; [reflexivity|assumption|apply Arith.zero2pow]].
  pc_simpl; rewrite interp_machine_run_step;
  [|unfold programCounter; rewrite nat_bitvector_big_inv;[reflexivity|lia]
   |apply encode_decode_id|intro HAH; discriminate HAH].
  rewrite pureOp_cjmp_interp_imm; unfold pureOp_cjmp.
  change (if b0 then _ else ?y) with y.
  pc_simpl; rewrite interp_machine_run_step;
  [|unfold programCounter; rewrite nat_bitvector_big_inv;[reflexivity|lia]
   |apply encode_decode_id|intro HAH; discriminate HAH].
  rewrite pureOp_load_w_interp_imm; unfold pureOp_load_w.
  unfold registers.
  pc_simpl; rewrite interp_machine_run_step;
  [|unfold programCounter; rewrite nat_bitvector_big_inv;[reflexivity|lia]
   |apply encode_decode_id|intro HAH; discriminate HAH].
  rewrite pureOp_load_w_interp_imm; unfold pureOp_load_w.
  pc_simpl; rewrite interp_machine_run_step;
  [|unfold programCounter; rewrite nat_bitvector_big_inv;[reflexivity|lia]
   |apply encode_decode_id|intro HAH; discriminate HAH].
  rewrite pureOp_add_interp_reg; unfold pureOp_add.
  unfold registers.
  pc_simpl; rewrite interp_machine_run_step;
  [|unfold programCounter; rewrite nat_bitvector_big_inv;[reflexivity|lia]
   |apply encode_decode_id|intro HAH; discriminate HAH].
  rewrite pureOp_store_w_interp_imm; unfold pureOp_store_w.
  pc_simpl; rewrite interp_machine_run_step;
  [|unfold programCounter; rewrite nat_bitvector_big_inv;[reflexivity|lia]
   |apply encode_decode_id|intro HAH; discriminate HAH].
  rewrite pureOp_store_w_interp_imm; unfold pureOp_store_w.
  pc_simpl; rewrite interp_machine_run_step;
  [|unfold programCounter; rewrite nat_bitvector_big_inv;[reflexivity|lia]
   |apply encode_decode_id|intro HAH; discriminate HAH].
  rewrite pureOp_sub_interp_imm; unfold pureOp_sub.
  pc_simpl; rewrite interp_machine_run_step;
  [|unfold programCounter; rewrite nat_bitvector_big_inv;[reflexivity|lia]
   |apply encode_decode_id|intro HAH; discriminate HAH].
  rewrite pureOp_jmp_interp_imm; unfold pureOp_jmp.
  pc_simpl;reflexivity.
Qed.

(*After initialization, the loop generated by FibProgram is the same
  as that specified by fib_step_r. *)
Lemma fib_runs_step_r : forall n m,
  n < 2 ^ wordSize ->
  programCounter m = nat_bitvector_big _ 3 ->
  nth (registers m) (bitvector_fin_big [b0; b0]) = nat_bitvector_big _ n ->
  program m = FibProgram ->
  interp_machine (E := void1) run m
  ≈ interp_machine (E := void1) run (fib_step_r n m).
Proof.
  induction n; destruct m; intros;
  unfold programCounter in H0;
  unfold registers in H1;
  unfold program in H2;
  rewrite H0, H2;
  unfold fib_step_r;[reflexivity|].
  fold fib_step_r.
  rewrite fib_runs_step; [|exact H|reflexivity|exact H1|reflexivity].
  rewrite IHn; try reflexivity; [lia|].
  rewrite fib_step_index_dec; unfold registers.
  rewrite H1.
  rewrite bv_sub_correct_pos;[f_equal;lia|assumption|
  exact pureOp_read_correct_lem|lia].
Qed.

(*The ending of FibProgram is the same as fib_finish. *)
Lemma fib_runs_finish : forall m,
  programCounter m = nat_bitvector_big _ 3 ->
  nth (registers m) (bitvector_fin_big [b0; b0]) = nat_bitvector_big _ 0 ->
  program m = FibProgram ->
  interp_machine (E := void1) run m
  ≈ interp_machine (E := void1) run (fib_finish m).
Proof.
  assert (255 < 2 ^ wordSize) as HLT;[apply address_min|].
  destruct m; unfold programCounter, registers, program; intros.
  unfold fib_finish.
  rewrite H, H1; clear H H1.
  pc_simpl; rewrite interp_machine_run_step;
  [|unfold programCounter; rewrite nat_bitvector_big_inv;[reflexivity|lia]
   |apply encode_decode_id|intro HAH; discriminate HAH].
  rewrite pureOp_cmpe_interp_imm; unfold pureOp_cmpe.
  rewrite H0; change (bv_eq _ _) with b1.
  pc_simpl; rewrite interp_machine_run_step;
  [|unfold programCounter; rewrite nat_bitvector_big_inv;[reflexivity|lia]
   |apply encode_decode_id|intro HAH; discriminate HAH].
  rewrite pureOp_cjmp_interp_imm.
  reflexivity.
Qed.

(* The state manipulations produced by FibProgram is the same as that
   produced by fib_full. *)
Lemma fib_runs_full : forall n, 
  n < 2 ^ wordSize ->
  (interp_machine (E := void1) run (initialState FibProgram
        (nat_bitvector_big wordSize n :: nil)%list nil))
  ≈ (interp_machine (E := void1) run (fib_full (initialState FibProgram
        (nat_bitvector_big wordSize n :: nil)%list nil))).
Proof.
  assert (255 < 2 ^ wordSize) as HLT;[apply address_min|].
  intros n lt.
  rewrite fib_runs_init, fib_runs_step_r, fib_runs_finish;
  unfold fib_full;
  unfold initialState, fib_init, pureOp_mov, pureOp_store_w, pureOp_read.
  - reflexivity.
  - unfold registers.
    rewrite nat_bitvector_big_inv;[|apply Arith.zero2pow ].
    rewrite nth_replace.
    rewrite nat_bitvector_big_inv;[|assumption].
    change (const b0 wordSize) with (nat_bitvector_big wordSize 0).
    destruct n;[pc_simpl;reflexivity|].
    apply programCounter_fib_step_r.
  - unfold registers at 2.
    rewrite nat_bitvector_big_inv;[|apply Arith.zero2pow ].
    rewrite nth_replace.
    rewrite nat_bitvector_big_inv;[|assumption].
    apply fib_step_r_halt_lem;[assumption|].
    unfold registers.
    apply nth_replace.
  - rewrite program_fib_step_r; reflexivity.
  - unfold registers.
    rewrite nth_replace.
    rewrite nat_bitvector_big_inv;[|apply Arith.zero2pow ].
    rewrite nat_bitvector_big_inv;assumption.
  - unfold programCounter. 
    change (const b0 wordSize) with (nat_bitvector_big wordSize 0).
    pc_simpl; reflexivity.
  - unfold registers.
    rewrite nth_replace. 
    rewrite nat_bitvector_big_inv;[|apply Arith.zero2pow ].
    rewrite nat_bitvector_big_inv;[reflexivity|assumption ].
  - reflexivity.
Qed.

(* That connects fib_full to our assembly, but we also need to 
   verify that fib_full runs the fibonacci function. *)

(*fib_step computes subsequent fib values.*)
Lemma fib_step_vals_1 : forall i j m n,
  Memory_Word_Load_from_Reg (memory m) (nat_bitvector_big _ 2)
    = nat_bitvector_big _ (mfib i j (2 ^ wordSize) (S n)) -> 
  Memory_Word_Load_from_Reg (memory (fib_step m)) (nat_bitvector_big _ 0)
    = nat_bitvector_big _ (mfib i j (2 ^ wordSize) (S n)).
Proof.
  assert (255 < 2 ^ wordSize) as HLT;[apply address_min|].
  intros i j m n.
  destruct m; unfold memory.
  intros.
  unfold fib_step.
  unfold pureOp_cmpe, pureOp_cjmp, pureOp_load_w.
  unfold pureOp_add, pureOp_store_w, pureOp_sub, pureOp_jmp.
  unfold registers.
  rewrite H; clear H.
  repeat rewrite (replace_swap _ (bitvector_fin_big [b0; b1]) (bitvector_fin_big [b1; b0])).
  repeat rewrite (replace_nth_irr _ (bitvector_fin_big [b0; b1]) (bitvector_fin_big [b1; b0])).
  repeat rewrite (replace_swap _ (bitvector_fin_big [b1; b0]) (bitvector_fin_big [b0; b1])).
  repeat rewrite (replace_nth_irr _ (bitvector_fin_big [b1; b0]) (bitvector_fin_big [b0; b1])).
  repeat rewrite replace_replace.
  repeat rewrite nth_replace.
  rewrite Memory_Word_Store_Load_from_Reg_Irr.
  rewrite Memory_Word_Store_Load_from_Reg.
  reflexivity.
  repeat rewrite nat_bitvector_big_inv; change wordSizeEighth with 2; lia.
  all: simpl; lia.
Qed.

(*fib_step computes subsequent fib values.*)
Lemma fib_step_vals_2 : forall i j m n,
  i < 2 ^ wordSize -> j < 2 ^ wordSize ->
  Memory_Word_Load_from_Reg (memory m) (nat_bitvector_big _ 0)
    = nat_bitvector_big _ (mfib i j (2 ^ wordSize) n) -> 
  Memory_Word_Load_from_Reg (memory m) (nat_bitvector_big _ 2)
    = nat_bitvector_big _ (mfib i j (2 ^ wordSize) (S n)) -> 
  Memory_Word_Load_from_Reg (memory (fib_step m)) (nat_bitvector_big _ 2)
    = nat_bitvector_big _ (mfib i j (2 ^ wordSize) (S (S n))).
Proof.
  assert (255 < 2 ^ wordSize) as HLT;[apply address_min|].
  intros i j m n iLT jLT.
  destruct m; unfold memory.
  intros.
  unfold fib_step.
  unfold pureOp_cmpe, pureOp_cjmp, pureOp_load_w.
  unfold pureOp_add, pureOp_store_w, pureOp_sub, pureOp_jmp.
  unfold registers.
  rewrite H, H0; clear H H0.
  repeat rewrite (replace_swap _ (bitvector_fin_big [b0; b1]) (bitvector_fin_big [b1; b0])).
  repeat rewrite (replace_nth_irr _ (bitvector_fin_big [b0; b1]) (bitvector_fin_big [b1; b0])).
  repeat rewrite (replace_swap _ (bitvector_fin_big [b1; b0]) (bitvector_fin_big [b0; b1])).
  repeat rewrite (replace_nth_irr _ (bitvector_fin_big [b1; b0]) (bitvector_fin_big [b0; b1])).
  repeat rewrite nth_replace.
  rewrite Memory_Word_Store_Store_from_Reg_Swap.
  rewrite Memory_Word_Store_Load_from_Reg_Irr.
  rewrite Memory_Word_Store_Load_from_Reg.
  rewrite <- bv_add_correct_mod_2.
  reflexivity.
  apply mfib_upper_bound;[assumption|assumption|apply pow_nonzero;lia].
  apply mfib_upper_bound;[assumption|assumption|apply pow_nonzero;lia].
  repeat rewrite nat_bitvector_big_inv; change wordSizeEighth with 2; lia.
  repeat rewrite nat_bitvector_big_inv; change wordSizeEighth with 2; lia.
  all: simpl; lia.
Qed.

Lemma fib_step_r_vals : forall n m,
  n < 2 ^ wordSize ->
  nth (registers m) (bitvector_fin_big [b0;b0]) 
    = (nat_bitvector_big _ n) ->
  Memory_Word_Load_from_Reg (memory (fib_step_r n m)) (nat_bitvector_big _ 0)
  = nat_bitvector_big _ 
      (mfib (bitvector_nat_big (Memory_Word_Load_from_Reg (memory m) (nat_bitvector_big _ 0)))
            (bitvector_nat_big (Memory_Word_Load_from_Reg (memory m) (nat_bitvector_big _ 2)))
            (2 ^ wordSize) n).
Proof.
  induction n; intros; destruct m; unfold registers in H0.
  - unfold fib_step_r.
    unfold memory.
    unfold mfib.
    repeat rewrite bitvector_nat_big_inv.
    reflexivity.
  - unfold fib_step_r; fold fib_step_r.
    rewrite IHn; clear IHn.
    + repeat unfold memory at 3.
      rewrite mfib_rebase.
      f_equal; f_equal.
      --  rewrite (fib_step_vals_1 (bitvector_nat_big
                    (Memory_Word_Load_from_Reg memory0
                        (nat_bitvector_big wordSize 0))) (bitvector_nat_big
                    (Memory_Word_Load_from_Reg memory0
                        (nat_bitvector_big wordSize 2))) _ 0).
          rewrite nat_bitvector_big_inv;[reflexivity|].
          apply mfib_upper_bound.
          all: try apply bitvector_nat_big_lt_2pow.
          apply pow_nonzero; lia.
          unfold memory.
          unfold mfib.
          rewrite bitvector_nat_big_inv; reflexivity.
      --  rewrite (fib_step_vals_2 (bitvector_nat_big
                    (Memory_Word_Load_from_Reg memory0
                        (nat_bitvector_big wordSize 0))) (bitvector_nat_big
                    (Memory_Word_Load_from_Reg memory0
                        (nat_bitvector_big wordSize 2))) _ 0).
          rewrite nat_bitvector_big_inv;[reflexivity|].
          apply mfib_upper_bound.
          all: try apply bitvector_nat_big_lt_2pow.
          apply pow_nonzero; lia.
          all: unfold memory, mfib; rewrite bitvector_nat_big_inv; reflexivity.
    + lia.
    + rewrite fib_step_index_dec.
      unfold registers; rewrite H0.
      rewrite bv_sub_correct_pos.
      f_equal.
      all: lia.
Qed.

(* register 00 has the same value as address 0 after each step. *)
Lemma fib_step_copy: forall m,
  nth (registers (fib_step m)) (bitvector_fin_big [b1; b0])
  = Memory_Word_Load_from_Reg (memory (fib_step m)) (nat_bitvector_big _ 0).
Proof.
  assert (255 < 2 ^ wordSize) as HLT;[apply address_min|].
  destruct m.
  unfold fib_step.
  unfold pureOp_cmpe, pureOp_cjmp, pureOp_load_w.
  repeat unfold registers at 2.
  unfold pureOp_add, pureOp_store_w, pureOp_sub, pureOp_jmp.
  unfold registers, memory.
  repeat rewrite (replace_swap _ (bitvector_fin_big [b1; b0]) (bitvector_fin_big [b0; b1])).
  repeat rewrite nth_replace.
  repeat rewrite replace_replace.
  repeat rewrite (replace_swap _ (bitvector_fin_big [b0; b1]) (bitvector_fin_big [b1; b0])).
  repeat rewrite nth_replace.
  rewrite (replace_nth_irr _ _ (bitvector_fin_big [b1; b0])).
  rewrite (replace_nth_irr _ _ (bitvector_fin_big [b1; b0])).
  rewrite nth_replace.
  rewrite Memory_Word_Store_Load_from_Reg_Irr. 
  rewrite Memory_Word_Store_Load_from_Reg; reflexivity.
  repeat rewrite nat_bitvector_big_inv;change wordSizeEighth with 2;lia.
  all: simpl; lia.
Qed.

(* register 00 has the same value as address 0 after each step_r. *)
Lemma fib_step_r_copy: forall n m,
  nth (registers (fib_step_r m (fib_init (initialState FibProgram
        (nat_bitvector_big wordSize n :: nil)%list nil)))) (bitvector_fin_big [b1; b0])
  = Memory_Word_Load_from_Reg (memory (fib_step_r m (fib_init (initialState FibProgram
        (nat_bitvector_big wordSize n :: nil)%list nil)))) (nat_bitvector_big _ 0).
Proof.
  assert (255 < 2 ^ wordSize) as HLT;[apply address_min|].
  intro n.
  destruct m.
  - unfold fib_step_r.
    unfold initialState, fib_init, pureOp_mov, pureOp_store_w, pureOp_read, registers.
    unfold memory.
    rewrite nat_bitvector_big_inv;[|apply Arith.zero2pow].
    rewrite nth_replace.
    repeat rewrite replace_nth_irr.
    rewrite Memory_Word_Store_Load_from_Reg_Irr.
    rewrite Memory_Word_Load_from_Reg_const.
    reflexivity.
    repeat rewrite nat_bitvector_big_inv;change wordSizeEighth with 2;lia.
    all: simpl; lia.
  - rewrite fib_step_r_unfold_out.
    apply fib_step_copy.
Qed.

(* After running fib_full instructions, reg 10 contains the appropriate value *)
Lemma fib_full_vals : forall n, 
  n < 2 ^ wordSize ->
  nth (registers (fib_full (initialState FibProgram
        (nat_bitvector_big wordSize n :: nil)%list nil)))
      (bitvector_fin_big [b1; b0])
  = nat_bitvector_big _ (fib n mod (2 ^ wordSize)).
Proof.
  assert (255 < 2 ^ wordSize) as HLT;[apply address_min|].
  intros n nLT.
  unfold fib_full, fib_finish.
  rewrite registers_pureOp_cjmp, registers_pureOp_cmpe.
  rewrite <- mfib_mod;[|exact pureOp_read_correct_lem].
  rewrite fib_step_r_copy.
  rewrite fib_step_r_vals.
  unfold initialState, fib_init, pureOp_mov, pureOp_store_w, pureOp_read, registers.
  unfold memory.
  repeat rewrite nth_replace.
  rewrite Memory_Word_Store_Load_from_Reg_Irr.
  rewrite Memory_Word_Load_from_Reg_const.
  rewrite Memory_Word_Store_Load_from_Reg.
  rewrite nat_bitvector_big_inv;[|exact pureOp_read_correct_lem].
  rewrite nat_bitvector_big_inv;[|apply Arith.zero2pow].
  rewrite nat_bitvector_big_inv;[|assumption].
  reflexivity.
  repeat rewrite nat_bitvector_big_inv;change wordSizeEighth with 2;lia.
  apply bitvector_nat_big_lt_2pow.
  rewrite bitvector_nat_big_inv; reflexivity.
Qed.

(* We can compose our previous lines of proof together now. *)

(* After running fib_full, the PC is at an answer instruction. *)
Lemma fib_full_answer : forall n, n < 2 ^ wordSize ->
  (List.nth_error (program (fib_full (initialState FibProgram
                                     (nat_bitvector_big wordSize n :: nil)%list nil)))
                  (bitvector_nat_big (programCounter (fib_full (initialState FibProgram
                                     (nat_bitvector_big wordSize n :: nil)%list nil)))))
  = Some (InstructionEncode (answerI, inr (bitvector_fin_big [b1; b0]))).
Proof.
  assert (255 < 2 ^ wordSize) as HLT;[apply address_min|].
  intros n nlt.
  remember (fib_full _) as intr.
  unfold initialState, fib_full, fib_init, pureOp_mov, pureOp_store_w, pureOp_read, registers in Heqintr.
  rewrite nat_bitvector_big_inv, nth_replace, nat_bitvector_big_inv in Heqintr;
  [ | assumption | apply Arith.zero2pow ].
  rewrite nth_replace, replace_replace in Heqintr.
  rewrite Heqintr; clear Heqintr intr.
  change (const b0 wordSize) with (nat_bitvector_big wordSize 0).
  pc_simpl.
  rewrite program_fib_finish, program_fib_step_r.
  unfold program.
  rewrite programCounter_fib_finish;[reflexivity|].
  rewrite fib_step_r_halt_lem;[reflexivity|assumption|].
  unfold registers.
  rewrite nth_replace.
  reflexivity.
Qed.

(*the state is correctly calculated by fib_full and the value
  is correctly calculated by (fib n mod (2 ^ wordSize) *)
Lemma fib_ret_state_val : forall n, 
  n < 2 ^ wordSize ->
  (interp_machine (E := void1) run
     (initialState FibProgram
        (nat_bitvector_big wordSize n :: nil)%list nil))
  ≈ Ret (fib_full (initialState FibProgram
                   (nat_bitvector_big wordSize n :: nil)%list nil),
         nat_bitvector_big _ (fib n mod (2 ^ wordSize))).
Proof.
  intros n lt. rewrite fib_runs_full;[|assumption].
  rewrite interp_machine_run_halt_reg;
  [ rewrite fib_full_vals;[reflexivity|assumption]
  | rewrite fib_full_answer;[reflexivity|assumption]
  | apply encode_decode_id ].
Qed.

(*And, finally, we have our main theorem, that our assembly
  program correctly calculates the fibonacci numbers within
  the bounds of mod 2 ^ wordSize. *)
Theorem fib_correct : forall n,
  n < 2 ^ wordSize ->
  fib_asm n ≈ Ret (nat_bitvector_big _ (fib n mod (2 ^ wordSize))).
Proof.
  intros n lt.
  unfold fib_asm, interp_program.
  rewrite fib_ret_state_val;[|assumption].
  unfold ITree.map.
  rewrite bind_ret_l.
  reflexivity.
Qed.
