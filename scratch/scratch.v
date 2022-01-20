(* In this file I try writing vnTinyRAM in coq *)
Set Warnings "-notation-overridden,-parsing".

From Coq Require Import Vector List Strings.String.
From ExtLib.Structures Require Import Monads MonadState.
Import ListNotations.
Local Open Scope string.

(*Fixing W = 8 and K = 8*)
Definition W : nat := 8.
Definition K : nat := 8.
(* Memory cells stack overflow when I try 16 lol *)

Inductive bit : Type := zero | one.

Definition word : Type := t bit 8.

Inductive reg : Type :=
| r0 (w : word) : reg
| r1 (w : word) : reg
| r2 (w : word) : reg
| r3 (w : word) : reg
| r4 (w : word) : reg
| r5 (w : word) : reg
| r6 (w : word) : reg
| r7 (w : word) : reg
.

Inductive state : Type :=
| pc (n : nat) : state
| r (r__k : reg) : state
| flag (n : bit) : state
.

Inductive instruction : Type :=
| ld (r : reg) (w : word) : instruction
| bitor (r : reg) (r : reg) : instruction
 (* etc. *)
.

Check ["load"; "1"; "0110"; "load"; "2"; "1001"; "bitor"; "1"; "2"].

Definition Memory : Type := t word (Nat.pow 2 8).

Inductive instruction : Type :=
| instr_and ()
