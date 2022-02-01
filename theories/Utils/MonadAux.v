From Coq Require Import
     List.
From ExtLib Require Import
     Monad.
Import MonadNotation.
Import ListNotations.

Definition traverse_ {A: Type} {M: Type -> Type} `{Monad M} (f: A -> M unit): list A -> M unit :=
  fix traverse__ l: M unit :=
    match l with
    | nil => ret tt
    | a::l => (f a;; traverse__ l)%monad
    end.
