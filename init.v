From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section monad.
  Context (A : Type) (B : Type).

  Inductive Maybe A : Type :=
  | None : Maybe A
  | Some : A -> Maybe A.

  Definition ret A (x : A) : Maybe A := Some x.

  Definition bind (m : Maybe A) (f : A -> Maybe B) : Maybe B :=
    match m with
    | None => None B
    | Some x => f x
    end.


End monad.
Notation "x >>= f" := (bind x f) (at level 50, left associativity).

Section Example.

  Definition example1 : Maybe nat :=
    ret 10 >>=
      (fun x =>
         ret (x + 1) >>=
           (fun y =>
              ret (y + x))).

  Definition example2 a b : Maybe nat :=
    ret a >>= (fun x =>
    ret b >>= (fun y =>
      ret (x + y))).

  Compute example1.
  Compute example2 10 10.

End Example.
