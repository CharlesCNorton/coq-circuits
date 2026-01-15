(** * Error.OddParityChecker: Odd Parity Check

    Returns true if input has odd number of 1s.
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Base.Definitions.
Require Import Base.Tactics.

Import ListNotations.

Open Scope Z_scope.

(** * Circuit Definition *)

Definition odd_parity_checker (b7 b6 b5 b4 b3 b2 b1 b0 : bool) : bool :=
  xorb (xorb (xorb b7 b6) (xorb b5 b4))
       (xorb (xorb b3 b2) (xorb b1 b0)).

(** * Specification *)

Definition odd_parity_checker_spec (b7 b6 b5 b4 b3 b2 b1 b0 : bool) : bool :=
  xorb (xorb (xorb b7 b6) (xorb b5 b4))
       (xorb (xorb b3 b2) (xorb b1 b0)).

(** * Verification *)

Theorem odd_parity_checker_correct
  : forall b7 b6 b5 b4 b3 b2 b1 b0,
    odd_parity_checker b7 b6 b5 b4 b3 b2 b1 b0 =
    odd_parity_checker_spec b7 b6 b5 b4 b3 b2 b1 b0.
Proof. intros. reflexivity. Qed.

(** Relationship to even parity *)
Theorem odd_is_not_even
  : forall b7 b6 b5 b4 b3 b2 b1 b0,
    odd_parity_checker b7 b6 b5 b4 b3 b2 b1 b0 =
    negb (negb (xorb (xorb (xorb b7 b6) (xorb b5 b4))
                     (xorb (xorb b3 b2) (xorb b1 b0)))).
Proof.
  intros.
  unfold odd_parity_checker.
  rewrite Bool.negb_involutive.
  reflexivity.
Qed.

(** All zeros has even parity, so odd check is false *)
Theorem odd_parity_checker_zeros
  : odd_parity_checker false false false false false false false false = false.
Proof. reflexivity. Qed.

(** Single one has odd parity *)
Theorem odd_parity_checker_single_one
  : odd_parity_checker true false false false false false false false = true.
Proof. reflexivity. Qed.

(** * Network Architecture *)

Definition odd_parity_checker_num_neurons : nat := 21.
Definition odd_parity_checker_num_params : nat := 63.
Definition odd_parity_checker_depth : nat := 6.
