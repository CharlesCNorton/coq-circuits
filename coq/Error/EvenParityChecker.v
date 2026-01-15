(** * Error.EvenParityChecker: Even Parity Check

    Returns true if input has even number of 1s.
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Base.Definitions.
Require Import Base.Tactics.

Import ListNotations.

Open Scope Z_scope.

(** * Circuit Definition *)

Definition even_parity_checker (b7 b6 b5 b4 b3 b2 b1 b0 : bool) : bool :=
  negb (xorb (xorb (xorb b7 b6) (xorb b5 b4))
             (xorb (xorb b3 b2) (xorb b1 b0))).

(** * Specification *)

Definition even_parity_checker_spec (b7 b6 b5 b4 b3 b2 b1 b0 : bool) : bool :=
  negb (xorb (xorb (xorb b7 b6) (xorb b5 b4))
             (xorb (xorb b3 b2) (xorb b1 b0))).

(** * Verification *)

Theorem even_parity_checker_correct
  : forall b7 b6 b5 b4 b3 b2 b1 b0,
    even_parity_checker b7 b6 b5 b4 b3 b2 b1 b0 =
    even_parity_checker_spec b7 b6 b5 b4 b3 b2 b1 b0.
Proof. intros. reflexivity. Qed.

(** All zeros has even parity *)
Theorem even_parity_checker_zeros
  : even_parity_checker false false false false false false false false = true.
Proof. reflexivity. Qed.

(** Single one has odd parity *)
Theorem even_parity_checker_single_one
  : even_parity_checker true false false false false false false false = false.
Proof. reflexivity. Qed.

(** Two ones has even parity *)
Theorem even_parity_checker_two_ones
  : even_parity_checker true true false false false false false false = true.
Proof. reflexivity. Qed.

(** * Network Architecture *)

Definition even_parity_checker_num_neurons : nat := 22.
Definition even_parity_checker_num_params : nat := 66.
Definition even_parity_checker_depth : nat := 7.
