(** * Pattern.Symmetry8Bit: Palindrome Detector

    Returns true if bit pattern is symmetric (palindrome).
    b7=b0, b6=b1, b5=b2, b4=b3
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Base.Definitions.
Require Import Base.Tactics.

Import ListNotations.

Open Scope Z_scope.

(** * Circuit Definition *)

Definition symmetry_8bit (b7 b6 b5 b4 b3 b2 b1 b0 : bool) : bool :=
  andb (andb (Bool.eqb b7 b0) (Bool.eqb b6 b1))
       (andb (Bool.eqb b5 b2) (Bool.eqb b4 b3)).

(** * Specification *)

Definition symmetry_8bit_spec (b7 b6 b5 b4 b3 b2 b1 b0 : bool) : bool :=
  andb (andb (Bool.eqb b7 b0) (Bool.eqb b6 b1))
       (andb (Bool.eqb b5 b2) (Bool.eqb b4 b3)).

(** * Verification *)

Theorem symmetry_8bit_correct
  : forall b7 b6 b5 b4 b3 b2 b1 b0,
    symmetry_8bit b7 b6 b5 b4 b3 b2 b1 b0 =
    symmetry_8bit_spec b7 b6 b5 b4 b3 b2 b1 b0.
Proof. intros. reflexivity. Qed.

(** All zeros is symmetric *)
Theorem symmetry_8bit_all_zeros
  : symmetry_8bit false false false false false false false false = true.
Proof. reflexivity. Qed.

(** All ones is symmetric *)
Theorem symmetry_8bit_all_ones
  : symmetry_8bit true true true true true true true true = true.
Proof. reflexivity. Qed.

(** 10000001 is symmetric *)
Theorem symmetry_8bit_example
  : symmetry_8bit true false false false false false false true = true.
Proof. reflexivity. Qed.

(** 10000000 is not symmetric *)
Theorem symmetry_8bit_not_example
  : symmetry_8bit true false false false false false false false = false.
Proof. reflexivity. Qed.

(** * Network Architecture *)

Definition symmetry_8bit_num_neurons : nat := 7.
Definition symmetry_8bit_num_params : nat := 21.
Definition symmetry_8bit_depth : nat := 3.
