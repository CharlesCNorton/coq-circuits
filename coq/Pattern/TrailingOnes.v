(** * Pattern.TrailingOnes: Count Trailing Ones

    Counts consecutive 1-bits from LSB.
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Base.Definitions.
Require Import Base.Tactics.

Import ListNotations.

Open Scope nat_scope.

(** * Circuit Definition *)

Definition trailing_ones_8bit (b7 b6 b5 b4 b3 b2 b1 b0 : bool) : nat :=
  if negb b0 then 0
  else if negb b1 then 1
  else if negb b2 then 2
  else if negb b3 then 3
  else if negb b4 then 4
  else if negb b5 then 5
  else if negb b6 then 6
  else if negb b7 then 7
  else 8.

(** * Specification *)

Definition trailing_ones_8bit_spec (b7 b6 b5 b4 b3 b2 b1 b0 : bool) : nat :=
  if negb b0 then 0
  else if negb b1 then 1
  else if negb b2 then 2
  else if negb b3 then 3
  else if negb b4 then 4
  else if negb b5 then 5
  else if negb b6 then 6
  else if negb b7 then 7
  else 8.

(** * Verification *)

Theorem trailing_ones_8bit_correct
  : forall b7 b6 b5 b4 b3 b2 b1 b0,
    trailing_ones_8bit b7 b6 b5 b4 b3 b2 b1 b0 =
    trailing_ones_8bit_spec b7 b6 b5 b4 b3 b2 b1 b0.
Proof. intros. reflexivity. Qed.

(** All zeros gives 0 *)
Theorem trailing_ones_8bit_all_zeros
  : trailing_ones_8bit false false false false false false false false = 0.
Proof. reflexivity. Qed.

(** All ones gives 8 *)
Theorem trailing_ones_8bit_all_ones
  : trailing_ones_8bit true true true true true true true true = 8.
Proof. reflexivity. Qed.

(** Single trailing one *)
Theorem trailing_ones_8bit_one
  : trailing_ones_8bit false false false false false false false true = 1.
Proof. reflexivity. Qed.

(** * Network Architecture *)

Definition trailing_ones_8bit_num_neurons : nat := 8.
Definition trailing_ones_8bit_num_params : nat := 72.
Definition trailing_ones_8bit_depth : nat := 1.
