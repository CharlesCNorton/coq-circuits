(** * Pattern.PopCount: Population Count (Hamming Weight)

    Counts the number of 1-bits in an 8-bit input.
    Output is 4 bits (0-8).
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Base.Definitions.
Require Import Base.Tactics.

Import ListNotations.

Open Scope nat_scope.

(** * Circuit Definition *)

Definition popcount_8bit (b7 b6 b5 b4 b3 b2 b1 b0 : bool) : nat :=
  (if b7 then 1 else 0) + (if b6 then 1 else 0) +
  (if b5 then 1 else 0) + (if b4 then 1 else 0) +
  (if b3 then 1 else 0) + (if b2 then 1 else 0) +
  (if b1 then 1 else 0) + (if b0 then 1 else 0).

(** Binary output representation *)
Definition popcount_8bit_binary (b7 b6 b5 b4 b3 b2 b1 b0 : bool)
  : bool * bool * bool * bool :=
  let count := popcount_8bit b7 b6 b5 b4 b3 b2 b1 b0 in
  (Nat.leb 8 count, Nat.odd (count / 4), Nat.odd (count / 2), Nat.odd count).

(** * Specification *)

Definition popcount_8bit_spec (b7 b6 b5 b4 b3 b2 b1 b0 : bool) : nat :=
  hamming_weight [b0; b1; b2; b3; b4; b5; b6; b7].

(** * Verification *)

Theorem popcount_8bit_correct
  : forall b7 b6 b5 b4 b3 b2 b1 b0,
    popcount_8bit b7 b6 b5 b4 b3 b2 b1 b0 =
    popcount_8bit_spec b7 b6 b5 b4 b3 b2 b1 b0.
Proof.
  intros.
  unfold popcount_8bit, popcount_8bit_spec, hamming_weight.
  destruct b7, b6, b5, b4, b3, b2, b1, b0; reflexivity.
Qed.

(** All zeros gives 0 *)
Theorem popcount_8bit_all_zeros
  : popcount_8bit false false false false false false false false = 0.
Proof. reflexivity. Qed.

(** All ones gives 8 *)
Theorem popcount_8bit_all_ones
  : popcount_8bit true true true true true true true true = 8.
Proof. reflexivity. Qed.

(** * Network Architecture *)

Definition popcount_8bit_num_neurons : nat := 9.
Definition popcount_8bit_num_params : nat := 81.
Definition popcount_8bit_depth : nat := 1.
