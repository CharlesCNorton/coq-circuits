(** * Pattern.SanityTest8: PopCount = hamming_weight

    Sanity Test 8: Verify PopCount computes hamming_weight.

    This demonstrates:
    1. PopCount circuit matches specification
    2. Circuit output equals hamming_weight function
    3. Consistency between pattern recognition and base definitions
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Lia.
Require Import Base.Definitions.
Require Import Base.Tactics.
Require Import Base.Verification.
Require Import Pattern.PopCount.

Import ListNotations.

Open Scope nat_scope.

(** * Sanity Test 8: PopCount = hamming_weight *)

(** PopCount equals hamming_weight of reversed list *)
Theorem sanity_test_8_popcount_is_hamming
  : forall b7 b6 b5 b4 b3 b2 b1 b0,
    popcount_8bit b7 b6 b5 b4 b3 b2 b1 b0 =
    hamming_weight [b0; b1; b2; b3; b4; b5; b6; b7].
Proof.
  intros.
  unfold popcount_8bit, hamming_weight.
  destruct b7, b6, b5, b4, b3, b2, b1, b0; reflexivity.
Qed.

(** Exhaustive verification *)
Theorem sanity_test_8_exhaustive
  : forall b7 b6 b5 b4 b3 b2 b1 b0,
    popcount_8bit b7 b6 b5 b4 b3 b2 b1 b0 =
    popcount_8bit_spec b7 b6 b5 b4 b3 b2 b1 b0.
Proof.
  apply popcount_8bit_correct.
Qed.

(** Range is 0 to 8 *)
Theorem sanity_test_8_range
  : forall b7 b6 b5 b4 b3 b2 b1 b0,
    popcount_8bit b7 b6 b5 b4 b3 b2 b1 b0 <= 8.
Proof.
  intros.
  unfold popcount_8bit.
  destruct b7, b6, b5, b4, b3, b2, b1, b0; lia.
Qed.

(** Minimum is 0 (all zeros) *)
Theorem sanity_test_8_min
  : popcount_8bit false false false false false false false false = 0.
Proof. reflexivity. Qed.

(** Maximum is 8 (all ones) *)
Theorem sanity_test_8_max
  : popcount_8bit true true true true true true true true = 8.
Proof. reflexivity. Qed.

(** Intermediate values *)
Theorem sanity_test_8_examples
  : popcount_8bit true false false false false false false false = 1 /\
    popcount_8bit true true false false false false false false = 2 /\
    popcount_8bit true true true true false false false false = 4.
Proof.
  repeat split; reflexivity.
Qed.

(** SANITY TEST 8 PASSES: PopCount = hamming_weight *)
Theorem sanity_test_8_complete
  : forall b7 b6 b5 b4 b3 b2 b1 b0,
    popcount_8bit b7 b6 b5 b4 b3 b2 b1 b0 =
    hamming_weight [b0; b1; b2; b3; b4; b5; b6; b7].
Proof.
  apply sanity_test_8_popcount_is_hamming.
Qed.
