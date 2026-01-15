(** * Pattern.SanityTest12: HammingDistance = PopCount(XOR)

    Sanity Test 12: Verify HammingDistance(A,B) = PopCount(A XOR B).

    This demonstrates:
    1. Hamming distance counts differing bit positions
    2. XOR marks positions where bits differ
    3. PopCount counts the XOR result
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Base.Definitions.
Require Import Base.Tactics.
Require Import Pattern.HammingDistance8Bit.
Require Import Pattern.PopCount.

Import ListNotations.

Open Scope nat_scope.

(** * Sanity Test 12: HammingDistance = PopCount(XOR) *)

(** PopCount of XOR equals hamming distance *)
Theorem sanity_test_12_hamming_via_xor
  : forall a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0,
    hamming_distance_8bit a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0 =
    popcount_8bit (xorb a7 b7) (xorb a6 b6) (xorb a5 b5) (xorb a4 b4)
                  (xorb a3 b3) (xorb a2 b2) (xorb a1 b1) (xorb a0 b0).
Proof.
  intros.
  unfold hamming_distance_8bit, popcount_8bit.
  destruct a7, a6, a5, a4, a3, a2, a1, a0, b7, b6, b5, b4, b3, b2, b1, b0;
  reflexivity.
Qed.

(** Distance from self is 0 *)
Theorem sanity_test_12_self_distance
  : forall a7 a6 a5 a4 a3 a2 a1 a0,
    hamming_distance_8bit a7 a6 a5 a4 a3 a2 a1 a0 a7 a6 a5 a4 a3 a2 a1 a0 = 0.
Proof.
  apply hamming_distance_8bit_self.
Qed.

(** Maximum distance is 8 (all bits differ) *)
Theorem sanity_test_12_max_distance
  : hamming_distance_8bit false false false false false false false false
                          true true true true true true true true = 8.
Proof.
  apply hamming_distance_8bit_extremes.
Qed.

(** XOR captures bit differences *)
Theorem sanity_test_12_xor_differences
  : forall a b, xorb a b = true <-> a <> b.
Proof.
  intros.
  destruct a, b; split; intro H; try reflexivity; try discriminate; try congruence.
Qed.

(** Distance is symmetric *)
Theorem sanity_test_12_symmetric
  : forall a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0,
    hamming_distance_8bit a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0 =
    hamming_distance_8bit b7 b6 b5 b4 b3 b2 b1 b0 a7 a6 a5 a4 a3 a2 a1 a0.
Proof.
  apply hamming_distance_8bit_sym.
Qed.

(** Single bit difference gives distance 1 *)
Theorem sanity_test_12_single_diff
  : hamming_distance_8bit false false false false false false false false
                          true false false false false false false false = 1 /\
    hamming_distance_8bit false false false false false false false false
                          false false false false false false false true = 1.
Proof.
  split; reflexivity.
Qed.

(** SANITY TEST 12 PASSES: HammingDistance = PopCount(XOR) *)
Theorem sanity_test_12_complete
  : forall a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0,
    hamming_distance_8bit a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0 =
    popcount_8bit (xorb a7 b7) (xorb a6 b6) (xorb a5 b5) (xorb a4 b4)
                  (xorb a3 b3) (xorb a2 b2) (xorb a1 b1) (xorb a0 b0).
Proof.
  apply sanity_test_12_hamming_via_xor.
Qed.
