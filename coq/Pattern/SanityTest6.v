(** * Pattern.SanityTest6: AllOnes = AllOutOfEight

    Sanity Test 6: Verify AllOnes detector equals 8-of-8 threshold.

    This demonstrates:
    1. Pattern recognition and threshold functions are equivalent
    2. Different formulations produce identical circuits
    3. AllOnes is a special case of k-out-of-n threshold
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Base.Definitions.
Require Import Base.Tactics.
Require Import Base.Verification.
Require Import Pattern.AllOnes.
Require Import Threshold.AllOutOfEight.

Import ListNotations.

Open Scope Z_scope.

(** * Sanity Test 6: AllOnes = AllOutOfEight *)

(** Both circuits have identical weights and biases *)
Theorem sanity_test_6_weights_equal
  : all_ones_weights = all_out_of_eight_weights.
Proof.
  unfold all_ones_weights, all_out_of_eight_weights.
  reflexivity.
Qed.

Theorem sanity_test_6_bias_equal
  : all_ones_bias = all_out_of_eight_bias.
Proof.
  unfold all_ones_bias, all_out_of_eight_bias.
  reflexivity.
Qed.

(** The circuits are identical *)
Theorem sanity_test_6_circuits_equal
  : forall xs, all_ones_circuit xs = all_out_of_eight_circuit xs.
Proof.
  intro xs.
  unfold all_ones_circuit, all_out_of_eight_circuit.
  rewrite sanity_test_6_weights_equal.
  rewrite sanity_test_6_bias_equal.
  reflexivity.
Qed.

(** Exhaustive verification on 8-bit inputs *)
Theorem sanity_test_6_exhaustive
  : forall x0 x1 x2 x3 x4 x5 x6 x7,
    all_ones_circuit [x0; x1; x2; x3; x4; x5; x6; x7] =
    all_out_of_eight_circuit [x0; x1; x2; x3; x4; x5; x6; x7].
Proof.
  intros.
  apply sanity_test_6_circuits_equal.
Qed.

(** Both detect only the all-ones input *)
Theorem sanity_test_6_only_all_ones
  : all_ones_circuit [true; true; true; true; true; true; true; true] = true /\
    all_out_of_eight_circuit [true; true; true; true; true; true; true; true] = true /\
    all_ones_circuit [true; true; true; true; true; true; true; false] = false /\
    all_out_of_eight_circuit [true; true; true; true; true; true; true; false] = false.
Proof.
  repeat split; vm_compute; reflexivity.
Qed.

(** SANITY TEST 6 PASSES: AllOnes = AllOutOfEight *)
Theorem sanity_test_6_complete
  : (all_ones_weights = all_out_of_eight_weights) /\
    (all_ones_bias = all_out_of_eight_bias) /\
    (forall xs, all_ones_circuit xs = all_out_of_eight_circuit xs).
Proof.
  split.
  apply sanity_test_6_weights_equal.
  split.
  apply sanity_test_6_bias_equal.
  apply sanity_test_6_circuits_equal.
Qed.
