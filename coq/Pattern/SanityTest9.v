(** * Pattern.SanityTest9: OneHotDetector = ExactlyK(1)

    Sanity Test 9: Verify OneHotDetector equals ExactlyK(1).

    This demonstrates:
    1. One-hot detection is a special case of exactly-k threshold
    2. Different implementations produce identical results
    3. Pattern recognition matches threshold composition
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Base.Definitions.
Require Import Base.Tactics.
Require Import Base.Verification.
Require Import Pattern.OneHotDetector.
Require Import Threshold.AtLeastK.
Require Import Threshold.AtMostK.
Require Import Threshold.ExactlyK.

Import ListNotations.

Open Scope Z_scope.

(** * Sanity Test 9: OneHotDetector = ExactlyK(1) *)

(** Both circuits are equivalent *)
Theorem sanity_test_9_equivalence
  : forall x0 x1 x2 x3 x4 x5 x6 x7,
    one_hot_circuit [x0; x1; x2; x3; x4; x5; x6; x7] =
    exactly_k_circuit 1 [x0; x1; x2; x3; x4; x5; x6; x7].
Proof.
  intros.
  unfold one_hot_circuit, exactly_k_circuit.
  unfold at_least_k_circuit, at_most_k_circuit, gate.
  unfold at_least_k_weights, at_least_k_bias.
  unfold at_most_k_weights, at_most_k_bias.
  destruct x0, x1, x2, x3, x4, x5, x6, x7; vm_compute; reflexivity.
Qed.

(** Exhaustive verification *)
Theorem sanity_test_9_exhaustive
  : verify_all (fun xs =>
      Bool.eqb (one_hot_circuit xs)
               (exactly_k_circuit 1 xs)) = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

(** Both match hamming weight = 1 *)
Theorem sanity_test_9_hamming_weight
  : forall x0 x1 x2 x3 x4 x5 x6 x7,
    let xs := [x0; x1; x2; x3; x4; x5; x6; x7] in
    one_hot_circuit xs = Nat.eqb (hamming_weight xs) 1 /\
    exactly_k_circuit 1 xs = Nat.eqb (hamming_weight xs) 1.
Proof.
  intros.
  split.
  - apply one_hot_correct.
  - unfold exactly_k_circuit, exactly_k_spec.
    unfold at_least_k_circuit, at_most_k_circuit, gate.
    unfold at_least_k_weights, at_least_k_bias.
    unfold at_most_k_weights, at_most_k_bias.
    destruct x0, x1, x2, x3, x4, x5, x6, x7; vm_compute; reflexivity.
Qed.

(** Zero bits: neither fires *)
Theorem sanity_test_9_zero_bits
  : one_hot_circuit [false; false; false; false; false; false; false; false] = false /\
    exactly_k_circuit 1 [false; false; false; false; false; false; false; false] = false.
Proof.
  split; vm_compute; reflexivity.
Qed.

(** One bit: both fire *)
Theorem sanity_test_9_one_bit
  : one_hot_circuit [true; false; false; false; false; false; false; false] = true /\
    exactly_k_circuit 1 [true; false; false; false; false; false; false; false] = true.
Proof.
  split; vm_compute; reflexivity.
Qed.

(** Two bits: neither fires *)
Theorem sanity_test_9_two_bits
  : one_hot_circuit [true; true; false; false; false; false; false; false] = false /\
    exactly_k_circuit 1 [true; true; false; false; false; false; false; false] = false.
Proof.
  split; vm_compute; reflexivity.
Qed.

(** SANITY TEST 9 PASSES: OneHotDetector = ExactlyK(1) *)
Theorem sanity_test_9_complete
  : forall x0 x1 x2 x3 x4 x5 x6 x7,
    one_hot_circuit [x0; x1; x2; x3; x4; x5; x6; x7] =
    exactly_k_circuit 1 [x0; x1; x2; x3; x4; x5; x6; x7].
Proof.
  apply sanity_test_9_equivalence.
Qed.
