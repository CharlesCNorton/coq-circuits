(** * Pattern.SanityTest7: AllZeros = NOT(OneOutOfEight)

    Sanity Test 7: Verify AllZeros = negation of 1-of-8 threshold.

    This demonstrates:
    1. AllZeros fires when NO inputs are true
    2. OneOutOfEight fires when AT LEAST ONE input is true
    3. These are logical complements
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Lia.
Require Import Base.Definitions.
Require Import Base.Tactics.
Require Import Base.Verification.
Require Import Pattern.AllZeros.
Require Import Threshold.OneOutOfEight.

Import ListNotations.

Open Scope Z_scope.

(** * Sanity Test 7: AllZeros = NOT(OneOutOfEight) *)

(** Logical complement relationship *)
Theorem sanity_test_7_complement
  : forall x0 x1 x2 x3 x4 x5 x6 x7,
    all_zeros_circuit [x0; x1; x2; x3; x4; x5; x6; x7] =
    negb (one_out_of_eight_circuit [x0; x1; x2; x3; x4; x5; x6; x7]).
Proof.
  intros.
  unfold all_zeros_circuit, one_out_of_eight_circuit, gate.
  unfold all_zeros_weights, all_zeros_bias.
  unfold one_out_of_eight_weights, one_out_of_eight_bias.
  destruct x0, x1, x2, x3, x4, x5, x6, x7; vm_compute; reflexivity.
Qed.

(** Exhaustive verification *)
Theorem sanity_test_7_exhaustive
  : verify_all (fun xs =>
      Bool.eqb (all_zeros_circuit xs)
               (negb (one_out_of_eight_circuit xs))) = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

(** AllZeros fires only on all-zeros input *)
Theorem sanity_test_7_all_zeros_only
  : all_zeros_circuit [false; false; false; false; false; false; false; false] = true /\
    one_out_of_eight_circuit [false; false; false; false; false; false; false; false] = false.
Proof.
  split; vm_compute; reflexivity.
Qed.

(** Any single true bit flips both *)
Theorem sanity_test_7_single_bit
  : all_zeros_circuit [true; false; false; false; false; false; false; false] = false /\
    one_out_of_eight_circuit [true; false; false; false; false; false; false; false] = true.
Proof.
  split; vm_compute; reflexivity.
Qed.

(** Algebraic characterization *)
Theorem sanity_test_7_hamming_weight
  : forall x0 x1 x2 x3 x4 x5 x6 x7,
    let xs := [x0; x1; x2; x3; x4; x5; x6; x7] in
    (all_zeros_circuit xs = true <-> hamming_weight xs = 0%nat) /\
    (one_out_of_eight_circuit xs = true <-> (hamming_weight xs >= 1)%nat).
Proof.
  intros.
  destruct x0, x1, x2, x3, x4, x5, x6, x7;
  split; split; intro H; vm_compute in *; try reflexivity; try discriminate; try lia.
Qed.

(** SANITY TEST 7 PASSES: AllZeros = NOT(OneOutOfEight) *)
Theorem sanity_test_7_complete
  : forall x0 x1 x2 x3 x4 x5 x6 x7,
    all_zeros_circuit [x0; x1; x2; x3; x4; x5; x6; x7] =
    negb (one_out_of_eight_circuit [x0; x1; x2; x3; x4; x5; x6; x7]).
Proof.
  apply sanity_test_7_complement.
Qed.
