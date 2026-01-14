(** * Threshold.FiveOutOfEight: 5-out-of-8 Threshold Gate

    Formally verified 5-out-of-8 threshold gate.
    Fires when at least 5 of 8 inputs are true.
    Equivalent to Majority gate.
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Lia.
Require Import Base.Definitions.
Require Import Base.Tactics.
Require Import Base.Verification.
Require Import Threshold.Majority.

Import ListNotations.

Open Scope Z_scope.

(** * Circuit Definition *)

(** 5-out-of-8 weights: all ones. *)
Definition five_out_of_eight_weights
  : list Z
  := ones8.

(** 5-out-of-8 bias: -5. *)
Definition five_out_of_eight_bias
  : Z
  := -5.

(** 5-out-of-8 circuit. *)
Definition five_out_of_eight_circuit (xs : list bool)
  : bool
  := gate five_out_of_eight_weights five_out_of_eight_bias xs.

(** * Specification *)

Definition five_out_of_eight_spec (xs : list bool)
  : bool
  := Nat.leb 5 (hamming_weight xs).

(** * Verification *)

(** 5-out-of-8 circuit is correct. *)
Theorem five_out_of_eight_correct
  : forall x0 x1 x2 x3 x4 x5 x6 x7,
    five_out_of_eight_circuit [x0; x1; x2; x3; x4; x5; x6; x7] =
    five_out_of_eight_spec [x0; x1; x2; x3; x4; x5; x6; x7].
Proof.
  intros.
  unfold five_out_of_eight_circuit, five_out_of_eight_spec, gate.
  unfold five_out_of_eight_weights, five_out_of_eight_bias.
  destruct x0, x1, x2, x3, x4, x5, x6, x7; vm_compute; reflexivity.
Qed.

(** * Equivalence to Majority *)

(** 5-out-of-8 is equivalent to Majority. *)
Theorem five_out_of_eight_is_majority
  : forall x0 x1 x2 x3 x4 x5 x6 x7,
    five_out_of_eight_circuit [x0; x1; x2; x3; x4; x5; x6; x7] =
    majority_circuit [x0; x1; x2; x3; x4; x5; x6; x7].
Proof.
  intros.
  unfold five_out_of_eight_circuit, majority_circuit.
  unfold five_out_of_eight_weights, five_out_of_eight_bias.
  unfold majority_weights, majority_bias.
  reflexivity.
Qed.

(** * Length Safety *)

Lemma five_out_of_eight_weights_length
  : length five_out_of_eight_weights = 8%nat.
Proof. unfold five_out_of_eight_weights. apply ones8_length. Qed.

Theorem five_out_of_eight_length_requirement (xs : list bool)
  : length xs = 8%nat ->
    gate_length_ok five_out_of_eight_weights xs.
Proof.
  intro Hlen.
  unfold gate_length_ok.
  rewrite five_out_of_eight_weights_length.
  symmetry.
  exact Hlen.
Qed.

(** * Network Architecture *)

Definition five_out_of_eight_num_params : nat := 9.
Definition five_out_of_eight_num_neurons : nat := 1.
Definition five_out_of_eight_depth : nat := 1.
