(** * Threshold.Majority: Majority Gate

    Formally verified majority gate for 8-bit inputs.
    Fires when more than half (≥5) of inputs are true.
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Lia.
Require Import Base.Definitions.
Require Import Base.Tactics.
Require Import Base.Verification.

Import ListNotations.

Open Scope Z_scope.

(** * Circuit Definition *)

(** Majority gate weights: all ones for 8 inputs. *)
Definition majority_weights
  : list Z
  := ones8.

(** Majority gate bias: -5 (requires at least 5 true inputs). *)
Definition majority_bias
  : Z
  := -5.

(** Majority circuit: fires when HW(xs) >= 5. *)
Definition majority_circuit (xs : list bool)
  : bool
  := gate majority_weights majority_bias xs.

(** * Specification *)

(** Majority holds when at least 5 of 8 inputs are true. *)
Definition majority_spec (xs : list bool)
  : bool
  := Nat.leb 5 (hamming_weight xs).

(** * Verification *)

(** Majority circuit computes majority correctly. *)
Theorem majority_correct
  : forall x0 x1 x2 x3 x4 x5 x6 x7,
    majority_circuit [x0; x1; x2; x3; x4; x5; x6; x7] =
    majority_spec [x0; x1; x2; x3; x4; x5; x6; x7].
Proof.
  intros.
  unfold majority_circuit, majority_spec, gate.
  unfold majority_weights, majority_bias.
  destruct x0, x1, x2, x3, x4, x5, x6, x7; vm_compute; reflexivity.
Qed.

(** Exhaustive verification via computation. *)
Theorem majority_exhaustive_verified
  : verify_all (fun xs => Bool.eqb (majority_circuit xs) (majority_spec xs)) = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

(** * Algebraic Characterization *)

(** Majority is characterized by hamming weight. *)
Theorem majority_hamming_weight (xs : list bool)
  : length xs = 8%nat ->
    majority_circuit xs = true <-> (hamming_weight xs >= 5)%nat.
Proof.
  intro Hlen.
  unfold majority_circuit, gate, majority_weights, majority_bias.
  destruct xs as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|x6 [|x7 [|]]]]]]]]]; try discriminate.
  clear Hlen.
  destruct x0, x1, x2, x3, x4, x5, x6, x7; simpl; split; intro H; try reflexivity; try discriminate; try lia.
Qed.

(** Majority equals 5-out-of-8 threshold. *)
Theorem majority_is_five_out_of_eight (xs : list bool)
  : length xs = 8%nat ->
    majority_circuit xs = Nat.leb 5 (hamming_weight xs).
Proof.
  intro Hlen.
  destruct xs as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|x6 [|x7 [|]]]]]]]]]; try discriminate.
  clear Hlen.
  unfold majority_circuit, gate, majority_weights, majority_bias.
  destruct x0, x1, x2, x3, x4, x5, x6, x7; vm_compute; reflexivity.
Qed.

(** * Length Safety *)

(** Majority weights have length 8 *)
Lemma majority_weights_length
  : length majority_weights = 8%nat.
Proof.
  unfold majority_weights.
  apply ones8_length.
Qed.

(** Majority requires exactly 8 inputs *)
Theorem majority_length_requirement (xs : list bool)
  : length xs = 8%nat ->
    gate_length_ok majority_weights xs.
Proof.
  intro Hlen.
  unfold gate_length_ok.
  rewrite majority_weights_length.
  symmetry.
  exact Hlen.
Qed.

(** * Properties *)

(** All true gives majority. *)
Lemma majority_all_true
  : majority_circuit [true; true; true; true; true; true; true; true] = true.
Proof. vm_compute. reflexivity. Qed.

(** All false gives no majority. *)
Lemma majority_all_false
  : majority_circuit [false; false; false; false; false; false; false; false] = false.
Proof. vm_compute. reflexivity. Qed.

(** Majority with exactly 4 true is false. *)
Lemma majority_exactly_four_false
  : majority_circuit [true; true; true; true; false; false; false; false] = false.
Proof.
  vm_compute.
  reflexivity.
Qed.

(** * Network Architecture *)

(** Total parameters: 9 (8 weights + 1 bias). *)
Definition majority_num_params : nat := 9.

(** Single neuron. *)
Definition majority_num_neurons : nat := 1.

(** Network depth: 1 layer. *)
Definition majority_depth : nat := 1.
