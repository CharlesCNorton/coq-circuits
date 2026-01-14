(** * Threshold.AtLeastK: Parametric At-Least-K Threshold

    Parameterized threshold: fires when at least k of 8 inputs are true.
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

(** AtLeastK weights: all ones for 8 inputs. *)
Definition at_least_k_weights
  : list Z
  := ones8.

(** AtLeastK bias: -k. *)
Definition at_least_k_bias (k : nat)
  : Z
  := - (Z.of_nat k).

(** AtLeastK circuit. *)
Definition at_least_k_circuit (k : nat) (xs : list bool)
  : bool
  := gate at_least_k_weights (at_least_k_bias k) xs.

(** * Specification *)

Definition at_least_k_spec (k : nat) (xs : list bool)
  : bool
  := Nat.leb k (hamming_weight xs).

(** * Verification *)

(** AtLeastK circuit is correct for k=5 (majority). *)
Theorem at_least_5_correct
  : forall x0 x1 x2 x3 x4 x5 x6 x7,
    at_least_k_circuit 5 [x0; x1; x2; x3; x4; x5; x6; x7] =
    at_least_k_spec 5 [x0; x1; x2; x3; x4; x5; x6; x7].
Proof.
  intros.
  unfold at_least_k_circuit, at_least_k_spec, gate.
  unfold at_least_k_weights, at_least_k_bias.
  destruct x0, x1, x2, x3, x4, x5, x6, x7; vm_compute; reflexivity.
Qed.

(** * Algebraic Characterization *)

(** AtLeastK is characterized by hamming weight for specific k values. *)
Theorem at_least_k_hamming_weight_5 (xs : list bool)
  : length xs = 8%nat ->
    at_least_k_circuit 5 xs = true <-> (hamming_weight xs >= 5)%nat.
Proof.
  intro Hlen.
  unfold at_least_k_circuit, gate, at_least_k_weights, at_least_k_bias.
  destruct xs as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|x6 [|x7 [|]]]]]]]]]; try discriminate.
  clear Hlen.
  destruct x0, x1, x2, x3, x4, x5, x6, x7; simpl; split; intro H; try reflexivity; try discriminate; try lia.
Qed.

(** * Length Safety *)

Lemma at_least_k_weights_length
  : length at_least_k_weights = 8%nat.
Proof. unfold at_least_k_weights. apply ones8_length. Qed.

Theorem at_least_k_length_requirement (k : nat) (xs : list bool)
  : length xs = 8%nat ->
    gate_length_ok at_least_k_weights xs.
Proof.
  intro Hlen.
  unfold gate_length_ok.
  rewrite at_least_k_weights_length.
  symmetry.
  exact Hlen.
Qed.

(** * Network Architecture *)

Definition at_least_k_num_params : nat := 9.
Definition at_least_k_num_neurons : nat := 1.
Definition at_least_k_depth : nat := 1.
