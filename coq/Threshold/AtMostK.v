(** * Threshold.AtMostK: Parametric At-Most-K Threshold

    Parameterized threshold: fires when at most k of 8 inputs are true.
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

(** AtMostK weights: all negative ones for 8 inputs. *)
Definition at_most_k_weights
  : list Z
  := [-1; -1; -1; -1; -1; -1; -1; -1].

(** AtMostK bias: k. *)
Definition at_most_k_bias (k : nat)
  : Z
  := Z.of_nat k.

(** AtMostK circuit. *)
Definition at_most_k_circuit (k : nat) (xs : list bool)
  : bool
  := gate at_most_k_weights (at_most_k_bias k) xs.

(** * Specification *)

Definition at_most_k_spec (k : nat) (xs : list bool)
  : bool
  := Nat.leb (hamming_weight xs) k.

(** * Verification *)

(** AtMostK circuit is correct for k=3 (minority). *)
Theorem at_most_3_correct
  : forall x0 x1 x2 x3 x4 x5 x6 x7,
    at_most_k_circuit 3 [x0; x1; x2; x3; x4; x5; x6; x7] =
    at_most_k_spec 3 [x0; x1; x2; x3; x4; x5; x6; x7].
Proof.
  intros.
  unfold at_most_k_circuit, at_most_k_spec, gate.
  unfold at_most_k_weights, at_most_k_bias.
  destruct x0, x1, x2, x3, x4, x5, x6, x7; vm_compute; reflexivity.
Qed.

(** * Algebraic Characterization *)

(** AtMostK is characterized by hamming weight for specific k values. *)
Theorem at_most_k_hamming_weight_3 (xs : list bool)
  : length xs = 8%nat ->
    at_most_k_circuit 3 xs = true <-> (hamming_weight xs <= 3)%nat.
Proof.
  intro Hlen.
  unfold at_most_k_circuit, gate, at_most_k_weights, at_most_k_bias.
  destruct xs as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|x6 [|x7 [|]]]]]]]]]; try discriminate.
  clear Hlen.
  destruct x0, x1, x2, x3, x4, x5, x6, x7; simpl; split; intro H; try reflexivity; try discriminate; try lia.
Qed.

(** * Length Safety *)

Lemma at_most_k_weights_length
  : length at_most_k_weights = 8%nat.
Proof. reflexivity. Qed.

Theorem at_most_k_length_requirement (k : nat) (xs : list bool)
  : length xs = 8%nat ->
    gate_length_ok at_most_k_weights xs.
Proof.
  intro Hlen.
  unfold gate_length_ok.
  rewrite at_most_k_weights_length.
  symmetry.
  exact Hlen.
Qed.

(** * Network Architecture *)

Definition at_most_k_num_params : nat := 9.
Definition at_most_k_num_neurons : nat := 1.
Definition at_most_k_depth : nat := 1.
