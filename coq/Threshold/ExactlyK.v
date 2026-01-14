(** * Threshold.ExactlyK: Parametric Exactly-K Threshold

    Parameterized threshold: fires when exactly k of 8 inputs are true.
    Implemented as AND(AtLeastK, AtMostK).
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Lia.
Require Import Base.Definitions.
Require Import Base.Tactics.
Require Import Base.Verification.
Require Import Threshold.AtLeastK.
Require Import Threshold.AtMostK.

Import ListNotations.

Open Scope Z_scope.

(** * Circuit Definition *)

(** ExactlyK is a 2-layer circuit: AtLeastK AND AtMostK. *)
Definition exactly_k_circuit (k : nat) (xs : list bool)
  : bool
  :=
  let at_least := at_least_k_circuit k xs in
  let at_most := at_most_k_circuit k xs in
  andb at_least at_most.

(** * Specification *)

Definition exactly_k_spec (k : nat) (xs : list bool)
  : bool
  := Nat.eqb (hamming_weight xs) k.

(** * Verification *)

(** ExactlyK circuit is correct for k=4. *)
Theorem exactly_4_correct
  : forall x0 x1 x2 x3 x4 x5 x6 x7,
    exactly_k_circuit 4 [x0; x1; x2; x3; x4; x5; x6; x7] =
    exactly_k_spec 4 [x0; x1; x2; x3; x4; x5; x6; x7].
Proof.
  intros.
  unfold exactly_k_circuit, exactly_k_spec.
  unfold at_least_k_circuit, at_most_k_circuit, gate.
  unfold at_least_k_weights, at_least_k_bias.
  unfold at_most_k_weights, at_most_k_bias.
  destruct x0, x1, x2, x3, x4, x5, x6, x7; vm_compute; reflexivity.
Qed.

(** * Algebraic Characterization *)

(** ExactlyK is characterized by hamming weight equality for k=4. *)
Theorem exactly_k_hamming_weight_4 (xs : list bool)
  : length xs = 8%nat ->
    exactly_k_circuit 4 xs = true <-> hamming_weight xs = 4%nat.
Proof.
  intro Hlen.
  unfold exactly_k_circuit.
  rewrite Bool.andb_true_iff.
  unfold at_least_k_circuit, at_most_k_circuit, gate.
  unfold at_least_k_weights, at_least_k_bias.
  unfold at_most_k_weights, at_most_k_bias.
  destruct xs as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|x6 [|x7 [|]]]]]]]]]; try discriminate.
  clear Hlen.
  destruct x0, x1, x2, x3, x4, x5, x6, x7; simpl; split; intro H; try reflexivity; try discriminate; try lia.
Qed.

(** * Network Architecture *)

Definition exactly_k_num_params : nat := 18.
Definition exactly_k_num_neurons : nat := 2.
Definition exactly_k_depth : nat := 2.
