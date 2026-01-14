(** * Threshold.FourOutOfEight: 4-out-of-8 Threshold Gate

    Fires when at least 4 of 8 inputs are true.
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

Definition four_out_of_eight_weights : list Z := ones8.
Definition four_out_of_eight_bias : Z := -4.

Definition four_out_of_eight_circuit (xs : list bool) : bool :=
  gate four_out_of_eight_weights four_out_of_eight_bias xs.

Definition four_out_of_eight_spec (xs : list bool) : bool :=
  Nat.leb 4 (hamming_weight xs).

Theorem four_out_of_eight_correct
  : forall x0 x1 x2 x3 x4 x5 x6 x7,
    four_out_of_eight_circuit [x0; x1; x2; x3; x4; x5; x6; x7] =
    four_out_of_eight_spec [x0; x1; x2; x3; x4; x5; x6; x7].
Proof.
  intros.
  unfold four_out_of_eight_circuit, four_out_of_eight_spec, gate.
  unfold four_out_of_eight_weights, four_out_of_eight_bias.
  destruct x0, x1, x2, x3, x4, x5, x6, x7; vm_compute; reflexivity.
Qed.

Lemma four_out_of_eight_weights_length
  : length four_out_of_eight_weights = 8%nat.
Proof. unfold four_out_of_eight_weights. apply ones8_length. Qed.

Theorem four_out_of_eight_length_requirement (xs : list bool)
  : length xs = 8%nat -> gate_length_ok four_out_of_eight_weights xs.
Proof.
  intro Hlen.
  unfold gate_length_ok.
  rewrite four_out_of_eight_weights_length.
  symmetry.
  exact Hlen.
Qed.

Definition four_out_of_eight_num_params : nat := 9.
