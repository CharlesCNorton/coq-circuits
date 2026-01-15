(** * Pattern.OneHotDetector: One-Hot Detector

    Fires when exactly one of 8 input bits is true.
    Equivalent to ExactlyK(1).
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

(** One-hot = AtLeast(1) AND AtMost(1) *)
Definition one_hot_circuit (xs : list bool) : bool :=
  andb (at_least_k_circuit 1 xs) (at_most_k_circuit 1 xs).

(** * Specification *)

Definition one_hot_spec (xs : list bool) : bool :=
  Nat.eqb (hamming_weight xs) 1.

(** * Verification *)

Theorem one_hot_correct
  : forall x0 x1 x2 x3 x4 x5 x6 x7,
    one_hot_circuit [x0; x1; x2; x3; x4; x5; x6; x7] =
    one_hot_spec [x0; x1; x2; x3; x4; x5; x6; x7].
Proof.
  intros.
  unfold one_hot_circuit, one_hot_spec.
  unfold at_least_k_circuit, at_most_k_circuit, gate.
  unfold at_least_k_weights, at_least_k_bias.
  unfold at_most_k_weights, at_most_k_bias.
  destruct x0, x1, x2, x3, x4, x5, x6, x7; vm_compute; reflexivity.
Qed.

Theorem one_hot_exhaustive
  : verify_all (fun xs =>
      Bool.eqb (one_hot_circuit xs) (one_hot_spec xs)) = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

(** * Properties *)

Lemma one_hot_single_bit
  : one_hot_circuit [true; false; false; false; false; false; false; false] = true.
Proof. vm_compute. reflexivity. Qed.

Lemma one_hot_no_bits
  : one_hot_circuit [false; false; false; false; false; false; false; false] = false.
Proof. vm_compute. reflexivity. Qed.

Lemma one_hot_two_bits
  : one_hot_circuit [true; true; false; false; false; false; false; false] = false.
Proof. vm_compute. reflexivity. Qed.

Lemma one_hot_all_bits
  : one_hot_circuit [true; true; true; true; true; true; true; true] = false.
Proof. vm_compute. reflexivity. Qed.

(** Any single bit position gives one-hot *)
Lemma one_hot_any_position
  : one_hot_circuit [false; true; false; false; false; false; false; false] = true /\
    one_hot_circuit [false; false; true; false; false; false; false; false] = true /\
    one_hot_circuit [false; false; false; true; false; false; false; false] = true /\
    one_hot_circuit [false; false; false; false; true; false; false; false] = true /\
    one_hot_circuit [false; false; false; false; false; true; false; false] = true /\
    one_hot_circuit [false; false; false; false; false; false; true; false] = true /\
    one_hot_circuit [false; false; false; false; false; false; false; true] = true.
Proof.
  repeat split; vm_compute; reflexivity.
Qed.

(** * Algebraic Characterization *)

Theorem one_hot_hamming_weight (xs : list bool)
  : length xs = 8%nat ->
    one_hot_circuit xs = true <-> hamming_weight xs = 1%nat.
Proof.
  intro Hlen.
  unfold one_hot_circuit.
  unfold at_least_k_circuit, at_most_k_circuit, gate.
  unfold at_least_k_weights, at_least_k_bias.
  unfold at_most_k_weights, at_most_k_bias.
  destruct xs as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|x6 [|x7 [|]]]]]]]]];
  try discriminate.
  clear Hlen.
  destruct x0, x1, x2, x3, x4, x5, x6, x7;
  simpl; split; intro H; try reflexivity; try discriminate; try lia.
Qed.

(** * Network Architecture *)

Definition one_hot_num_params : nat := 18.
Definition one_hot_num_neurons : nat := 2.
Definition one_hot_depth : nat := 2.
