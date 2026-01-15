(** * Pattern.AllZeros: All-Zeros Detector

    Fires when all 8 input bits are false.
    Equivalent to NOT(OneOutOfEight) or NOR of all inputs.
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

(** All-zeros: fire when no input is true.
    Weights all -1, bias 0: fires when sum of inputs = 0. *)
Definition all_zeros_weights : list Z := [-1; -1; -1; -1; -1; -1; -1; -1].
Definition all_zeros_bias : Z := 0.

Definition all_zeros_circuit (xs : list bool) : bool :=
  gate all_zeros_weights all_zeros_bias xs.

(** * Specification *)

Definition all_zeros_spec (xs : list bool) : bool :=
  Nat.eqb (hamming_weight xs) 0.

(** * Verification *)

Theorem all_zeros_correct
  : forall x0 x1 x2 x3 x4 x5 x6 x7,
    all_zeros_circuit [x0; x1; x2; x3; x4; x5; x6; x7] =
    negb (orb x0 (orb x1 (orb x2 (orb x3 (orb x4 (orb x5 (orb x6 x7))))))).
Proof.
  intros.
  unfold all_zeros_circuit, gate, all_zeros_weights, all_zeros_bias.
  destruct x0, x1, x2, x3, x4, x5, x6, x7; vm_compute; reflexivity.
Qed.

Theorem all_zeros_exhaustive
  : verify_all (fun xs =>
      Bool.eqb (all_zeros_circuit xs)
               (Nat.eqb (hamming_weight xs) 0)) = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

(** * Properties *)

Lemma all_zeros_true
  : all_zeros_circuit [false; false; false; false; false; false; false; false] = true.
Proof. vm_compute. reflexivity. Qed.

Lemma all_zeros_one_true
  : all_zeros_circuit [false; false; false; false; false; false; false; true] = false.
Proof. vm_compute. reflexivity. Qed.

Lemma all_zeros_all_true
  : all_zeros_circuit [true; true; true; true; true; true; true; true] = false.
Proof. vm_compute. reflexivity. Qed.

(** * Algebraic Characterization *)

Theorem all_zeros_hamming_weight (xs : list bool)
  : length xs = 8%nat ->
    all_zeros_circuit xs = true <-> hamming_weight xs = 0%nat.
Proof.
  intro Hlen.
  unfold all_zeros_circuit, gate, all_zeros_weights, all_zeros_bias.
  destruct xs as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|x6 [|x7 [|]]]]]]]]];
  try discriminate.
  clear Hlen.
  destruct x0, x1, x2, x3, x4, x5, x6, x7;
  simpl; split; intro H; try reflexivity; try discriminate; try lia.
Qed.

(** * Network Architecture *)

Definition all_zeros_num_params : nat := 9.
Definition all_zeros_num_neurons : nat := 1.
Definition all_zeros_depth : nat := 1.
