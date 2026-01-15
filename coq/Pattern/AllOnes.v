(** * Pattern.AllOnes: All-Ones Detector

    Fires when all 8 input bits are true.
    Equivalent to AllOutOfEight (8-of-8 threshold).
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

Definition all_ones_weights : list Z := ones8.
Definition all_ones_bias : Z := -8.

Definition all_ones_circuit (xs : list bool) : bool :=
  gate all_ones_weights all_ones_bias xs.

(** * Specification *)

Definition all_ones_spec (xs : list bool) : bool :=
  Nat.eqb (hamming_weight xs) (length xs).

(** * Verification *)

Theorem all_ones_correct
  : forall x0 x1 x2 x3 x4 x5 x6 x7,
    all_ones_circuit [x0; x1; x2; x3; x4; x5; x6; x7] =
    andb x0 (andb x1 (andb x2 (andb x3 (andb x4 (andb x5 (andb x6 x7)))))).
Proof.
  intros.
  unfold all_ones_circuit, gate, all_ones_weights, all_ones_bias.
  destruct x0, x1, x2, x3, x4, x5, x6, x7; vm_compute; reflexivity.
Qed.

Theorem all_ones_exhaustive
  : verify_all (fun xs =>
      Bool.eqb (all_ones_circuit xs)
               (andb (nth 0 xs false)
                (andb (nth 1 xs false)
                 (andb (nth 2 xs false)
                  (andb (nth 3 xs false)
                   (andb (nth 4 xs false)
                    (andb (nth 5 xs false)
                     (andb (nth 6 xs false) (nth 7 xs false))))))))) = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

(** * Properties *)

Lemma all_ones_true
  : all_ones_circuit [true; true; true; true; true; true; true; true] = true.
Proof. vm_compute. reflexivity. Qed.

Lemma all_ones_one_false
  : all_ones_circuit [true; true; true; true; true; true; true; false] = false.
Proof. vm_compute. reflexivity. Qed.

Lemma all_ones_all_false
  : all_ones_circuit [false; false; false; false; false; false; false; false] = false.
Proof. vm_compute. reflexivity. Qed.

(** * Algebraic Characterization *)

Theorem all_ones_hamming_weight (xs : list bool)
  : length xs = 8%nat ->
    all_ones_circuit xs = true <-> hamming_weight xs = 8%nat.
Proof.
  intro Hlen.
  unfold all_ones_circuit, gate, all_ones_weights, all_ones_bias.
  destruct xs as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|x6 [|x7 [|]]]]]]]]];
  try discriminate.
  clear Hlen.
  destruct x0, x1, x2, x3, x4, x5, x6, x7;
  simpl; split; intro H; try reflexivity; try discriminate; try lia.
Qed.

(** * Network Architecture *)

Definition all_ones_num_params : nat := 9.
Definition all_ones_num_neurons : nat := 1.
Definition all_ones_depth : nat := 1.
