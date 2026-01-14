(** * Threshold.Minority: Minority Gate

    Formally verified minority gate for 8-bit inputs.
    Fires when less than half (≤3) of inputs are true.
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

(** Minority gate weights: all negative ones for 8 inputs. *)
Definition minority_weights
  : list Z
  := [-1; -1; -1; -1; -1; -1; -1; -1].

(** Minority gate bias: 3 (fires when HW ≤ 3). *)
Definition minority_bias
  : Z
  := 3.

(** Minority circuit: fires when HW(xs) <= 3. *)
Definition minority_circuit (xs : list bool)
  : bool
  := gate minority_weights minority_bias xs.

(** * Specification *)

(** Minority holds when at most 3 of 8 inputs are true. *)
Definition minority_spec (xs : list bool)
  : bool
  := Nat.leb (hamming_weight xs) 3.

(** * Verification *)

(** Minority circuit computes minority correctly. *)
Theorem minority_correct
  : forall x0 x1 x2 x3 x4 x5 x6 x7,
    minority_circuit [x0; x1; x2; x3; x4; x5; x6; x7] =
    minority_spec [x0; x1; x2; x3; x4; x5; x6; x7].
Proof.
  intros.
  unfold minority_circuit, minority_spec, gate.
  unfold minority_weights, minority_bias.
  destruct x0, x1, x2, x3, x4, x5, x6, x7; vm_compute; reflexivity.
Qed.

(** Exhaustive verification via computation. *)
Theorem minority_exhaustive_verified
  : verify_all (fun xs => Bool.eqb (minority_circuit xs) (minority_spec xs)) = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

(** * Algebraic Characterization *)

(** Minority is characterized by hamming weight. *)
Theorem minority_hamming_weight (xs : list bool)
  : length xs = 8%nat ->
    minority_circuit xs = true <-> (hamming_weight xs <= 3)%nat.
Proof.
  intro Hlen.
  unfold minority_circuit, gate, minority_weights, minority_bias.
  destruct xs as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|x6 [|x7 [|]]]]]]]]]; try discriminate.
  clear Hlen.
  destruct x0, x1, x2, x3, x4, x5, x6, x7; simpl; split; intro H; try reflexivity; try discriminate; try lia.
Qed.

(** * Length Safety *)

(** Minority weights have length 8 *)
Lemma minority_weights_length
  : length minority_weights = 8%nat.
Proof. reflexivity. Qed.

(** Minority requires exactly 8 inputs *)
Theorem minority_length_requirement (xs : list bool)
  : length xs = 8%nat ->
    gate_length_ok minority_weights xs.
Proof.
  intro Hlen.
  unfold gate_length_ok.
  rewrite minority_weights_length.
  symmetry.
  exact Hlen.
Qed.

(** * Properties *)

(** All false gives minority. *)
Lemma minority_all_false
  : minority_circuit [false; false; false; false; false; false; false; false] = true.
Proof. vm_compute. reflexivity. Qed.

(** All true gives no minority. *)
Lemma minority_all_true
  : minority_circuit [true; true; true; true; true; true; true; true] = false.
Proof. vm_compute. reflexivity. Qed.

(** Exactly 3 true gives minority. *)
Lemma minority_exactly_three_true
  : minority_circuit [true; true; true; false; false; false; false; false] = true.
Proof. vm_compute. reflexivity. Qed.

(** Exactly 4 true gives no minority. *)
Lemma minority_exactly_four_false
  : minority_circuit [true; true; true; true; false; false; false; false] = false.
Proof. vm_compute. reflexivity. Qed.

(** * Network Architecture *)

(** Total parameters: 9 (8 weights + 1 bias). *)
Definition minority_num_params : nat := 9.

(** Single neuron. *)
Definition minority_num_neurons : nat := 1.

(** Network depth: 1 layer. *)
Definition minority_depth : nat := 1.
