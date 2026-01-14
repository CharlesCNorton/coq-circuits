(** * Boolean.NOT: NOT Gate

    Formally verified NOT gate (single-input negation).
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Base.Definitions.
Require Import Base.Tactics.
Require Import Base.Verification.

Import ListNotations.

Open Scope Z_scope.

(** * Circuit Definition *)

(** NOT gate weights: single weight of -1. *)
Definition not_weights
  : list Z
  := [-1].

(** NOT gate bias: 0. *)
Definition not_bias
  : Z
  := 0.

(** NOT gate: single threshold neuron computing negation.
    Input [x] produces output NOT(x). *)
Definition not_circuit (x : bool)
  : bool
  := gate not_weights not_bias [x].

(** Extend to 8-bit input (operates on first bit only). *)
Definition not_8bit (xs : list bool)
  : bool
  :=
  match xs with
  | x :: _ => not_circuit x
  | [] => false
  end.

(** * Specification *)

Definition not_spec (x : bool)
  : bool
  := negb x.

(** * Verification *)

(** NOT circuit computes negation correctly. *)
Theorem not_correct
  : forall x, not_circuit x = not_spec x.
Proof.
  intro x.
  destruct x; reflexivity.
Qed.

(** Exhaustive verification on all single-bit inputs. *)
Theorem not_exhaustive
  : not_circuit false = true /\ not_circuit true = false.
Proof.
  split; reflexivity.
Qed.

(** 8-bit version correct. *)
Theorem not_8bit_correct
  : forall x0 x1 x2 x3 x4 x5 x6 x7,
    not_8bit [x0; x1; x2; x3; x4; x5; x6; x7] = negb x0.
Proof.
  intros.
  simpl.
  apply not_correct.
Qed.

(** * Properties *)

(** NOT is involutive. *)
Lemma not_involutive
  : forall x, not_circuit (not_circuit x) = x.
Proof.
  intro x.
  destruct x; reflexivity.
Qed.

(** NOT maps true to false. *)
Lemma not_true
  : not_circuit true = false.
Proof. reflexivity. Qed.

(** NOT maps false to true. *)
Lemma not_false
  : not_circuit false = true.
Proof. reflexivity. Qed.

(** * Length Safety *)

(** NOT weights have length 1 *)
Lemma not_weights_length
  : length not_weights = 1%nat.
Proof. reflexivity. Qed.

(** NOT requires exactly 1 input *)
Theorem not_length_requirement (x : bool)
  : gate_length_ok not_weights [x].
Proof.
  unfold gate_length_ok.
  rewrite not_weights_length.
  reflexivity.
Qed.

(** Length-safe NOT circuit *)
Definition not_circuit_safe (x : bool)
  : bool
  := gate_safe not_weights not_bias [x] (not_length_requirement x).

(** Safe version equivalent to unsafe version *)
Theorem not_safe_equiv (x : bool)
  : not_circuit_safe x = not_circuit x.
Proof.
  unfold not_circuit_safe, gate_safe.
  reflexivity.
Qed.

(** * Network Architecture *)

(** Total parameters: 2 (1 weight + 1 bias). *)
Definition not_num_params : nat := 2.
