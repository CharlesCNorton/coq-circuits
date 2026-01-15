(** * Combinational.Multiplexer2to1: 2-to-1 Multiplexer

    Selects one of two inputs based on select signal.
    MUX(s, a, b) = IF s THEN b ELSE a
    Implemented as: OR(AND(NOT(s), a), AND(s, b))
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Base.Definitions.
Require Import Base.Tactics.
Require Import Boolean.AND.
Require Import Boolean.OR.
Require Import Boolean.NOT.

Import ListNotations.

Open Scope Z_scope.

(** * Circuit Definition *)

(** MUX(s, a, b) = (NOT(s) AND a) OR (s AND b) *)
Definition mux2to1 (s a b : bool) : bool :=
  or_circuit (and_circuit (not_circuit s) a)
             (and_circuit s b).

(** * Specification *)

Definition mux2to1_spec (s a b : bool) : bool :=
  if s then b else a.

(** * Verification *)

Theorem mux2to1_correct
  : forall s a b, mux2to1 s a b = mux2to1_spec s a b.
Proof.
  intros.
  unfold mux2to1, mux2to1_spec.
  unfold or_circuit, and_circuit, not_circuit, gate.
  destruct s, a, b; vm_compute; reflexivity.
Qed.

(** * Properties *)

Lemma mux2to1_select_a
  : forall a b, mux2to1 false a b = a.
Proof.
  intros.
  destruct a, b; reflexivity.
Qed.

Lemma mux2to1_select_b
  : forall a b, mux2to1 true a b = b.
Proof.
  intros.
  destruct a, b; reflexivity.
Qed.

Lemma mux2to1_same_inputs
  : forall s x, mux2to1 s x x = x.
Proof.
  intros.
  destruct s, x; reflexivity.
Qed.

(** * Exhaustive Verification *)

Theorem mux2to1_exhaustive
  : mux2to1 false false false = false /\
    mux2to1 false false true = false /\
    mux2to1 false true false = true /\
    mux2to1 false true true = true /\
    mux2to1 true false false = false /\
    mux2to1 true false true = true /\
    mux2to1 true true false = false /\
    mux2to1 true true true = true.
Proof.
  repeat split; reflexivity.
Qed.

(** * Network Architecture *)

(** NOT: 1 neuron, AND: 2 neurons, OR: 1 neuron *)
Definition mux2to1_num_neurons : nat := 4.
Definition mux2to1_num_params : nat := 12.
Definition mux2to1_depth : nat := 2.
