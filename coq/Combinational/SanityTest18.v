(** * Combinational.SanityTest18: Mux2to1 Composition

    Sanity Test 18: Verify Mux2to1 = OR(AND(NOT(s),a), AND(s,b)).

    This demonstrates:
    1. Multiplexer is built from basic gates
    2. Selection logic uses NOT, AND, OR composition
    3. s=0 selects a, s=1 selects b
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Base.Definitions.
Require Import Base.Tactics.
Require Import Combinational.Multiplexer2to1.
Require Import Boolean.AND.
Require Import Boolean.OR.
Require Import Boolean.NOT.

Import ListNotations.

Open Scope Z_scope.

(** * Sanity Test 18: Mux2to1 = OR(AND(NOT(s),a), AND(s,b)) *)

(** Mux is composed from basic gates *)
Theorem sanity_test_18_mux_composition
  : forall s a b,
    mux2to1 s a b =
    or_circuit (and_circuit (not_circuit s) a)
               (and_circuit s b).
Proof.
  intros.
  unfold mux2to1.
  reflexivity.
Qed.

(** Mux matches if-then-else spec *)
Theorem sanity_test_18_mux_spec
  : forall s a b, mux2to1 s a b = mux2to1_spec s a b.
Proof.
  apply mux2to1_correct.
Qed.

(** s=false selects a *)
Theorem sanity_test_18_select_a
  : forall a b, mux2to1 false a b = a.
Proof.
  apply mux2to1_select_a.
Qed.

(** s=true selects b *)
Theorem sanity_test_18_select_b
  : forall a b, mux2to1 true a b = b.
Proof.
  apply mux2to1_select_b.
Qed.

(** Same inputs gives that input regardless of select *)
Theorem sanity_test_18_same_inputs
  : forall s x, mux2to1 s x x = x.
Proof.
  apply mux2to1_same_inputs.
Qed.

(** Gate-level verification *)
Theorem sanity_test_18_gate_expansion
  : forall s a b,
    let not_s := not_circuit s in
    let path_a := and_circuit not_s a in
    let path_b := and_circuit s b in
    mux2to1 s a b = or_circuit path_a path_b.
Proof.
  intros.
  reflexivity.
Qed.

(** Exhaustive truth table *)
Theorem sanity_test_18_truth_table
  : mux2to1 false false false = false /\
    mux2to1 false false true = false /\
    mux2to1 false true false = true /\
    mux2to1 false true true = true /\
    mux2to1 true false false = false /\
    mux2to1 true false true = true /\
    mux2to1 true true false = false /\
    mux2to1 true true true = true.
Proof.
  apply mux2to1_exhaustive.
Qed.

(** SANITY TEST 18 PASSES: Mux2to1 = OR(AND(NOT(s),a), AND(s,b)) *)
Theorem sanity_test_18_complete
  : forall s a b,
    mux2to1 s a b = or_circuit (and_circuit (not_circuit s) a) (and_circuit s b) /\
    mux2to1 s a b = (if s then b else a).
Proof.
  intros.
  split.
  - apply sanity_test_18_mux_composition.
  - apply sanity_test_18_mux_spec.
Qed.
