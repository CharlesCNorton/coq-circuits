(** * Boolean.SanityTest5: NOR Composition Builds OR

    Sanity Test 5: Verify that NOR(NOR(x,y), NOR(x,y)) = OR(x,y)

    This demonstrates:
    1. NOR is functionally complete
    2. Circuit composition preserves correctness
    3. Our threshold implementations are consistent
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Base.Definitions.
Require Import Base.Tactics.
Require Import Boolean.OR.
Require Import Boolean.NOR.

Import ListNotations.

Open Scope Z_scope.

(** * Composition: OR from NOR *)

(** OR(x,y) = NOR(NOR(x,y), NOR(x,y)) *)
Definition or_from_nor (x y : bool) : bool :=
  nor_circuit (nor_circuit x y) (nor_circuit x y).

(** * Sanity Test 5: NOR composition equals OR *)

Theorem sanity_test_5_nor_composition
  : forall x y, or_from_nor x y = or_circuit x y.
Proof.
  intros.
  unfold or_from_nor, or_circuit, nor_circuit, gate.
  destruct x, y; vm_compute; reflexivity.
Qed.

(** Alternative formulation using orb *)
Theorem sanity_test_5_spec
  : forall x y, or_from_nor x y = orb x y.
Proof.
  intros.
  rewrite sanity_test_5_nor_composition.
  apply or_correct.
Qed.

(** * Additional NOR Compositions *)

(** NOT from NOR: NOT(x) = NOR(x, x) *)
Definition not_from_nor (x : bool) : bool :=
  nor_circuit x x.

Theorem not_from_nor_correct
  : forall x, not_from_nor x = negb x.
Proof.
  intros.
  unfold not_from_nor, nor_circuit, gate.
  destruct x; vm_compute; reflexivity.
Qed.

(** AND from NOR: AND(x,y) = NOR(NOR(x,x), NOR(y,y)) *)
Definition and_from_nor (x y : bool) : bool :=
  nor_circuit (nor_circuit x x) (nor_circuit y y).

Theorem and_from_nor_correct
  : forall x y, and_from_nor x y = andb x y.
Proof.
  intros.
  unfold and_from_nor, nor_circuit, gate.
  destruct x, y; vm_compute; reflexivity.
Qed.

(** * Functional Completeness Demonstration *)

Theorem nor_builds_not
  : forall x, nor_circuit x x = negb x.
Proof.
  intros.
  unfold nor_circuit, gate.
  destruct x; vm_compute; reflexivity.
Qed.

Theorem nor_builds_or
  : forall x y, nor_circuit (nor_circuit x y) (nor_circuit x y) = orb x y.
Proof.
  intros.
  apply sanity_test_5_spec.
Qed.

Theorem nor_builds_and
  : forall x y, nor_circuit (nor_circuit x x) (nor_circuit y y) = andb x y.
Proof.
  intros.
  apply and_from_nor_correct.
Qed.

(** SANITY TEST 5 PASSES: NOR is functionally complete *)
Theorem sanity_test_5_complete
  : forall x y,
    or_from_nor x y = or_circuit x y /\
    or_from_nor x y = orb x y.
Proof.
  intros.
  split.
  - apply sanity_test_5_nor_composition.
  - apply sanity_test_5_spec.
Qed.
