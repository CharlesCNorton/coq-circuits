(** * Boolean.SanityTest1: NAND Composition Builds AND

    Sanity Test 1: Verify that NAND(NAND(x,y), NAND(x,y)) = AND(x,y)

    This demonstrates:
    1. NAND is functionally complete
    2. Circuit composition preserves correctness
    3. Our threshold implementations are consistent
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Base.Definitions.
Require Import Base.Tactics.
Require Import Boolean.AND.
Require Import Boolean.NAND.

Import ListNotations.

Open Scope Z_scope.

(** * Composition: AND from NAND *)

(** AND(x,y) = NAND(NAND(x,y), NAND(x,y)) *)
Definition and_from_nand (x y : bool) : bool :=
  nand_circuit (nand_circuit x y) (nand_circuit x y).

(** * Sanity Test 1: NAND composition equals AND *)

Theorem sanity_test_1_nand_composition
  : forall x y, and_from_nand x y = and_circuit x y.
Proof.
  intros.
  unfold and_from_nand, and_circuit, nand_circuit, gate.
  destruct x, y; vm_compute; reflexivity.
Qed.

(** Alternative formulation using andb *)
Theorem sanity_test_1_spec
  : forall x y, and_from_nand x y = andb x y.
Proof.
  intros.
  rewrite sanity_test_1_nand_composition.
  apply and_correct.
Qed.

(** * Additional NAND Compositions *)

(** NOT from NAND: NOT(x) = NAND(x, x) *)
Definition not_from_nand (x : bool) : bool :=
  nand_circuit x x.

Theorem not_from_nand_correct
  : forall x, not_from_nand x = negb x.
Proof.
  intros.
  unfold not_from_nand, nand_circuit, gate.
  destruct x; vm_compute; reflexivity.
Qed.

(** OR from NAND: OR(x,y) = NAND(NAND(x,x), NAND(y,y)) *)
Definition or_from_nand (x y : bool) : bool :=
  nand_circuit (nand_circuit x x) (nand_circuit y y).

Theorem or_from_nand_correct
  : forall x y, or_from_nand x y = orb x y.
Proof.
  intros.
  unfold or_from_nand, nand_circuit, gate.
  destruct x, y; vm_compute; reflexivity.
Qed.

(** * Functional Completeness Demonstration *)

(** NAND can build all basic gates *)
Theorem nand_builds_not
  : forall x, nand_circuit x x = negb x.
Proof.
  intros.
  unfold nand_circuit, gate.
  destruct x; vm_compute; reflexivity.
Qed.

Theorem nand_builds_and
  : forall x y, nand_circuit (nand_circuit x y) (nand_circuit x y) = andb x y.
Proof.
  intros.
  apply sanity_test_1_spec.
Qed.

Theorem nand_builds_or
  : forall x y, nand_circuit (nand_circuit x x) (nand_circuit y y) = orb x y.
Proof.
  intros.
  apply or_from_nand_correct.
Qed.

(** SANITY TEST 1 PASSES: NAND ∘ NAND = AND ✓ *)
Theorem sanity_test_1_complete
  : forall x y,
    and_from_nand x y = and_circuit x y /\
    and_from_nand x y = andb x y.
Proof.
  intros.
  split.
  - apply sanity_test_1_nand_composition.
  - apply sanity_test_1_spec.
Qed.
