(** * Arithmetic.SanityTest13: Equality8Bit = AND(XNOR...)

    Sanity Test 13: Verify Equality is bitwise XNOR combined with AND.

    This demonstrates:
    1. Equality requires all bits to match
    2. XNOR tests bit equality
    3. AND combines all bit comparisons
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Base.Definitions.
Require Import Base.Tactics.
Require Import Arithmetic.Equality8Bit.
Require Import Boolean.XNOR.

Import ListNotations.

Open Scope Z_scope.

(** * Sanity Test 13: Equality = AND(XNOR(a_i, b_i)...) *)

(** Equality is conjunction of bitwise XNORs *)
Theorem sanity_test_13_equality_is_xnor_and
  : forall a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0,
    equality_8bit a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0 =
    andb (xnor_circuit a7 b7)
    (andb (xnor_circuit a6 b6)
    (andb (xnor_circuit a5 b5)
    (andb (xnor_circuit a4 b4)
    (andb (xnor_circuit a3 b3)
    (andb (xnor_circuit a2 b2)
    (andb (xnor_circuit a1 b1)
          (xnor_circuit a0 b0))))))).
Proof.
  intros.
  unfold equality_8bit, eq_bit.
  reflexivity.
Qed.

(** XNOR gives true iff bits are equal *)
Theorem sanity_test_13_xnor_is_eq
  : forall a b, xnor_circuit a b = Bool.eqb a b.
Proof.
  intros.
  destruct a, b; reflexivity.
Qed.

(** Equality is reflexive *)
Theorem sanity_test_13_reflexive
  : forall a7 a6 a5 a4 a3 a2 a1 a0,
    equality_8bit a7 a6 a5 a4 a3 a2 a1 a0 a7 a6 a5 a4 a3 a2 a1 a0 = true.
Proof.
  apply equality_same.
Qed.

(** Equality is symmetric *)
Theorem sanity_test_13_symmetric
  : forall a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0,
    equality_8bit a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0 =
    equality_8bit b7 b6 b5 b4 b3 b2 b1 b0 a7 a6 a5 a4 a3 a2 a1 a0.
Proof.
  apply equality_symmetric.
Qed.

(** Single bit difference makes inequality *)
Theorem sanity_test_13_single_diff
  : equality_8bit true false false false false false false false
                  false false false false false false false false = false /\
    equality_8bit false false false false false false false false
                  false false false false false false false true = false.
Proof.
  split; reflexivity.
Qed.

(** All zeros equal *)
Theorem sanity_test_13_zeros_equal
  : equality_8bit false false false false false false false false
                  false false false false false false false false = true.
Proof.
  apply equality_zeros.
Qed.

(** All ones equal *)
Theorem sanity_test_13_ones_equal
  : equality_8bit true true true true true true true true
                  true true true true true true true true = true.
Proof.
  apply equality_ones.
Qed.

(** SANITY TEST 13 PASSES: Equality = AND(XNOR...) *)
Theorem sanity_test_13_complete
  : forall a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0,
    equality_8bit a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0 =
    andb (xnor_circuit a7 b7)
    (andb (xnor_circuit a6 b6)
    (andb (xnor_circuit a5 b5)
    (andb (xnor_circuit a4 b4)
    (andb (xnor_circuit a3 b3)
    (andb (xnor_circuit a2 b2)
    (andb (xnor_circuit a1 b1)
          (xnor_circuit a0 b0))))))).
Proof.
  apply sanity_test_13_equality_is_xnor_and.
Qed.
