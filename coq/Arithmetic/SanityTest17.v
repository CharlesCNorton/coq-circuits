(** * Arithmetic.SanityTest17: Incrementer = RippleCarry(A, 1)

    Sanity Test 17: Verify Incrementer equals RippleCarry with B=1.

    This demonstrates:
    1. Incrementer is a special case of addition
    2. Adding 1 (00000001) increments the value
    3. Implementation reuses verified ripple carry adder
*)

Require Import ZArith.
Require Import Arith.
Require Import List.
Require Import Bool.
Require Import Lia.
Require Import Base.Definitions.
Require Import Base.Tactics.
Require Import Arithmetic.RippleCarry8Bit.
Require Import Arithmetic.Incrementer8Bit.

Import ListNotations.

Open Scope nat_scope.

(** * Sanity Test 17: Incrementer = RippleCarry(A, 00000001) *)

(** Incrementer is defined as ripple carry with B = 1 *)
Theorem sanity_test_17_incrementer_is_add_one
  : forall a7 a6 a5 a4 a3 a2 a1 a0,
    incrementer_8bit a7 a6 a5 a4 a3 a2 a1 a0 =
    ripple_carry_8bit a7 a6 a5 a4 a3 a2 a1 a0
                      false false false false false false false true.
Proof.
  intros.
  unfold incrementer_8bit.
  reflexivity.
Qed.

(** Incrementing 0 gives 1 *)
Theorem sanity_test_17_zero_plus_one
  : incrementer_8bit false false false false false false false false =
    (false, false, false, false, false, false, false, false, true).
Proof.
  apply incrementer_zero_gives_one.
Qed.

(** Incrementing 255 overflows to 0 *)
Theorem sanity_test_17_overflow
  : incrementer_8bit true true true true true true true true =
    (true, false, false, false, false, false, false, false, false).
Proof.
  apply incrementer_max_overflows.
Qed.

(** Incrementing 1 gives 2 *)
Theorem sanity_test_17_one_plus_one
  : incrementer_8bit false false false false false false false true =
    (false, false, false, false, false, false, false, true, false).
Proof.
  reflexivity.
Qed.

(** Incrementing 127 gives 128 *)
Theorem sanity_test_17_half_max
  : incrementer_8bit false true true true true true true true =
    (false, true, false, false, false, false, false, false, false).
Proof.
  reflexivity.
Qed.

(** Ripple carry with 1 matches incrementer for specific values *)
Theorem sanity_test_17_examples
  : ripple_carry_8bit false false false false false false false false
                      false false false false false false false true =
    (false, false, false, false, false, false, false, false, true) /\
    ripple_carry_8bit false false false false false false false true
                      false false false false false false false true =
    (false, false, false, false, false, false, false, true, false) /\
    ripple_carry_8bit true true true true true true true true
                      false false false false false false false true =
    (true, false, false, false, false, false, false, false, false).
Proof.
  repeat split; reflexivity.
Qed.

(** SANITY TEST 17 PASSES: Incrementer = RippleCarry(A, 1) *)
Theorem sanity_test_17_complete
  : forall a7 a6 a5 a4 a3 a2 a1 a0,
    incrementer_8bit a7 a6 a5 a4 a3 a2 a1 a0 =
    ripple_carry_8bit a7 a6 a5 a4 a3 a2 a1 a0
                      false false false false false false false true.
Proof.
  apply sanity_test_17_incrementer_is_add_one.
Qed.
