(** * Arithmetic.RippleCarry4Bit: 4-Bit Ripple Carry Adder

    Adds two 4-bit numbers using four full adders chained together.
*)

Require Import ZArith.
Require Import Arith.
Require Import List.
Require Import Bool.
Require Import Base.Definitions.
Require Import Base.Tactics.
Require Import Base.Composition.
Require Import Arithmetic.FullAdder.

Import ListNotations.

Open Scope nat_scope.

(** * Circuit Definition *)

(** 4-bit ripple carry adder: chains four full adders *)
Definition ripple_carry_4bit (a3 a2 a1 a0 b3 b2 b1 b0 : bool)
  : bool * bool * bool * bool * bool :=
  let '(sum0, carry0) := full_adder a0 b0 false in
  let '(sum1, carry1) := full_adder a1 b1 carry0 in
  let '(sum2, carry2) := full_adder a2 b2 carry1 in
  let '(sum3, carry3) := full_adder a3 b3 carry2 in
  (carry3, sum3, sum2, sum1, sum0).

(** * Specification *)

(** Convert 4-bit bool to nat *)
Definition bits4_to_nat (b3 b2 b1 b0 : bool) : nat :=
  (if b3 then 8 else 0) + (if b2 then 4 else 0) +
  (if b1 then 2 else 0) + (if b0 then 1 else 0).

(** Convert 5-bit result to nat *)
Definition bits5_to_nat (b4 b3 b2 b1 b0 : bool) : nat :=
  (if b4 then 16 else 0) + (if b3 then 8 else 0) +
  (if b2 then 4 else 0) + (if b1 then 2 else 0) + (if b0 then 1 else 0).

(** Specification: addition should match arithmetic *)
Definition ripple_carry_4bit_spec (a3 a2 a1 a0 b3 b2 b1 b0 : bool)
  : bool * bool * bool * bool * bool :=
  let a_val := bits4_to_nat a3 a2 a1 a0 in
  let b_val := bits4_to_nat b3 b2 b1 b0 in
  let sum := a_val + b_val in
  let c := Nat.leb 16 sum in
  let s3 := Nat.odd (sum / 8) in
  let s2 := Nat.odd (sum / 4) in
  let s1 := Nat.odd (sum / 2) in
  let s0 := Nat.odd sum in
  (c, s3, s2, s1, s0).

(** * Verification *)

Theorem ripple_carry_4bit_correct
  : forall a3 a2 a1 a0 b3 b2 b1 b0,
    ripple_carry_4bit a3 a2 a1 a0 b3 b2 b1 b0 =
    ripple_carry_4bit_spec a3 a2 a1 a0 b3 b2 b1 b0.
Proof.
  intros.
  unfold ripple_carry_4bit, ripple_carry_4bit_spec.
  unfold full_adder, full_adder_sum, full_adder_carry.
  destruct a3, a2, a1, a0, b3, b2, b1, b0; vm_compute; reflexivity.
Qed.

(** * Properties *)

(** 4-bit addition commutative *)
Lemma ripple_carry_4bit_comm
  : forall a3 a2 a1 a0 b3 b2 b1 b0,
    ripple_carry_4bit a3 a2 a1 a0 b3 b2 b1 b0 =
    ripple_carry_4bit b3 b2 b1 b0 a3 a2 a1 a0.
Proof.
  intros.
  destruct a3, a2, a1, a0, b3, b2, b1, b0; reflexivity.
Qed.

(** Adding zero preserves value *)
Lemma ripple_carry_4bit_zero
  : forall a3 a2 a1 a0,
    ripple_carry_4bit a3 a2 a1 a0 false false false false =
    (false, a3, a2, a1, a0).
Proof.
  intros.
  destruct a3, a2, a1, a0; reflexivity.
Qed.

(** * Network Architecture *)

Definition ripple_carry_4bit_num_neurons : nat := 16.
Definition ripple_carry_4bit_num_params : nat := 48.
Definition ripple_carry_4bit_depth : nat := 4.
