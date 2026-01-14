(** * Arithmetic.RippleCarry2Bit: 2-Bit Ripple Carry Adder

    Adds two 2-bit numbers using two full adders chained together.
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

(** 2-bit ripple carry adder: chains two full adders *)
Definition ripple_carry_2bit (a1 a0 b1 b0 : bool) : bool * bool * bool :=
  let '(sum0, carry0) := full_adder a0 b0 false in
  let '(sum1, carry1) := full_adder a1 b1 carry0 in
  (carry1, sum1, sum0).

(** * Specification *)

(** Convert 2-bit bool list to nat *)
Definition bits2_to_nat (b1 b0 : bool) : nat :=
  (if b1 then 2 else 0) + (if b0 then 1 else 0).

(** Convert 3-bit result to nat *)
Definition bits3_to_nat (b2 b1 b0 : bool) : nat :=
  (if b2 then 4 else 0) + (if b1 then 2 else 0) + (if b0 then 1 else 0).

(** Specification: addition should match arithmetic *)
Definition ripple_carry_2bit_spec (a1 a0 b1 b0 : bool) : bool * bool * bool :=
  let a_val := bits2_to_nat a1 a0 in
  let b_val := bits2_to_nat b1 b0 in
  let sum := a_val + b_val in
  let c := Nat.leb 4 sum in
  let s1 := Nat.odd (sum / 2) in
  let s0 := Nat.odd sum in
  (c, s1, s0).

(** * Verification *)

Theorem ripple_carry_2bit_correct
  : forall a1 a0 b1 b0,
    ripple_carry_2bit a1 a0 b1 b0 = ripple_carry_2bit_spec a1 a0 b1 b0.
Proof.
  intros.
  unfold ripple_carry_2bit, ripple_carry_2bit_spec.
  unfold full_adder, full_adder_sum, full_adder_carry.
  destruct a1, a0, b1, b0; vm_compute; reflexivity.
Qed.

(** * Properties *)

(** 2-bit addition commutative *)
Lemma ripple_carry_2bit_comm
  : forall a1 a0 b1 b0,
    ripple_carry_2bit a1 a0 b1 b0 = ripple_carry_2bit b1 b0 a1 a0.
Proof.
  intros.
  destruct a1, a0, b1, b0; reflexivity.
Qed.

(** Adding zero preserves value *)
Lemma ripple_carry_2bit_zero
  : forall a1 a0,
    ripple_carry_2bit a1 a0 false false = (false, a1, a0).
Proof.
  intros.
  destruct a1, a0; reflexivity.
Qed.

(** * Network Architecture *)

(** Total neurons: 8 (2 full adders × 4 neurons each) *)
Definition ripple_carry_2bit_num_neurons : nat := 8.

(** Total parameters: 24 (2 full adders × 12 params each) *)
Definition ripple_carry_2bit_num_params : nat := 24.

(** Network depth: 2 (chained full adders) *)
Definition ripple_carry_2bit_depth : nat := 2.
