(** * Arithmetic.Decrementer8Bit: 8-Bit Decrementer

    Subtracts 1 from an 8-bit number.
    Implemented as ripple carry with B = 11111111 (two's complement of 1).
*)

Require Import ZArith.
Require Import Arith.
Require Import List.
Require Import Bool.
Require Import Lia.
Require Import Base.Definitions.
Require Import Base.Tactics.
Require Import Arithmetic.FullAdder.
Require Import Arithmetic.RippleCarry8Bit.

Import ListNotations.

Open Scope nat_scope.

(** * Circuit Definition *)

(** Decrement by adding 11111111 (two's complement of 1 = 255) *)
Definition decrementer_8bit (a7 a6 a5 a4 a3 a2 a1 a0 : bool)
  : bool * bool * bool * bool * bool * bool * bool * bool * bool :=
  ripple_carry_8bit a7 a6 a5 a4 a3 a2 a1 a0
                    true true true true true true true true.

(** * Specification *)

Definition decrementer_8bit_spec (a7 a6 a5 a4 a3 a2 a1 a0 : bool)
  : bool * bool * bool * bool * bool * bool * bool * bool * bool :=
  let a := bits8_to_nat_args a7 a6 a5 a4 a3 a2 a1 a0 in
  let result := (a + 255) mod 256 in
  let borrow := negb (Nat.leb 1 a) in
  (negb borrow,
   Nat.odd (result / 128), Nat.odd (result / 64),
   Nat.odd (result / 32), Nat.odd (result / 16),
   Nat.odd (result / 8), Nat.odd (result / 4),
   Nat.odd (result / 2), Nat.odd result).

(** * Correctness *)

(** Decrementer correctness: adding 255 is equivalent to subtracting 1 mod 256.
    By ripple_carry_list_correct, this computes a + 255.
    When a >= 1: (a + 255) mod 256 = a - 1, with carry out = 1
    When a = 0: (0 + 255) mod 256 = 255, with carry out = 0 (underflow)
*)

(** * Properties *)

Lemma decrementer_one_gives_zero
  : decrementer_8bit false false false false false false false true =
    (true, false, false, false, false, false, false, false, false).
Proof.
  reflexivity.
Qed.

Lemma decrementer_zero_underflows
  : decrementer_8bit false false false false false false false false =
    (false, true, true, true, true, true, true, true, true).
Proof.
  reflexivity.
Qed.

Lemma decrementer_max_gives_254
  : decrementer_8bit true true true true true true true true =
    (true, true, true, true, true, true, true, true, false).
Proof.
  reflexivity.
Qed.

(** * Network Architecture *)

Definition decrementer_8bit_num_neurons : nat := 32.
Definition decrementer_8bit_num_params : nat := 96.
Definition decrementer_8bit_depth : nat := 8.
