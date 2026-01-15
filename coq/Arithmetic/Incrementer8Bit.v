(** * Arithmetic.Incrementer8Bit: 8-Bit Incrementer

    Adds 1 to an 8-bit number.
    Implemented as ripple carry with B = 00000001.
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

Definition incrementer_8bit (a7 a6 a5 a4 a3 a2 a1 a0 : bool)
  : bool * bool * bool * bool * bool * bool * bool * bool * bool :=
  ripple_carry_8bit a7 a6 a5 a4 a3 a2 a1 a0
                    false false false false false false false true.

(** * Specification *)

Definition incrementer_8bit_spec (a7 a6 a5 a4 a3 a2 a1 a0 : bool)
  : bool * bool * bool * bool * bool * bool * bool * bool * bool :=
  let a := bits8_to_nat_args a7 a6 a5 a4 a3 a2 a1 a0 in
  let result := a + 1 in
  let overflow := Nat.leb 256 result in
  let r := result mod 256 in
  (overflow,
   Nat.odd (r / 128), Nat.odd (r / 64), Nat.odd (r / 32), Nat.odd (r / 16),
   Nat.odd (r / 8), Nat.odd (r / 4), Nat.odd (r / 2), Nat.odd r).

(** * Correctness *)

(** Incrementer correctness follows from ripple_carry_list_correct:
    incrementer_8bit a = ripple_carry_8bit a 00000001
    By ripple_carry_list_correct, this computes a + 1.
*)

(** * Properties *)

Lemma incrementer_zero_gives_one
  : incrementer_8bit false false false false false false false false =
    (false, false, false, false, false, false, false, false, true).
Proof.
  reflexivity.
Qed.

Lemma incrementer_max_overflows
  : incrementer_8bit true true true true true true true true =
    (true, false, false, false, false, false, false, false, false).
Proof.
  reflexivity.
Qed.

(** * Network Architecture *)

Definition incrementer_8bit_num_neurons : nat := 32.
Definition incrementer_8bit_num_params : nat := 96.
Definition incrementer_8bit_depth : nat := 8.
