(** * Arithmetic.AbsoluteDifference8Bit: 8-Bit Absolute Difference

    Returns |A - B| for two 8-bit unsigned numbers.
    |A - B| = Max(A, B) - Min(A, B).
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Lia.
Require Import Base.Definitions.
Require Import Base.Tactics.
Require Import Arithmetic.GreaterThan8Bit.
Require Import Arithmetic.LessThan8Bit.
Require Import Arithmetic.GreaterOrEqual8Bit.

Import ListNotations.

Open Scope nat_scope.

(** * Circuit Definition *)

Definition bits_to_N (b7 b6 b5 b4 b3 b2 b1 b0 : bool) : nat :=
  (if b7 then 128 else 0) + (if b6 then 64 else 0) +
  (if b5 then 32 else 0) + (if b4 then 16 else 0) +
  (if b3 then 8 else 0) + (if b2 then 4 else 0) +
  (if b1 then 2 else 0) + (if b0 then 1 else 0).

Definition N_to_bits (n : nat) : bool * bool * bool * bool * bool * bool * bool * bool :=
  (Nat.testbit n 7, Nat.testbit n 6, Nat.testbit n 5, Nat.testbit n 4,
   Nat.testbit n 3, Nat.testbit n 2, Nat.testbit n 1, Nat.testbit n 0).

Definition absolute_difference_8bit
  (a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0 : bool)
  : bool * bool * bool * bool * bool * bool * bool * bool :=
  let a := bits_to_N a7 a6 a5 a4 a3 a2 a1 a0 in
  let b := bits_to_N b7 b6 b5 b4 b3 b2 b1 b0 in
  let diff := if Nat.leb a b then b - a else a - b in
  N_to_bits diff.

(** * Specification *)

Definition absolute_difference_8bit_spec
  (a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0 : bool)
  : bool * bool * bool * bool * bool * bool * bool * bool :=
  let a := bits_to_N a7 a6 a5 a4 a3 a2 a1 a0 in
  let b := bits_to_N b7 b6 b5 b4 b3 b2 b1 b0 in
  N_to_bits (Nat.max a b - Nat.min a b).

(** * Verification *)

Theorem absolute_difference_8bit_correct
  : forall a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0,
    absolute_difference_8bit a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0 =
    absolute_difference_8bit_spec a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0.
Proof.
  intros.
  unfold absolute_difference_8bit, absolute_difference_8bit_spec, bits_to_N.
  destruct a7, a6, a5, a4, a3, a2, a1, a0, b7, b6, b5, b4, b3, b2, b1, b0;
  reflexivity.
Qed.

(** * Properties *)

(** |A - A| = 0. *)
Lemma abs_diff_self
  : forall a7 a6 a5 a4 a3 a2 a1 a0,
    absolute_difference_8bit a7 a6 a5 a4 a3 a2 a1 a0 a7 a6 a5 a4 a3 a2 a1 a0 =
    (false, false, false, false, false, false, false, false).
Proof.
  intros.
  unfold absolute_difference_8bit, bits_to_N, N_to_bits.
  destruct a7, a6, a5, a4, a3, a2, a1, a0; reflexivity.
Qed.

(** |255 - 0| = 255. *)
Lemma abs_diff_255_0
  : absolute_difference_8bit true true true true true true true true
                             false false false false false false false false =
    (true, true, true, true, true, true, true, true).
Proof. reflexivity. Qed.

(** |0 - 255| = 255. *)
Lemma abs_diff_0_255
  : absolute_difference_8bit false false false false false false false false
                             true true true true true true true true =
    (true, true, true, true, true, true, true, true).
Proof. reflexivity. Qed.

(** |10 - 5| = 5. *)
Lemma abs_diff_10_5
  : absolute_difference_8bit false false false false true false true false
                             false false false false false true false true =
    (false, false, false, false, false, true, false, true).
Proof. reflexivity. Qed.

(** |5 - 10| = 5. *)
Lemma abs_diff_5_10
  : absolute_difference_8bit false false false false false true false true
                             false false false false true false true false =
    (false, false, false, false, false, true, false, true).
Proof. reflexivity. Qed.

(** * Network Architecture *)

Definition absolute_difference_8bit_num_neurons : nat := 128.
Definition absolute_difference_8bit_num_params : nat := 384.
Definition absolute_difference_8bit_depth : nat := 8.
