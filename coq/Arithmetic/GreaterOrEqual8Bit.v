(** * Arithmetic.GreaterOrEqual8Bit: 8-Bit Greater Than or Equal Comparator

    Fires when A >= B for two 8-bit unsigned numbers.
    Equivalent to NOT(A < B).
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Base.Definitions.
Require Import Base.Tactics.
Require Import Arithmetic.LessThan8Bit.

Import ListNotations.

Open Scope Z_scope.

(** * Circuit Definition *)

Definition greater_or_equal_8bit
  (a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0 : bool) : bool :=
  negb (less_than_8bit a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0).

(** * Specification *)

Definition bits_to_N (b7 b6 b5 b4 b3 b2 b1 b0 : bool) : nat :=
  (if b7 then 128 else 0) + (if b6 then 64 else 0) +
  (if b5 then 32 else 0) + (if b4 then 16 else 0) +
  (if b3 then 8 else 0) + (if b2 then 4 else 0) +
  (if b1 then 2 else 0) + (if b0 then 1 else 0).

Definition greater_or_equal_8bit_spec
  (a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0 : bool) : bool :=
  Nat.leb (bits_to_N b7 b6 b5 b4 b3 b2 b1 b0)
          (bits_to_N a7 a6 a5 a4 a3 a2 a1 a0).

(** * Verification *)

Theorem greater_or_equal_8bit_correct
  : forall a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0,
    greater_or_equal_8bit a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0 =
    greater_or_equal_8bit_spec a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0.
Proof.
  intros.
  unfold greater_or_equal_8bit, greater_or_equal_8bit_spec.
  unfold less_than_8bit, lt_bit, eq_bit, bits_to_N.
  destruct a7, a6, a5, a4, a3, a2, a1, a0, b7, b6, b5, b4, b3, b2, b1, b0;
  reflexivity.
Qed.

(** * Properties *)

(** Reflexive: A >= A. *)
Lemma greater_or_equal_reflexive
  : forall a7 a6 a5 a4 a3 a2 a1 a0,
    greater_or_equal_8bit a7 a6 a5 a4 a3 a2 a1 a0 a7 a6 a5 a4 a3 a2 a1 a0 = true.
Proof.
  intros.
  unfold greater_or_equal_8bit, less_than_8bit, lt_bit, eq_bit.
  destruct a7, a6, a5, a4, a3, a2, a1, a0; reflexivity.
Qed.

(** 255 >= 0. *)
Lemma greater_or_equal_max_min
  : greater_or_equal_8bit true true true true true true true true
                          false false false false false false false false = true.
Proof. reflexivity. Qed.

(** NOT (0 >= 255) is false, i.e. 0 >= 255 = false. Wait that's wrong. 0 >= 255 should be false. *)
Lemma greater_or_equal_min_max
  : greater_or_equal_8bit false false false false false false false false
                          true true true true true true true true = false.
Proof. reflexivity. Qed.

(** 0 >= 0. *)
Lemma greater_or_equal_zeros
  : greater_or_equal_8bit false false false false false false false false
                          false false false false false false false false = true.
Proof. reflexivity. Qed.

(** 1 >= 1. *)
Lemma greater_or_equal_ones
  : greater_or_equal_8bit false false false false false false false true
                          false false false false false false false true = true.
Proof. reflexivity. Qed.

(** 2 >= 1. *)
Lemma greater_or_equal_two_one
  : greater_or_equal_8bit false false false false false false true false
                          false false false false false false false true = true.
Proof. reflexivity. Qed.

(** * Network Architecture *)

Definition greater_or_equal_8bit_num_neurons : nat := 65.
Definition greater_or_equal_8bit_num_params : nat := 195.
Definition greater_or_equal_8bit_depth : nat := 5.
