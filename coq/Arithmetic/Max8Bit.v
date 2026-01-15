(** * Arithmetic.Max8Bit: 8-Bit Maximum

    Returns the maximum of two 8-bit unsigned numbers.
    Max(A, B) = if A >= B then A else B.
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Base.Definitions.
Require Import Base.Tactics.
Require Import Arithmetic.LessThan8Bit.
Require Import Arithmetic.GreaterOrEqual8Bit.

Import ListNotations.

Open Scope Z_scope.

(** * Circuit Definition *)

(** Select bit based on condition. *)
Definition select_bit (cond a b : bool) : bool :=
  orb (andb cond a) (andb (negb cond) b).

Definition max_8bit
  (a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0 : bool)
  : bool * bool * bool * bool * bool * bool * bool * bool :=
  let cond := greater_or_equal_8bit a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0 in
  (select_bit cond a7 b7,
   select_bit cond a6 b6,
   select_bit cond a5 b5,
   select_bit cond a4 b4,
   select_bit cond a3 b3,
   select_bit cond a2 b2,
   select_bit cond a1 b1,
   select_bit cond a0 b0).

(** * Specification *)

Definition bits_to_N (b7 b6 b5 b4 b3 b2 b1 b0 : bool) : nat :=
  (if b7 then 128 else 0) + (if b6 then 64 else 0) +
  (if b5 then 32 else 0) + (if b4 then 16 else 0) +
  (if b3 then 8 else 0) + (if b2 then 4 else 0) +
  (if b1 then 2 else 0) + (if b0 then 1 else 0).

Definition max_8bit_spec
  (a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0 : bool)
  : bool * bool * bool * bool * bool * bool * bool * bool :=
  if Nat.leb (bits_to_N b7 b6 b5 b4 b3 b2 b1 b0)
             (bits_to_N a7 a6 a5 a4 a3 a2 a1 a0)
  then (a7, a6, a5, a4, a3, a2, a1, a0)
  else (b7, b6, b5, b4, b3, b2, b1, b0).

(** * Verification *)

Theorem max_8bit_correct
  : forall a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0,
    max_8bit a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0 =
    max_8bit_spec a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0.
Proof.
  intros.
  unfold max_8bit, max_8bit_spec, select_bit.
  unfold greater_or_equal_8bit, less_than_8bit, lt_bit, eq_bit, bits_to_N.
  destruct a7, a6, a5, a4, a3, a2, a1, a0, b7, b6, b5, b4, b3, b2, b1, b0;
  reflexivity.
Qed.

(** * Properties *)

(** Max(A, A) = A. *)
Lemma max_idempotent
  : forall a7 a6 a5 a4 a3 a2 a1 a0,
    max_8bit a7 a6 a5 a4 a3 a2 a1 a0 a7 a6 a5 a4 a3 a2 a1 a0 =
    (a7, a6, a5, a4, a3, a2, a1, a0).
Proof.
  intros.
  unfold max_8bit, select_bit, greater_or_equal_8bit.
  unfold less_than_8bit, lt_bit, eq_bit.
  destruct a7, a6, a5, a4, a3, a2, a1, a0; reflexivity.
Qed.

(** Max(255, 0) = 255. *)
Lemma max_255_0
  : max_8bit true true true true true true true true
             false false false false false false false false =
    (true, true, true, true, true, true, true, true).
Proof. reflexivity. Qed.

(** Max(0, 255) = 255. *)
Lemma max_0_255
  : max_8bit false false false false false false false false
             true true true true true true true true =
    (true, true, true, true, true, true, true, true).
Proof. reflexivity. Qed.

(** Max(5, 10) = 10. *)
Lemma max_5_10
  : max_8bit false false false false false true false true
             false false false false true false true false =
    (false, false, false, false, true, false, true, false).
Proof. reflexivity. Qed.

(** * Network Architecture *)

Definition max_8bit_num_neurons : nat := 89.
Definition max_8bit_num_params : nat := 267.
Definition max_8bit_depth : nat := 6.
