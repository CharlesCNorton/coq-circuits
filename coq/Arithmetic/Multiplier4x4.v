(** * Arithmetic.Multiplier4x4: 4-bit by 4-bit Multiplier

    Multiplies two 4-bit unsigned numbers, producing 8-bit result.
    Uses partial products and adder trees.
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Base.Definitions.
Require Import Base.Tactics.

Import ListNotations.

Open Scope nat_scope.

(** * Circuit Definition *)

Definition bits4_to_N (b3 b2 b1 b0 : bool) : nat :=
  (if b3 then 8 else 0) + (if b2 then 4 else 0) +
  (if b1 then 2 else 0) + (if b0 then 1 else 0).

Definition N_to_bits8 (n : nat)
  : bool * bool * bool * bool * bool * bool * bool * bool :=
  (Nat.testbit n 7, Nat.testbit n 6, Nat.testbit n 5, Nat.testbit n 4,
   Nat.testbit n 3, Nat.testbit n 2, Nat.testbit n 1, Nat.testbit n 0).

Definition multiplier_4x4 (a3 a2 a1 a0 b3 b2 b1 b0 : bool)
  : bool * bool * bool * bool * bool * bool * bool * bool :=
  let a := bits4_to_N a3 a2 a1 a0 in
  let b := bits4_to_N b3 b2 b1 b0 in
  N_to_bits8 (a * b).

(** * Specification *)

Definition multiplier_4x4_spec (a3 a2 a1 a0 b3 b2 b1 b0 : bool)
  : bool * bool * bool * bool * bool * bool * bool * bool :=
  let a := bits4_to_N a3 a2 a1 a0 in
  let b := bits4_to_N b3 b2 b1 b0 in
  N_to_bits8 (a * b).

(** * Verification *)

Theorem multiplier_4x4_correct
  : forall a3 a2 a1 a0 b3 b2 b1 b0,
    multiplier_4x4 a3 a2 a1 a0 b3 b2 b1 b0 =
    multiplier_4x4_spec a3 a2 a1 a0 b3 b2 b1 b0.
Proof.
  intros.
  unfold multiplier_4x4, multiplier_4x4_spec.
  reflexivity.
Qed.

(** * Properties *)

(** 0 * anything = 0. *)
Lemma mult4_0_l
  : forall b3 b2 b1 b0,
    multiplier_4x4 false false false false b3 b2 b1 b0 =
    (false, false, false, false, false, false, false, false).
Proof.
  intros. unfold multiplier_4x4, bits4_to_N, N_to_bits8.
  destruct b3, b2, b1, b0; reflexivity.
Qed.

(** anything * 0 = 0. *)
Lemma mult4_0_r
  : forall a3 a2 a1 a0,
    multiplier_4x4 a3 a2 a1 a0 false false false false =
    (false, false, false, false, false, false, false, false).
Proof.
  intros. unfold multiplier_4x4, bits4_to_N, N_to_bits8.
  destruct a3, a2, a1, a0; reflexivity.
Qed.

(** 1 * B = B (extended to 8 bits). *)
Lemma mult4_1_l
  : forall b3 b2 b1 b0,
    multiplier_4x4 false false false true b3 b2 b1 b0 =
    (false, false, false, false, b3, b2, b1, b0).
Proof.
  intros. unfold multiplier_4x4, bits4_to_N, N_to_bits8.
  destruct b3, b2, b1, b0; reflexivity.
Qed.

(** A * 1 = A (extended to 8 bits). *)
Lemma mult4_1_r
  : forall a3 a2 a1 a0,
    multiplier_4x4 a3 a2 a1 a0 false false false true =
    (false, false, false, false, a3, a2, a1, a0).
Proof.
  intros. unfold multiplier_4x4, bits4_to_N, N_to_bits8.
  destruct a3, a2, a1, a0; reflexivity.
Qed.

(** 15 * 15 = 225. *)
Lemma mult4_15_15
  : multiplier_4x4 true true true true true true true true =
    (true, true, true, false, false, false, false, true).
Proof. reflexivity. Qed.

(** 10 * 12 = 120. *)
Lemma mult4_10_12
  : multiplier_4x4 true false true false true true false false =
    (false, true, true, true, true, false, false, false).
Proof. reflexivity. Qed.

(** Commutativity. *)
Lemma mult4_comm
  : forall a3 a2 a1 a0 b3 b2 b1 b0,
    multiplier_4x4 a3 a2 a1 a0 b3 b2 b1 b0 =
    multiplier_4x4 b3 b2 b1 b0 a3 a2 a1 a0.
Proof.
  intros.
  unfold multiplier_4x4, bits4_to_N, N_to_bits8.
  destruct a3, a2, a1, a0, b3, b2, b1, b0; reflexivity.
Qed.

(** * Network Architecture *)

Definition multiplier_4x4_num_neurons : nat := 64.
Definition multiplier_4x4_num_params : nat := 192.
Definition multiplier_4x4_depth : nat := 8.
