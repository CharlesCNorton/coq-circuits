(** * Arithmetic.GreaterThan8Bit: 8-Bit Greater Than Comparator

    Fires when A > B for two 8-bit unsigned numbers.
    Compares from MSB to LSB.
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Base.Definitions.
Require Import Base.Tactics.

Import ListNotations.

Open Scope Z_scope.

(** * Circuit Definition *)

(** Bit comparison helpers. *)
Definition gt_bit (a b : bool) : bool := andb a (negb b).
Definition eq_bit (a b : bool) : bool := Bool.eqb a b.

(** Greater than: compare from MSB to LSB.
    A > B iff first differing bit has a=1, b=0. *)
Definition greater_than_8bit
  (a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0 : bool) : bool :=
  if gt_bit a7 b7 then true
  else if negb (eq_bit a7 b7) then false
  else if gt_bit a6 b6 then true
  else if negb (eq_bit a6 b6) then false
  else if gt_bit a5 b5 then true
  else if negb (eq_bit a5 b5) then false
  else if gt_bit a4 b4 then true
  else if negb (eq_bit a4 b4) then false
  else if gt_bit a3 b3 then true
  else if negb (eq_bit a3 b3) then false
  else if gt_bit a2 b2 then true
  else if negb (eq_bit a2 b2) then false
  else if gt_bit a1 b1 then true
  else if negb (eq_bit a1 b1) then false
  else gt_bit a0 b0.

(** * Specification *)

(** Convert 8 bits to natural number. *)
Definition bits_to_N (b7 b6 b5 b4 b3 b2 b1 b0 : bool) : nat :=
  (if b7 then 128 else 0) + (if b6 then 64 else 0) +
  (if b5 then 32 else 0) + (if b4 then 16 else 0) +
  (if b3 then 8 else 0) + (if b2 then 4 else 0) +
  (if b1 then 2 else 0) + (if b0 then 1 else 0).

Definition greater_than_8bit_spec
  (a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0 : bool) : bool :=
  Nat.ltb (bits_to_N b7 b6 b5 b4 b3 b2 b1 b0)
          (bits_to_N a7 a6 a5 a4 a3 a2 a1 a0).

(** * Verification *)

Theorem greater_than_8bit_correct
  : forall a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0,
    greater_than_8bit a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0 =
    greater_than_8bit_spec a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0.
Proof.
  intros.
  unfold greater_than_8bit, greater_than_8bit_spec, gt_bit, eq_bit, bits_to_N.
  destruct a7, a6, a5, a4, a3, a2, a1, a0, b7, b6, b5, b4, b3, b2, b1, b0;
  reflexivity.
Qed.

(** * Properties *)

(** Not greater than self. *)
Lemma greater_than_irreflexive
  : forall a7 a6 a5 a4 a3 a2 a1 a0,
    greater_than_8bit a7 a6 a5 a4 a3 a2 a1 a0 a7 a6 a5 a4 a3 a2 a1 a0 = false.
Proof.
  intros.
  unfold greater_than_8bit, gt_bit, eq_bit.
  destruct a7, a6, a5, a4, a3, a2, a1, a0; reflexivity.
Qed.

(** 255 > 0. *)
Lemma greater_than_max_min
  : greater_than_8bit true true true true true true true true
                      false false false false false false false false = true.
Proof. reflexivity. Qed.

(** NOT (0 > 255). *)
Lemma greater_than_min_max
  : greater_than_8bit false false false false false false false false
                      true true true true true true true true = false.
Proof. reflexivity. Qed.

(** 1 > 0. *)
Lemma greater_than_one_zero
  : greater_than_8bit false false false false false false false true
                      false false false false false false false false = true.
Proof. reflexivity. Qed.

(** NOT (0 > 1). *)
Lemma greater_than_zero_one
  : greater_than_8bit false false false false false false false false
                      false false false false false false false true = false.
Proof. reflexivity. Qed.

(** 128 > 127. *)
Lemma greater_than_128_127
  : greater_than_8bit true false false false false false false false
                      false true true true true true true true = true.
Proof. reflexivity. Qed.

(** * Network Architecture *)

Definition greater_than_8bit_num_neurons : nat := 64.
Definition greater_than_8bit_num_params : nat := 192.
Definition greater_than_8bit_depth : nat := 4.
