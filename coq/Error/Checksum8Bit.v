(** * Error.Checksum8Bit: 8-Bit Checksum

    Computes simple checksum (sum of bit values mod 256).
    For 8 bits, this equals the hamming weight.
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Base.Definitions.
Require Import Base.Tactics.

Import ListNotations.

Open Scope nat_scope.

(** * Circuit Definition *)

Definition checksum_8bit (b7 b6 b5 b4 b3 b2 b1 b0 : bool) : nat :=
  (if b7 then 1 else 0) + (if b6 then 1 else 0) +
  (if b5 then 1 else 0) + (if b4 then 1 else 0) +
  (if b3 then 1 else 0) + (if b2 then 1 else 0) +
  (if b1 then 1 else 0) + (if b0 then 1 else 0).

(** * Specification *)

Definition checksum_8bit_spec (b7 b6 b5 b4 b3 b2 b1 b0 : bool) : nat :=
  hamming_weight [b0; b1; b2; b3; b4; b5; b6; b7].

(** * Verification *)

Theorem checksum_8bit_correct
  : forall b7 b6 b5 b4 b3 b2 b1 b0,
    checksum_8bit b7 b6 b5 b4 b3 b2 b1 b0 =
    checksum_8bit_spec b7 b6 b5 b4 b3 b2 b1 b0.
Proof.
  intros.
  unfold checksum_8bit, checksum_8bit_spec, hamming_weight.
  destruct b7, b6, b5, b4, b3, b2, b1, b0; reflexivity.
Qed.

(** All zeros gives checksum 0 *)
Theorem checksum_8bit_zeros
  : checksum_8bit false false false false false false false false = 0.
Proof. reflexivity. Qed.

(** All ones gives checksum 8 *)
Theorem checksum_8bit_ones
  : checksum_8bit true true true true true true true true = 8.
Proof. reflexivity. Qed.

(** * Network Architecture *)

Definition checksum_8bit_num_neurons : nat := 9.
Definition checksum_8bit_num_params : nat := 81.
Definition checksum_8bit_depth : nat := 1.
