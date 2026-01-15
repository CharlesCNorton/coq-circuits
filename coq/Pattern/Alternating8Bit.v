(** * Pattern.Alternating8Bit: Alternating Pattern Detector

    Returns true if bits alternate: 10101010 or 01010101.
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Base.Definitions.
Require Import Base.Tactics.

Import ListNotations.

Open Scope Z_scope.

(** * Circuit Definition *)

Definition alternating_8bit (b7 b6 b5 b4 b3 b2 b1 b0 : bool) : bool :=
  let pattern_10 := andb (andb (andb b7 (negb b6)) (andb b5 (negb b4)))
                         (andb (andb b3 (negb b2)) (andb b1 (negb b0))) in
  let pattern_01 := andb (andb (andb (negb b7) b6) (andb (negb b5) b4))
                         (andb (andb (negb b3) b2) (andb (negb b1) b0)) in
  orb pattern_10 pattern_01.

(** * Specification *)

Definition alternating_8bit_spec (b7 b6 b5 b4 b3 b2 b1 b0 : bool) : bool :=
  orb (andb (andb (andb b7 (negb b6)) (andb b5 (negb b4)))
            (andb (andb b3 (negb b2)) (andb b1 (negb b0))))
      (andb (andb (andb (negb b7) b6) (andb (negb b5) b4))
            (andb (andb (negb b3) b2) (andb (negb b1) b0))).

(** * Verification *)

Theorem alternating_8bit_correct
  : forall b7 b6 b5 b4 b3 b2 b1 b0,
    alternating_8bit b7 b6 b5 b4 b3 b2 b1 b0 =
    alternating_8bit_spec b7 b6 b5 b4 b3 b2 b1 b0.
Proof. intros. reflexivity. Qed.

(** 10101010 is alternating *)
Theorem alternating_8bit_10
  : alternating_8bit true false true false true false true false = true.
Proof. reflexivity. Qed.

(** 01010101 is alternating *)
Theorem alternating_8bit_01
  : alternating_8bit false true false true false true false true = true.
Proof. reflexivity. Qed.

(** All zeros is not alternating *)
Theorem alternating_8bit_zeros
  : alternating_8bit false false false false false false false false = false.
Proof. reflexivity. Qed.

(** All ones is not alternating *)
Theorem alternating_8bit_ones
  : alternating_8bit true true true true true true true true = false.
Proof. reflexivity. Qed.

(** * Network Architecture *)

Definition alternating_8bit_num_neurons : nat := 17.
Definition alternating_8bit_num_params : nat := 51.
Definition alternating_8bit_depth : nat := 4.
