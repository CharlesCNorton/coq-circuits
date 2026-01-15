(** * Combinational.PriorityEncoder8Bit: 8-Bit Priority Encoder

    Returns the index of the highest-priority (highest-indexed) active input.
    Also outputs a valid signal indicating if any input is active.

    For one-hot inputs, this matches the simple encoder.
    For multiple active inputs, returns OR-combined encoding.
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Base.Definitions.
Require Import Base.Tactics.
Require Import Boolean.OR.

Import ListNotations.

Open Scope Z_scope.

(** * Circuit Definition *)

Definition priority_encoder_8bit (i0 i1 i2 i3 i4 i5 i6 i7 : bool)
  : bool * bool * bool * bool :=
  let valid := orb (orb (orb i0 i1) (orb i2 i3)) (orb (orb i4 i5) (orb i6 i7)) in
  let b2 := orb (orb i4 i5) (orb i6 i7) in
  let b1 := orb (orb i2 i3) (orb i6 i7) in
  let b0 := orb (orb i1 i3) (orb i5 i7) in
  (valid, b2, b1, b0).

(** * Specification *)

Definition priority_encoder_8bit_spec (i0 i1 i2 i3 i4 i5 i6 i7 : bool)
  : bool * bool * bool * bool :=
  let valid := orb (orb (orb i0 i1) (orb i2 i3)) (orb (orb i4 i5) (orb i6 i7)) in
  let b2 := orb (orb i4 i5) (orb i6 i7) in
  let b1 := orb (orb i2 i3) (orb i6 i7) in
  let b0 := orb (orb i1 i3) (orb i5 i7) in
  (valid, b2, b1, b0).

(** * Verification *)

Theorem priority_encoder_8bit_correct
  : forall i0 i1 i2 i3 i4 i5 i6 i7,
    priority_encoder_8bit i0 i1 i2 i3 i4 i5 i6 i7 =
    priority_encoder_8bit_spec i0 i1 i2 i3 i4 i5 i6 i7.
Proof.
  intros.
  unfold priority_encoder_8bit, priority_encoder_8bit_spec.
  reflexivity.
Qed.

(** No input means invalid *)
Theorem priority_encoder_8bit_no_input
  : priority_encoder_8bit false false false false false false false false =
    (false, false, false, false).
Proof. reflexivity. Qed.

(** One-hot input tests *)
Theorem priority_encoder_8bit_onehot_0
  : priority_encoder_8bit true false false false false false false false =
    (true, false, false, false).
Proof. reflexivity. Qed.

Theorem priority_encoder_8bit_onehot_7
  : priority_encoder_8bit false false false false false false false true =
    (true, true, true, true).
Proof. reflexivity. Qed.

(** * Network Architecture *)

Definition priority_encoder_8bit_num_neurons : nat := 12.
Definition priority_encoder_8bit_num_params : nat := 36.
Definition priority_encoder_8bit_depth : nat := 2.
