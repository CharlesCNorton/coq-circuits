(** * Combinational.Encoder8to3: 8-to-3 Priority Encoder

    Encodes 8 inputs to 3-bit binary output.
    Assumes at most one input is high (one-hot encoding).

    Output bits:
    - b2 = i4 OR i5 OR i6 OR i7
    - b1 = i2 OR i3 OR i6 OR i7
    - b0 = i1 OR i3 OR i5 OR i7
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

Definition or4 (a b c d : bool) : bool :=
  or_circuit (or_circuit a b) (or_circuit c d).

Definition encoder8to3 (i0 i1 i2 i3 i4 i5 i6 i7 : bool) : bool * bool * bool :=
  let b2 := or4 i4 i5 i6 i7 in
  let b1 := or4 i2 i3 i6 i7 in
  let b0 := or4 i1 i3 i5 i7 in
  (b2, b1, b0).

(** * Specification *)

Definition encoder8to3_spec (i0 i1 i2 i3 i4 i5 i6 i7 : bool) : bool * bool * bool :=
  (orb (orb i4 i5) (orb i6 i7),
   orb (orb i2 i3) (orb i6 i7),
   orb (orb i1 i3) (orb i5 i7)).

(** * Verification *)

Theorem encoder8to3_correct
  : forall i0 i1 i2 i3 i4 i5 i6 i7,
    encoder8to3 i0 i1 i2 i3 i4 i5 i6 i7 = encoder8to3_spec i0 i1 i2 i3 i4 i5 i6 i7.
Proof.
  intros.
  unfold encoder8to3, encoder8to3_spec, or4.
  destruct i0, i1, i2, i3, i4, i5, i6, i7; reflexivity.
Qed.

(** One-hot input produces correct binary encoding *)
Theorem encoder8to3_onehot_0 : encoder8to3 true false false false false false false false = (false, false, false).
Proof. reflexivity. Qed.

Theorem encoder8to3_onehot_1 : encoder8to3 false true false false false false false false = (false, false, true).
Proof. reflexivity. Qed.

Theorem encoder8to3_onehot_2 : encoder8to3 false false true false false false false false = (false, true, false).
Proof. reflexivity. Qed.

Theorem encoder8to3_onehot_3 : encoder8to3 false false false true false false false false = (false, true, true).
Proof. reflexivity. Qed.

Theorem encoder8to3_onehot_4 : encoder8to3 false false false false true false false false = (true, false, false).
Proof. reflexivity. Qed.

Theorem encoder8to3_onehot_5 : encoder8to3 false false false false false true false false = (true, false, true).
Proof. reflexivity. Qed.

Theorem encoder8to3_onehot_6 : encoder8to3 false false false false false false true false = (true, true, false).
Proof. reflexivity. Qed.

Theorem encoder8to3_onehot_7 : encoder8to3 false false false false false false false true = (true, true, true).
Proof. reflexivity. Qed.

(** * Network Architecture *)

Definition encoder8to3_num_neurons : nat := 9.
Definition encoder8to3_num_params : nat := 27.
Definition encoder8to3_depth : nat := 2.
