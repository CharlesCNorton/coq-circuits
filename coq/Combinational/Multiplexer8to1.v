(** * Combinational.Multiplexer8to1: 8-to-1 Multiplexer

    Selects one of eight inputs based on 3-bit select signal.
    Composed from two 4-to-1 multiplexers and one 2-to-1 multiplexer.
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Base.Definitions.
Require Import Base.Tactics.
Require Import Combinational.Multiplexer2to1.
Require Import Combinational.Multiplexer4to1.

Import ListNotations.

Open Scope Z_scope.

(** * Circuit Definition *)

Definition mux8to1 (s2 s1 s0 a b c d e f g h : bool) : bool :=
  let abcd := mux4to1 s1 s0 a b c d in
  let efgh := mux4to1 s1 s0 e f g h in
  mux2to1 s2 abcd efgh.

(** * Specification *)

Definition mux8to1_spec (s2 s1 s0 a b c d e f g h : bool) : bool :=
  match s2, s1, s0 with
  | false, false, false => a
  | false, false, true => b
  | false, true, false => c
  | false, true, true => d
  | true, false, false => e
  | true, false, true => f
  | true, true, false => g
  | true, true, true => h
  end.

(** * Verification *)

Theorem mux8to1_correct
  : forall s2 s1 s0 a b c d e f g h,
    mux8to1 s2 s1 s0 a b c d e f g h = mux8to1_spec s2 s1 s0 a b c d e f g h.
Proof.
  intros.
  unfold mux8to1, mux8to1_spec.
  destruct s2, s1, s0, a, b, c, d, e, f, g, h; reflexivity.
Qed.

(** * Properties *)

Lemma mux8to1_same_inputs
  : forall s2 s1 s0 x, mux8to1 s2 s1 s0 x x x x x x x x = x.
Proof.
  intros.
  destruct s2, s1, s0, x; reflexivity.
Qed.

(** * Network Architecture *)

Definition mux8to1_num_neurons : nat := 28.
Definition mux8to1_num_params : nat := 84.
Definition mux8to1_depth : nat := 6.
