(** * Combinational.Multiplexer4to1: 4-to-1 Multiplexer

    Selects one of four inputs based on 2-bit select signal.
    Composed from three 2-to-1 multiplexers.
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Base.Definitions.
Require Import Base.Tactics.
Require Import Combinational.Multiplexer2to1.

Import ListNotations.

Open Scope Z_scope.

(** * Circuit Definition *)

(** MUX4(s1, s0, a, b, c, d):
    s1=0, s0=0 -> a
    s1=0, s0=1 -> b
    s1=1, s0=0 -> c
    s1=1, s0=1 -> d

    Implementation: two levels of MUX2
    First level: MUX2(s0, a, b) and MUX2(s0, c, d)
    Second level: MUX2(s1, first_result, second_result)
*)
Definition mux4to1 (s1 s0 a b c d : bool) : bool :=
  let ab := mux2to1 s0 a b in
  let cd := mux2to1 s0 c d in
  mux2to1 s1 ab cd.

(** * Specification *)

Definition mux4to1_spec (s1 s0 a b c d : bool) : bool :=
  match s1, s0 with
  | false, false => a
  | false, true => b
  | true, false => c
  | true, true => d
  end.

(** * Verification *)

Theorem mux4to1_correct
  : forall s1 s0 a b c d,
    mux4to1 s1 s0 a b c d = mux4to1_spec s1 s0 a b c d.
Proof.
  intros.
  unfold mux4to1, mux4to1_spec.
  rewrite mux2to1_correct, mux2to1_correct, mux2to1_correct.
  unfold mux2to1_spec.
  destruct s1, s0; reflexivity.
Qed.

(** * Properties *)

Lemma mux4to1_select_a
  : forall a b c d, mux4to1 false false a b c d = a.
Proof.
  intros.
  unfold mux4to1.
  destruct a, b, c, d; reflexivity.
Qed.

Lemma mux4to1_select_b
  : forall a b c d, mux4to1 false true a b c d = b.
Proof.
  intros.
  unfold mux4to1.
  destruct a, b, c, d; reflexivity.
Qed.

Lemma mux4to1_select_c
  : forall a b c d, mux4to1 true false a b c d = c.
Proof.
  intros.
  unfold mux4to1.
  destruct a, b, c, d; reflexivity.
Qed.

Lemma mux4to1_select_d
  : forall a b c d, mux4to1 true true a b c d = d.
Proof.
  intros.
  unfold mux4to1.
  destruct a, b, c, d; reflexivity.
Qed.

Lemma mux4to1_same_inputs
  : forall s1 s0 x, mux4to1 s1 s0 x x x x = x.
Proof.
  intros.
  unfold mux4to1.
  destruct s1, s0, x; reflexivity.
Qed.

(** * Network Architecture *)

(** 3 MUX2s, each with 4 neurons *)
Definition mux4to1_num_neurons : nat := 12.
Definition mux4to1_num_params : nat := 36.
Definition mux4to1_depth : nat := 4.
