(** * Combinational.Demultiplexer1to4: 1-to-4 Demultiplexer

    Routes input to one of four outputs based on 2-bit select signal.
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Base.Definitions.
Require Import Base.Tactics.
Require Import Combinational.Demultiplexer1to2.

Import ListNotations.

Open Scope Z_scope.

(** * Circuit Definition *)

Definition demux1to4 (s1 s0 d : bool) : bool * bool * bool * bool :=
  let '(d0, d1) := demux1to2 s0 d in
  let '(out0, out1) := demux1to2 s1 d0 in
  let '(out2, out3) := demux1to2 s1 d1 in
  (out0, out1, out2, out3).

(** * Specification *)

Definition demux1to4_spec (s1 s0 d : bool) : bool * bool * bool * bool :=
  match s1, s0 with
  | false, false => (d, false, false, false)
  | false, true => (false, false, d, false)
  | true, false => (false, d, false, false)
  | true, true => (false, false, false, d)
  end.

(** * Verification *)

Theorem demux1to4_correct
  : forall s1 s0 d, demux1to4 s1 s0 d = demux1to4_spec s1 s0 d.
Proof.
  intros.
  unfold demux1to4, demux1to4_spec.
  destruct s1, s0, d; reflexivity.
Qed.

(** * Properties *)

Lemma demux1to4_zero_input
  : forall s1 s0, demux1to4 s1 s0 false = (false, false, false, false).
Proof.
  intros. destruct s1, s0; reflexivity.
Qed.

(** * Network Architecture *)

Definition demux1to4_num_neurons : nat := 9.
Definition demux1to4_num_params : nat := 27.
Definition demux1to4_depth : nat := 4.
