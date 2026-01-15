(** * Combinational.Demultiplexer1to8: 1-to-8 Demultiplexer

    Routes input to one of eight outputs based on 3-bit select signal.
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Base.Definitions.
Require Import Base.Tactics.
Require Import Combinational.Demultiplexer1to2.
Require Import Combinational.Demultiplexer1to4.

Import ListNotations.

Open Scope Z_scope.

(** * Circuit Definition *)

Definition demux1to8 (s2 s1 s0 d : bool)
  : bool * bool * bool * bool * bool * bool * bool * bool :=
  let '(d0, d1) := demux1to2 s2 d in
  let '(out0, out1, out2, out3) := demux1to4 s1 s0 d0 in
  let '(out4, out5, out6, out7) := demux1to4 s1 s0 d1 in
  (out0, out1, out2, out3, out4, out5, out6, out7).

(** * Specification *)

Definition demux1to8_spec (s2 s1 s0 d : bool)
  : bool * bool * bool * bool * bool * bool * bool * bool :=
  match s2, s1, s0 with
  | false, false, false => (d, false, false, false, false, false, false, false)
  | false, false, true => (false, false, d, false, false, false, false, false)
  | false, true, false => (false, d, false, false, false, false, false, false)
  | false, true, true => (false, false, false, d, false, false, false, false)
  | true, false, false => (false, false, false, false, d, false, false, false)
  | true, false, true => (false, false, false, false, false, false, d, false)
  | true, true, false => (false, false, false, false, false, d, false, false)
  | true, true, true => (false, false, false, false, false, false, false, d)
  end.

(** * Verification *)

Theorem demux1to8_correct
  : forall s2 s1 s0 d, demux1to8 s2 s1 s0 d = demux1to8_spec s2 s1 s0 d.
Proof.
  intros.
  unfold demux1to8, demux1to8_spec.
  destruct s2, s1, s0, d; reflexivity.
Qed.

(** * Properties *)

Lemma demux1to8_zero_input
  : forall s2 s1 s0,
    demux1to8 s2 s1 s0 false = (false, false, false, false, false, false, false, false).
Proof.
  intros. destruct s2, s1, s0; reflexivity.
Qed.

(** * Network Architecture *)

Definition demux1to8_num_neurons : nat := 21.
Definition demux1to8_num_params : nat := 63.
Definition demux1to8_depth : nat := 6.
