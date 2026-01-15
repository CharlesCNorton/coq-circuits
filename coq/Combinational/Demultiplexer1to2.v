(** * Combinational.Demultiplexer1to2: 1-to-2 Demultiplexer

    Routes input to one of two outputs based on select signal.
    DEMUX(s, d) = (NOT(s) AND d, s AND d)
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Base.Definitions.
Require Import Base.Tactics.
Require Import Boolean.AND.
Require Import Boolean.NOT.

Import ListNotations.

Open Scope Z_scope.

(** * Circuit Definition *)

Definition demux1to2 (s d : bool) : bool * bool :=
  (and_circuit (not_circuit s) d, and_circuit s d).

(** * Specification *)

Definition demux1to2_spec (s d : bool) : bool * bool :=
  if s then (false, d) else (d, false).

(** * Verification *)

Theorem demux1to2_correct
  : forall s d, demux1to2 s d = demux1to2_spec s d.
Proof.
  intros.
  unfold demux1to2, demux1to2_spec.
  destruct s, d; reflexivity.
Qed.

(** * Properties *)

Lemma demux1to2_select_0
  : forall d, demux1to2 false d = (d, false).
Proof.
  intros. destruct d; reflexivity.
Qed.

Lemma demux1to2_select_1
  : forall d, demux1to2 true d = (false, d).
Proof.
  intros. destruct d; reflexivity.
Qed.

Lemma demux1to2_zero_input
  : forall s, demux1to2 s false = (false, false).
Proof.
  intros. destruct s; reflexivity.
Qed.

(** * Network Architecture *)

Definition demux1to2_num_neurons : nat := 3.
Definition demux1to2_num_params : nat := 9.
Definition demux1to2_depth : nat := 2.
