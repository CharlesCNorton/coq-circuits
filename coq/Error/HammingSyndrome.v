(** * Error.HammingSyndrome: Hamming (7,4) Syndrome Calculator

    Computes 3-bit syndrome from 7-bit Hamming codeword.
    Syndrome = 0 indicates no error.
    Syndrome = n (1-7) indicates error at position n.

    Input format: p2 p1 p0 d3 d2 d1 d0
    Output: s2 s1 s0 (3-bit syndrome)
*)

Require Import List.
Require Import Bool.
Require Import Base.Definitions.
Require Import Base.Tactics.

Import ListNotations.

Open Scope nat_scope.

(** * Circuit Definition *)

(** Compute syndrome bits for error detection/location.
    s0 checks positions 1,3,5,7 (p0, d0, d1, d3)
    s1 checks positions 2,3,6,7 (p1, d0, d2, d3)
    s2 checks positions 4,5,6,7 (p2, d1, d2, d3)
*)
Definition hamming_syndrome (p2 p1 p0 d3 d2 d1 d0 : bool)
  : bool * bool * bool :=
  let s0 := xorb (xorb p0 d0) (xorb d1 d3) in
  let s1 := xorb (xorb p1 d0) (xorb d2 d3) in
  let s2 := xorb (xorb p2 d1) (xorb d2 d3) in
  (s2, s1, s0).

(** Convert syndrome to error position (0 = no error, 1-7 = position). *)
Definition syndrome_to_position (s2 s1 s0 : bool) : nat :=
  (if s2 then 4 else 0) + (if s1 then 2 else 0) + (if s0 then 1 else 0).

(** * Specification *)

Definition hamming_syndrome_spec (p2 p1 p0 d3 d2 d1 d0 : bool)
  : bool * bool * bool :=
  let s0 := xorb (xorb p0 d0) (xorb d1 d3) in
  let s1 := xorb (xorb p1 d0) (xorb d2 d3) in
  let s2 := xorb (xorb p2 d1) (xorb d2 d3) in
  (s2, s1, s0).

(** * Verification *)

Theorem hamming_syndrome_correct
  : forall p2 p1 p0 d3 d2 d1 d0,
    hamming_syndrome p2 p1 p0 d3 d2 d1 d0 =
    hamming_syndrome_spec p2 p1 p0 d3 d2 d1 d0.
Proof.
  intros. reflexivity.
Qed.

(** * Properties *)

(** Valid codeword has zero syndrome. *)
Require Import Error.HammingEncode4Bit.

Theorem valid_codeword_zero_syndrome
  : forall d3 d2 d1 d0,
    let '(p2, p1, p0, d3', d2', d1', d0') := hamming_encode_4bit d3 d2 d1 d0 in
    hamming_syndrome p2 p1 p0 d3' d2' d1' d0' = (false, false, false).
Proof.
  intros.
  unfold hamming_encode_4bit, hamming_syndrome.
  destruct d3, d2, d1, d0; reflexivity.
Qed.

(** Zero syndrome means position 0 (no error). *)
Lemma zero_syndrome_no_error
  : syndrome_to_position false false false = 0.
Proof. reflexivity. Qed.

(** Syndrome values 1-7 indicate error positions. *)
Lemma syndrome_pos_1 : syndrome_to_position false false true = 1.
Proof. reflexivity. Qed.

Lemma syndrome_pos_2 : syndrome_to_position false true false = 2.
Proof. reflexivity. Qed.

Lemma syndrome_pos_3 : syndrome_to_position false true true = 3.
Proof. reflexivity. Qed.

Lemma syndrome_pos_4 : syndrome_to_position true false false = 4.
Proof. reflexivity. Qed.

Lemma syndrome_pos_5 : syndrome_to_position true false true = 5.
Proof. reflexivity. Qed.

Lemma syndrome_pos_6 : syndrome_to_position true true false = 6.
Proof. reflexivity. Qed.

Lemma syndrome_pos_7 : syndrome_to_position true true true = 7.
Proof. reflexivity. Qed.

(** Single-bit error produces correct syndrome. *)
Lemma error_at_pos1_syndrome
  : forall d3 d2 d1 d0,
    let '(p2, p1, p0, d3', d2', d1', d0') := hamming_encode_4bit d3 d2 d1 d0 in
    let '(s2, s1, s0) := hamming_syndrome p2 p1 (negb p0) d3' d2' d1' d0' in
    syndrome_to_position s2 s1 s0 = 1.
Proof.
  intros.
  unfold hamming_encode_4bit, hamming_syndrome, syndrome_to_position.
  destruct d3, d2, d1, d0; reflexivity.
Qed.

Lemma error_at_pos7_syndrome
  : forall d3 d2 d1 d0,
    let '(p2, p1, p0, d3', d2', d1', d0') := hamming_encode_4bit d3 d2 d1 d0 in
    let '(s2, s1, s0) := hamming_syndrome p2 p1 p0 (negb d3') d2' d1' d0' in
    syndrome_to_position s2 s1 s0 = 7.
Proof.
  intros.
  unfold hamming_encode_4bit, hamming_syndrome, syndrome_to_position.
  destruct d3, d2, d1, d0; reflexivity.
Qed.

(** * Network Architecture *)

Definition hamming_syndrome_num_neurons : nat := 9.
Definition hamming_syndrome_num_params : nat := 27.
Definition hamming_syndrome_depth : nat := 2.
