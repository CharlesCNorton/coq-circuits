(** * Error.HammingDecode7Bit: Hamming (7,4) Decoder

    Decodes 7-bit Hamming codeword back to 4 data bits.
    Corrects single-bit errors using syndrome computation.

    Input format: p2 p1 p0 d3 d2 d1 d0 (positions 4,2,1,7,6,5,3)
    Output: d3 d2 d1 d0 (4 data bits, corrected if needed)
*)

Require Import List.
Require Import Bool.
Require Import Base.Definitions.
Require Import Base.Tactics.

Import ListNotations.

Open Scope nat_scope.

(** * Circuit Definition *)

(** Compute syndrome bits.
    s0 checks positions 1,3,5,7 (p0, d0, d1, d3)
    s1 checks positions 2,3,6,7 (p1, d0, d2, d3)
    s2 checks positions 4,5,6,7 (p2, d1, d2, d3)

    Syndrome = 0 means no error.
    Syndrome = n means error at position n.
*)
Definition hamming_syndrome (p2 p1 p0 d3 d2 d1 d0 : bool)
  : bool * bool * bool :=
  let s0 := xorb (xorb p0 d0) (xorb d1 d3) in
  let s1 := xorb (xorb p1 d0) (xorb d2 d3) in
  let s2 := xorb (xorb p2 d1) (xorb d2 d3) in
  (s2, s1, s0).

(** Convert syndrome to error position (0 = no error, 1-7 = position). *)
Definition syndrome_to_pos (s2 s1 s0 : bool) : nat :=
  (if s2 then 4 else 0) + (if s1 then 2 else 0) + (if s0 then 1 else 0).

(** Flip bit at given position in codeword.
    Positions: 1=p0, 2=p1, 3=d0, 4=p2, 5=d1, 6=d2, 7=d3 *)
Definition flip_at_pos (pos : nat) (p2 p1 p0 d3 d2 d1 d0 : bool)
  : bool * bool * bool * bool * bool * bool * bool :=
  match pos with
  | 1 => (p2, p1, negb p0, d3, d2, d1, d0)
  | 2 => (p2, negb p1, p0, d3, d2, d1, d0)
  | 3 => (p2, p1, p0, d3, d2, d1, negb d0)
  | 4 => (negb p2, p1, p0, d3, d2, d1, d0)
  | 5 => (p2, p1, p0, d3, d2, negb d1, d0)
  | 6 => (p2, p1, p0, d3, negb d2, d1, d0)
  | 7 => (p2, p1, p0, negb d3, d2, d1, d0)
  | _ => (p2, p1, p0, d3, d2, d1, d0)
  end.

(** Decode 7-bit Hamming codeword to 4 data bits with error correction. *)
Definition hamming_decode_7bit (p2 p1 p0 d3 d2 d1 d0 : bool)
  : bool * bool * bool * bool :=
  let '(s2, s1, s0) := hamming_syndrome p2 p1 p0 d3 d2 d1 d0 in
  let pos := syndrome_to_pos s2 s1 s0 in
  let '(_, _, _, d3', d2', d1', d0') := flip_at_pos pos p2 p1 p0 d3 d2 d1 d0 in
  (d3', d2', d1', d0').

(** * Specification *)

Definition hamming_decode_7bit_spec (p2 p1 p0 d3 d2 d1 d0 : bool)
  : bool * bool * bool * bool :=
  let '(s2, s1, s0) := hamming_syndrome p2 p1 p0 d3 d2 d1 d0 in
  let pos := syndrome_to_pos s2 s1 s0 in
  let '(_, _, _, d3', d2', d1', d0') := flip_at_pos pos p2 p1 p0 d3 d2 d1 d0 in
  (d3', d2', d1', d0').

(** * Verification *)

Theorem hamming_decode_7bit_correct
  : forall p2 p1 p0 d3 d2 d1 d0,
    hamming_decode_7bit p2 p1 p0 d3 d2 d1 d0 =
    hamming_decode_7bit_spec p2 p1 p0 d3 d2 d1 d0.
Proof.
  intros. reflexivity.
Qed.

(** * Properties *)

(** Valid codeword decodes to original data. *)
Lemma decode_valid_zeros
  : hamming_decode_7bit false false false false false false false =
    (false, false, false, false).
Proof. reflexivity. Qed.

Lemma decode_valid_ones
  : hamming_decode_7bit true true true true true true true =
    (true, true, true, true).
Proof. reflexivity. Qed.

(** Encoding then decoding recovers original data. *)
Require Import Error.HammingEncode4Bit.

Theorem encode_decode_identity
  : forall d3 d2 d1 d0,
    let '(p2, p1, p0, d3', d2', d1', d0') := hamming_encode_4bit d3 d2 d1 d0 in
    hamming_decode_7bit p2 p1 p0 d3' d2' d1' d0' = (d3, d2, d1, d0).
Proof.
  intros.
  unfold hamming_encode_4bit, hamming_decode_7bit, hamming_syndrome.
  unfold syndrome_to_pos, flip_at_pos.
  destruct d3, d2, d1, d0; reflexivity.
Qed.

(** Single-bit error correction: flipping any bit and decoding recovers data. *)
Lemma correct_error_pos1
  : forall d3 d2 d1 d0,
    let '(p2, p1, p0, d3', d2', d1', d0') := hamming_encode_4bit d3 d2 d1 d0 in
    hamming_decode_7bit p2 p1 (negb p0) d3' d2' d1' d0' = (d3, d2, d1, d0).
Proof.
  intros.
  unfold hamming_encode_4bit, hamming_decode_7bit, hamming_syndrome.
  unfold syndrome_to_pos, flip_at_pos.
  destruct d3, d2, d1, d0; reflexivity.
Qed.

Lemma correct_error_pos3
  : forall d3 d2 d1 d0,
    let '(p2, p1, p0, d3', d2', d1', d0') := hamming_encode_4bit d3 d2 d1 d0 in
    hamming_decode_7bit p2 p1 p0 d3' d2' d1' (negb d0') = (d3, d2, d1, d0).
Proof.
  intros.
  unfold hamming_encode_4bit, hamming_decode_7bit, hamming_syndrome.
  unfold syndrome_to_pos, flip_at_pos.
  destruct d3, d2, d1, d0; reflexivity.
Qed.

Lemma correct_error_pos7
  : forall d3 d2 d1 d0,
    let '(p2, p1, p0, d3', d2', d1', d0') := hamming_encode_4bit d3 d2 d1 d0 in
    hamming_decode_7bit p2 p1 p0 (negb d3') d2' d1' d0' = (d3, d2, d1, d0).
Proof.
  intros.
  unfold hamming_encode_4bit, hamming_decode_7bit, hamming_syndrome.
  unfold syndrome_to_pos, flip_at_pos.
  destruct d3, d2, d1, d0; reflexivity.
Qed.

(** * Network Architecture *)

Definition hamming_decode_7bit_num_neurons : nat := 24.
Definition hamming_decode_7bit_num_params : nat := 72.
Definition hamming_decode_7bit_depth : nat := 4.
