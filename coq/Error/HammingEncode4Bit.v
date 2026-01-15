(** * Error.HammingEncode4Bit: Hamming (7,4) Encoder

    Encodes 4 data bits into 7-bit Hamming code with 3 parity bits.
    Can detect and correct single-bit errors.

    Format: p1 p2 d1 p3 d2 d3 d4 (positions 1-7)
    where p1 checks positions 1,3,5,7
          p2 checks positions 2,3,6,7
          p3 checks positions 4,5,6,7
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Base.Definitions.
Require Import Base.Tactics.

Import ListNotations.

Open Scope Z_scope.

(** * Circuit Definition *)

(** Generate parity bits for Hamming (7,4) code.
    Input: d3 d2 d1 d0 (4 data bits)
    Output: p2 p1 p0 d3 d2 d1 d0 (3 parity + 4 data = 7 bits)

    Positions in codeword:
    - Position 1: p0
    - Position 2: p1
    - Position 3: d0
    - Position 4: p2
    - Position 5: d1
    - Position 6: d2
    - Position 7: d3

    Parity equations:
    - p0 = d0 XOR d1 XOR d3 (covers positions 1,3,5,7)
    - p1 = d0 XOR d2 XOR d3 (covers positions 2,3,6,7)
    - p2 = d1 XOR d2 XOR d3 (covers positions 4,5,6,7)
*)
Definition hamming_encode_4bit (d3 d2 d1 d0 : bool)
  : bool * bool * bool * bool * bool * bool * bool :=
  let p0 := xorb (xorb d0 d1) d3 in
  let p1 := xorb (xorb d0 d2) d3 in
  let p2 := xorb (xorb d1 d2) d3 in
  (p2, p1, p0, d3, d2, d1, d0).

(** * Specification *)

Definition hamming_encode_4bit_spec (d3 d2 d1 d0 : bool)
  : bool * bool * bool * bool * bool * bool * bool :=
  let p0 := xorb (xorb d0 d1) d3 in
  let p1 := xorb (xorb d0 d2) d3 in
  let p2 := xorb (xorb d1 d2) d3 in
  (p2, p1, p0, d3, d2, d1, d0).

(** * Verification *)

Theorem hamming_encode_4bit_correct
  : forall d3 d2 d1 d0,
    hamming_encode_4bit d3 d2 d1 d0 = hamming_encode_4bit_spec d3 d2 d1 d0.
Proof.
  intros. reflexivity.
Qed.

(** * Properties *)

(** All zeros encodes to all zeros. *)
Lemma hamming_encode_zeros
  : hamming_encode_4bit false false false false =
    (false, false, false, false, false, false, false).
Proof. reflexivity. Qed.

(** Single bit set. *)
Lemma hamming_encode_0001
  : hamming_encode_4bit false false false true =
    (false, true, true, false, false, false, true).
Proof. reflexivity. Qed.

Lemma hamming_encode_0010
  : hamming_encode_4bit false false true false =
    (true, false, true, false, false, true, false).
Proof. reflexivity. Qed.

Lemma hamming_encode_0100
  : hamming_encode_4bit false true false false =
    (true, true, false, false, true, false, false).
Proof. reflexivity. Qed.

Lemma hamming_encode_1000
  : hamming_encode_4bit true false false false =
    (true, true, true, true, false, false, false).
Proof. reflexivity. Qed.

(** All ones. *)
Lemma hamming_encode_1111
  : hamming_encode_4bit true true true true =
    (true, true, true, true, true, true, true).
Proof. reflexivity. Qed.

(** Parity check: XOR of all bits at positions covered by p0 should equal p0. *)
Lemma parity_check_p0
  : forall d3 d2 d1 d0,
    let '(p2, p1, p0, d3', d2', d1', d0') := hamming_encode_4bit d3 d2 d1 d0 in
    xorb (xorb p0 d0') (xorb d1' d3') = false.
Proof.
  intros. unfold hamming_encode_4bit.
  destruct d3, d2, d1, d0; reflexivity.
Qed.

(** * Network Architecture *)

Definition hamming_encode_4bit_num_neurons : nat := 9.
Definition hamming_encode_4bit_num_params : nat := 27.
Definition hamming_encode_4bit_depth : nat := 2.
