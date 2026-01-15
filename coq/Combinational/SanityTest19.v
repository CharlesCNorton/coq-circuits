(** * Combinational.SanityTest19: Decoder ∘ Encoder = Identity

    Sanity Test 19: Verify Decoder(Encoder(one-hot)) = one-hot.

    This demonstrates:
    1. Encoder converts one-hot to binary
    2. Decoder converts binary to one-hot
    3. Composition is identity on valid one-hot inputs
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Base.Definitions.
Require Import Base.Tactics.
Require Import Combinational.Encoder8to3.
Require Import Combinational.Decoder3to8.

Import ListNotations.

(** * Sanity Test 19: Decoder(Encoder(i)) = i for one-hot inputs *)

(** Roundtrip for position 0: 100... -> 000 -> 100... *)
Theorem sanity_test_19_roundtrip_0
  : let input := (true, false, false, false, false, false, false, false) in
    let '(b2, b1, b0) := encoder8to3 true false false false false false false false in
    decoder3to8 b2 b1 b0 = input.
Proof.
  reflexivity.
Qed.

(** Roundtrip for position 1: 010... -> 001 -> 010... *)
Theorem sanity_test_19_roundtrip_1
  : let '(b2, b1, b0) := encoder8to3 false true false false false false false false in
    decoder3to8 b2 b1 b0 = (false, true, false, false, false, false, false, false).
Proof.
  reflexivity.
Qed.

(** Roundtrip for position 2: 001... -> 010 -> 001... *)
Theorem sanity_test_19_roundtrip_2
  : let '(b2, b1, b0) := encoder8to3 false false true false false false false false in
    decoder3to8 b2 b1 b0 = (false, false, true, false, false, false, false, false).
Proof.
  reflexivity.
Qed.

(** Roundtrip for position 3 *)
Theorem sanity_test_19_roundtrip_3
  : let '(b2, b1, b0) := encoder8to3 false false false true false false false false in
    decoder3to8 b2 b1 b0 = (false, false, false, true, false, false, false, false).
Proof.
  reflexivity.
Qed.

(** Roundtrip for position 4 *)
Theorem sanity_test_19_roundtrip_4
  : let '(b2, b1, b0) := encoder8to3 false false false false true false false false in
    decoder3to8 b2 b1 b0 = (false, false, false, false, true, false, false, false).
Proof.
  reflexivity.
Qed.

(** Roundtrip for position 5 *)
Theorem sanity_test_19_roundtrip_5
  : let '(b2, b1, b0) := encoder8to3 false false false false false true false false in
    decoder3to8 b2 b1 b0 = (false, false, false, false, false, true, false, false).
Proof.
  reflexivity.
Qed.

(** Roundtrip for position 6 *)
Theorem sanity_test_19_roundtrip_6
  : let '(b2, b1, b0) := encoder8to3 false false false false false false true false in
    decoder3to8 b2 b1 b0 = (false, false, false, false, false, false, true, false).
Proof.
  reflexivity.
Qed.

(** Roundtrip for position 7 *)
Theorem sanity_test_19_roundtrip_7
  : let '(b2, b1, b0) := encoder8to3 false false false false false false false true in
    decoder3to8 b2 b1 b0 = (false, false, false, false, false, false, false, true).
Proof.
  reflexivity.
Qed.

(** Encoder produces correct binary for each one-hot position *)
Theorem sanity_test_19_encoder_values
  : encoder8to3 true false false false false false false false = (false, false, false) /\
    encoder8to3 false true false false false false false false = (false, false, true) /\
    encoder8to3 false false true false false false false false = (false, true, false) /\
    encoder8to3 false false false true false false false false = (false, true, true) /\
    encoder8to3 false false false false true false false false = (true, false, false) /\
    encoder8to3 false false false false false true false false = (true, false, true) /\
    encoder8to3 false false false false false false true false = (true, true, false) /\
    encoder8to3 false false false false false false false true = (true, true, true).
Proof.
  repeat split; reflexivity.
Qed.

(** SANITY TEST 19 PASSES: Decoder ∘ Encoder = Identity on one-hot inputs *)
Theorem sanity_test_19_complete
  : (let '(b2, b1, b0) := encoder8to3 true false false false false false false false in
     decoder3to8 b2 b1 b0 = (true, false, false, false, false, false, false, false)) /\
    (let '(b2, b1, b0) := encoder8to3 false true false false false false false false in
     decoder3to8 b2 b1 b0 = (false, true, false, false, false, false, false, false)) /\
    (let '(b2, b1, b0) := encoder8to3 false false true false false false false false in
     decoder3to8 b2 b1 b0 = (false, false, true, false, false, false, false, false)) /\
    (let '(b2, b1, b0) := encoder8to3 false false false true false false false false in
     decoder3to8 b2 b1 b0 = (false, false, false, true, false, false, false, false)) /\
    (let '(b2, b1, b0) := encoder8to3 false false false false true false false false in
     decoder3to8 b2 b1 b0 = (false, false, false, false, true, false, false, false)) /\
    (let '(b2, b1, b0) := encoder8to3 false false false false false true false false in
     decoder3to8 b2 b1 b0 = (false, false, false, false, false, true, false, false)) /\
    (let '(b2, b1, b0) := encoder8to3 false false false false false false true false in
     decoder3to8 b2 b1 b0 = (false, false, false, false, false, false, true, false)) /\
    (let '(b2, b1, b0) := encoder8to3 false false false false false false false true in
     decoder3to8 b2 b1 b0 = (false, false, false, false, false, false, false, true)).
Proof.
  repeat split; reflexivity.
Qed.
