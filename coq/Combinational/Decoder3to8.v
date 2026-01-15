(** * Combinational.Decoder3to8: 3-to-8 Decoder

    Decodes 3-bit binary input to 8 one-hot outputs.

    o_i = 1 iff (b2,b1,b0) = binary(i)
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

Definition and3 (a b c : bool) : bool :=
  and_circuit (and_circuit a b) c.

Definition decoder3to8 (b2 b1 b0 : bool)
  : bool * bool * bool * bool * bool * bool * bool * bool :=
  let nb2 := not_circuit b2 in
  let nb1 := not_circuit b1 in
  let nb0 := not_circuit b0 in
  let o0 := and3 nb2 nb1 nb0 in
  let o1 := and3 nb2 nb1 b0 in
  let o2 := and3 nb2 b1 nb0 in
  let o3 := and3 nb2 b1 b0 in
  let o4 := and3 b2 nb1 nb0 in
  let o5 := and3 b2 nb1 b0 in
  let o6 := and3 b2 b1 nb0 in
  let o7 := and3 b2 b1 b0 in
  (o0, o1, o2, o3, o4, o5, o6, o7).

(** * Specification *)

Definition decoder3to8_spec (b2 b1 b0 : bool)
  : bool * bool * bool * bool * bool * bool * bool * bool :=
  match b2, b1, b0 with
  | false, false, false => (true, false, false, false, false, false, false, false)
  | false, false, true => (false, true, false, false, false, false, false, false)
  | false, true, false => (false, false, true, false, false, false, false, false)
  | false, true, true => (false, false, false, true, false, false, false, false)
  | true, false, false => (false, false, false, false, true, false, false, false)
  | true, false, true => (false, false, false, false, false, true, false, false)
  | true, true, false => (false, false, false, false, false, false, true, false)
  | true, true, true => (false, false, false, false, false, false, false, true)
  end.

(** * Verification *)

Theorem decoder3to8_correct
  : forall b2 b1 b0, decoder3to8 b2 b1 b0 = decoder3to8_spec b2 b1 b0.
Proof.
  intros.
  unfold decoder3to8, decoder3to8_spec.
  destruct b2, b1, b0; reflexivity.
Qed.

(** Each output is one-hot *)
Theorem decoder3to8_onehot
  : forall b2 b1 b0,
    let '(o0, o1, o2, o3, o4, o5, o6, o7) := decoder3to8 b2 b1 b0 in
    (if o0 then 1 else 0) + (if o1 then 1 else 0) +
    (if o2 then 1 else 0) + (if o3 then 1 else 0) +
    (if o4 then 1 else 0) + (if o5 then 1 else 0) +
    (if o6 then 1 else 0) + (if o7 then 1 else 0) = 1.
Proof.
  intros.
  destruct b2, b1, b0; reflexivity.
Qed.

(** * Network Architecture *)

Definition decoder3to8_num_neurons : nat := 19.
Definition decoder3to8_num_params : nat := 57.
Definition decoder3to8_depth : nat := 3.
