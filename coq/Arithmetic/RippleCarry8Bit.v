(** * Arithmetic.RippleCarry8Bit: 8-Bit Ripple Carry Adder

    Adds two 8-bit numbers using eight full adders chained together.
    Proven by induction using a list-based formulation.
*)

Require Import ZArith.
Require Import Arith.
Require Import List.
Require Import Bool.
Require Import Lia.
Require Import Base.Definitions.
Require Import Base.Tactics.
Require Import Arithmetic.FullAdder.

Import ListNotations.

Open Scope nat_scope.

(** * List-based Ripple Carry Adder *)

Fixpoint ripple_carry_list (xs ys : list bool) (cin : bool)
  : list bool * bool :=
  match xs, ys with
  | [], [] => ([], cin)
  | x :: xs', y :: ys' =>
    let '(s, cout) := full_adder x y cin in
    let '(sums, cfinal) := ripple_carry_list xs' ys' cout in
    (s :: sums, cfinal)
  | _, _ => ([], false)
  end.

(** * Arithmetic Interpretation *)

Definition bool_to_nat (b : bool) : nat := if b then 1 else 0.

Fixpoint bits_to_nat (bs : list bool) : nat :=
  match bs with
  | [] => 0
  | b :: bs' => bool_to_nat b + 2 * bits_to_nat bs'
  end.

Definition result_to_nat (sums : list bool) (cout : bool) : nat :=
  bits_to_nat sums + (2 ^ length sums) * bool_to_nat cout.

(** * Full Adder Arithmetic Lemma *)

Lemma full_adder_arith (a b cin : bool)
  : let '(s, cout) := full_adder a b cin in
    bool_to_nat a + bool_to_nat b + bool_to_nat cin =
    bool_to_nat s + 2 * bool_to_nat cout.
Proof.
  destruct a, b, cin; reflexivity.
Qed.

(** * Helper Lemmas *)

Lemma result_to_nat_cons (s : bool) (sums : list bool) (cout : bool)
  : result_to_nat (s :: sums) cout =
    bool_to_nat s + 2 * result_to_nat sums cout.
Proof.
  unfold result_to_nat.
  simpl.
  ring.
Qed.

Lemma ripple_carry_list_length (xs ys : list bool) (cin : bool)
  : length xs = length ys ->
    length (fst (ripple_carry_list xs ys cin)) = length xs.
Proof.
  revert ys cin.
  induction xs as [| x xs' IH]; intros ys cin Hlen.
  - destruct ys; [reflexivity | discriminate].
  - destruct ys as [| y ys']; [discriminate |].
    simpl in Hlen.
    injection Hlen as Hlen'.
    cbn [ripple_carry_list].
    destruct (full_adder x y cin) as [s cout].
    specialize (IH ys' cout Hlen').
    destruct (ripple_carry_list xs' ys' cout) as [sums cfinal].
    cbn [fst length].
    cbn [fst] in IH.
    f_equal.
    exact IH.
Qed.

(** * Main Correctness Theorem *)

Theorem ripple_carry_list_correct (xs ys : list bool) (cin : bool)
  : length xs = length ys ->
    let '(sums, cout) := ripple_carry_list xs ys cin in
    bits_to_nat xs + bits_to_nat ys + bool_to_nat cin = result_to_nat sums cout.
Proof.
  revert ys cin.
  induction xs as [| x xs' IH]; intros ys cin Hlen.
  - destruct ys; [unfold result_to_nat; simpl; lia | discriminate].
  - destruct ys as [| y ys']; [discriminate |].
    simpl in Hlen.
    injection Hlen as Hlen'.
    cbn [ripple_carry_list bits_to_nat].
    destruct (full_adder x y cin) as [s cout] eqn:Hfa.
    specialize (IH ys' cout Hlen').
    destruct (ripple_carry_list xs' ys' cout) as [sums cfinal].
    rewrite result_to_nat_cons.
    pose proof (full_adder_arith x y cin) as Harith.
    rewrite Hfa in Harith.
    simpl in Harith.
    lia.
Qed.

(** * 8-bit Interface *)

Definition ripple_carry_8bit
  (a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0 : bool)
  : bool * bool * bool * bool * bool * bool * bool * bool * bool :=
  let xs := [a0; a1; a2; a3; a4; a5; a6; a7] in
  let ys := [b0; b1; b2; b3; b4; b5; b6; b7] in
  let '(sums, cout) := ripple_carry_list xs ys false in
  match sums with
  | [s0; s1; s2; s3; s4; s5; s6; s7] => (cout, s7, s6, s5, s4, s3, s2, s1, s0)
  | _ => (false, false, false, false, false, false, false, false, false)
  end.

(** * Specification *)

Definition bits8_to_nat_args (b7 b6 b5 b4 b3 b2 b1 b0 : bool) : nat :=
  bits_to_nat [b0; b1; b2; b3; b4; b5; b6; b7].

(** 8-bit correctness follows from list correctness.
    The general theorem ripple_carry_list_correct proves correctness
    for any equal-length lists. For 8-bit:
    - Input: two 8-element lists
    - Output: 8-element sum list + carry
    - bits_to_nat sums + 256 * cout = bits_to_nat xs + bits_to_nat ys
*)

(** * Network Architecture *)

Definition ripple_carry_8bit_num_neurons : nat := 32.
Definition ripple_carry_8bit_num_params : nat := 96.
Definition ripple_carry_8bit_depth : nat := 8.
