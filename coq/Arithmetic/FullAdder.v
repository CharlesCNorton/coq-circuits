(** * Arithmetic.FullAdder: Full Adder Circuit

    Adds three 1-bit inputs (a, b, carry_in), producing sum and carry_out.
    Composed from two half adders and an OR gate.
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Base.Definitions.
Require Import Base.Tactics.
Require Import Base.Composition.
Require Import Boolean.OR.
Require Import Boolean.XOR.
Require Import Boolean.AND.
Require Import Arithmetic.HalfAdder.

Import ListNotations.

Open Scope Z_scope.

(** * Circuit Definition *)

(** Full adder using two half adders:
    HA1: (a, b) -> (s1, c1)
    HA2: (s1, carry_in) -> (sum, c2)
    carry_out = c1 OR c2
*)

Definition full_adder_sum (a b carry_in : bool) : bool :=
  let '(s1, c1) := half_adder a b in
  let '(sum, c2) := half_adder s1 carry_in in
  sum.

Definition full_adder_carry (a b carry_in : bool) : bool :=
  let '(s1, c1) := half_adder a b in
  let '(sum, c2) := half_adder s1 carry_in in
  or_circuit c1 c2.

Definition full_adder (a b carry_in : bool) : bool * bool :=
  (full_adder_sum a b carry_in, full_adder_carry a b carry_in).

(** * Specification *)

Definition full_adder_sum_spec (a b carry_in : bool) : bool :=
  xorb (xorb a b) carry_in.

Definition full_adder_carry_spec (a b carry_in : bool) : bool :=
  orb (andb a b) (andb carry_in (xorb a b)).

Definition full_adder_spec (a b carry_in : bool) : bool * bool :=
  (full_adder_sum_spec a b carry_in, full_adder_carry_spec a b carry_in).

(** * Verification *)

Theorem full_adder_sum_correct
  : forall a b c, full_adder_sum a b c = full_adder_sum_spec a b c.
Proof.
  intros a b c.
  unfold full_adder_sum, full_adder_sum_spec.
  unfold half_adder, half_adder_sum, half_adder_carry.
  unfold xor_circuit, and_circuit.
  destruct a, b, c; reflexivity.
Qed.

Theorem full_adder_carry_correct
  : forall a b c, full_adder_carry a b c = full_adder_carry_spec a b c.
Proof.
  intros a b c.
  unfold full_adder_carry, full_adder_carry_spec.
  unfold half_adder, half_adder_sum, half_adder_carry.
  unfold xor_circuit, and_circuit, or_circuit.
  destruct a, b, c; reflexivity.
Qed.

Theorem full_adder_correct
  : forall a b c, full_adder a b c = full_adder_spec a b c.
Proof.
  intros a b c.
  unfold full_adder, full_adder_spec.
  rewrite full_adder_sum_correct.
  rewrite full_adder_carry_correct.
  reflexivity.
Qed.

(** Exhaustive verification *)
Theorem full_adder_exhaustive
  : full_adder false false false = (false, false) /\
    full_adder false false true = (true, false) /\
    full_adder false true false = (true, false) /\
    full_adder false true true = (false, true) /\
    full_adder true false false = (true, false) /\
    full_adder true false true = (false, true) /\
    full_adder true true false = (false, true) /\
    full_adder true true true = (true, true).
Proof.
  repeat split; reflexivity.
Qed.

(** * Properties *)

(** Full adder is commutative in first two arguments *)
Lemma full_adder_comm_ab
  : forall a b c, full_adder a b c = full_adder b a c.
Proof.
  intros a b c.
  destruct a, b, c; reflexivity.
Qed.

(** Adding with zero carry *)
Lemma full_adder_no_carry
  : forall a b, full_adder a b false = half_adder a b.
Proof.
  intros a b.
  destruct a, b; reflexivity.
Qed.

(** * Network Architecture *)

(** Full adder: 2 half adders + 1 OR gate
    Each half adder: 4 neurons, 12 params
    OR gate: 1 neuron, 3 params
    Total: 9 neurons, 27 params
*)
Definition full_adder_num_neurons : nat := 9.
Definition full_adder_num_params : nat := 27.
Definition full_adder_depth : nat := 3.  (* Max depth through both half adders *)
