(** * Arithmetic.HalfAdder: Half Adder Circuit

    Adds two 1-bit inputs, producing sum and carry.
    sum = a XOR b
    carry = a AND b
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Base.Definitions.
Require Import Base.Tactics.
Require Import Base.Composition.
Require Import Boolean.XOR.
Require Import Boolean.AND.

Import ListNotations.

Open Scope Z_scope.

(** * Circuit Definition *)

(** Half adder produces two outputs: sum and carry *)
Definition half_adder_sum (a b : bool) : bool :=
  xor_circuit a b.

Definition half_adder_carry (a b : bool) : bool :=
  and_circuit a b.

(** Pair output *)
Definition half_adder (a b : bool) : bool * bool :=
  (half_adder_sum a b, half_adder_carry a b).

(** * Specification *)

Definition half_adder_sum_spec (a b : bool) : bool :=
  xorb a b.

Definition half_adder_carry_spec (a b : bool) : bool :=
  andb a b.

Definition half_adder_spec (a b : bool) : bool * bool :=
  (half_adder_sum_spec a b, half_adder_carry_spec a b).

(** * Verification *)

Theorem half_adder_sum_correct
  : forall a b, half_adder_sum a b = half_adder_sum_spec a b.
Proof.
  intros a b.
  unfold half_adder_sum, half_adder_sum_spec.
  apply xor_correct.
Qed.

Theorem half_adder_carry_correct
  : forall a b, half_adder_carry a b = half_adder_carry_spec a b.
Proof.
  intros a b.
  unfold half_adder_carry, half_adder_carry_spec.
  apply and_correct.
Qed.

Theorem half_adder_correct
  : forall a b, half_adder a b = half_adder_spec a b.
Proof.
  intros a b.
  unfold half_adder, half_adder_spec.
  rewrite half_adder_sum_correct.
  rewrite half_adder_carry_correct.
  reflexivity.
Qed.

(** Exhaustive verification *)
Theorem half_adder_exhaustive
  : half_adder false false = (false, false) /\
    half_adder false true = (true, false) /\
    half_adder true false = (true, false) /\
    half_adder true true = (false, true).
Proof.
  repeat split; reflexivity.
Qed.

(** * Properties *)

(** Half adder is commutative *)
Lemma half_adder_comm
  : forall a b, half_adder a b = half_adder b a.
Proof.
  intros a b.
  unfold half_adder, half_adder_sum, half_adder_carry.
  rewrite xor_comm.
  rewrite and_comm.
  reflexivity.
Qed.

(** Adding zero *)
Lemma half_adder_zero_l
  : forall a, half_adder false a = (a, false).
Proof.
  intro a.
  destruct a; reflexivity.
Qed.

Lemma half_adder_zero_r
  : forall a, half_adder a false = (a, false).
Proof.
  intro a.
  destruct a; reflexivity.
Qed.

(** Adding to itself produces carry *)
Lemma half_adder_self
  : forall a, half_adder a a = (false, a).
Proof.
  intro a.
  destruct a; reflexivity.
Qed.

(** * Network Architecture *)

(** Half adder uses XOR (2-layer, 9 params) + AND (1-layer, 3 params) in parallel *)
Definition half_adder_num_neurons : nat := 4.  (* 3 for XOR + 1 for AND *)
Definition half_adder_num_params : nat := 12.  (* 9 + 3 *)
Definition half_adder_depth : nat := 2.        (* Max depth is XOR's 2 layers *)
