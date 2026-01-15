(** * Arithmetic.Equality8Bit: 8-Bit Equality Comparator

    Fires when two 8-bit numbers are equal.
    Implemented as AND of 8 XNOR gates.
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Lia.
Require Import Base.Definitions.
Require Import Base.Tactics.
Require Import Base.Verification.
Require Import Boolean.XNOR.

Import ListNotations.

Open Scope Z_scope.

(** * Circuit Definition *)

(** Equality: all bits must match.
    Each bit position uses XNOR (equivalence).
    Final AND combines all 8 bit comparisons. *)

Definition eq_bit (a b : bool) : bool := xnor_circuit a b.

Definition equality_8bit
  (a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0 : bool) : bool :=
  andb (eq_bit a7 b7)
  (andb (eq_bit a6 b6)
  (andb (eq_bit a5 b5)
  (andb (eq_bit a4 b4)
  (andb (eq_bit a3 b3)
  (andb (eq_bit a2 b2)
  (andb (eq_bit a1 b1)
        (eq_bit a0 b0))))))).

(** * Specification *)

Definition equality_8bit_spec
  (a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0 : bool) : bool :=
  andb (Bool.eqb a7 b7)
  (andb (Bool.eqb a6 b6)
  (andb (Bool.eqb a5 b5)
  (andb (Bool.eqb a4 b4)
  (andb (Bool.eqb a3 b3)
  (andb (Bool.eqb a2 b2)
  (andb (Bool.eqb a1 b1)
        (Bool.eqb a0 b0))))))).

(** * Verification *)

Theorem eq_bit_correct
  : forall a b, eq_bit a b = Bool.eqb a b.
Proof.
  intros.
  unfold eq_bit, xnor_circuit.
  destruct a, b; reflexivity.
Qed.

Theorem equality_8bit_correct
  : forall a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0,
    equality_8bit a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0 =
    equality_8bit_spec a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0.
Proof.
  intros.
  unfold equality_8bit, equality_8bit_spec.
  repeat rewrite eq_bit_correct.
  reflexivity.
Qed.

(** * Properties *)

Lemma equality_same
  : forall a7 a6 a5 a4 a3 a2 a1 a0,
    equality_8bit a7 a6 a5 a4 a3 a2 a1 a0 a7 a6 a5 a4 a3 a2 a1 a0 = true.
Proof.
  intros.
  unfold equality_8bit, eq_bit.
  rewrite xnor_self, xnor_self, xnor_self, xnor_self.
  rewrite xnor_self, xnor_self, xnor_self, xnor_self.
  reflexivity.
Qed.

Lemma equality_zeros
  : equality_8bit false false false false false false false false
                  false false false false false false false false = true.
Proof. reflexivity. Qed.

Lemma equality_ones
  : equality_8bit true true true true true true true true
                  true true true true true true true true = true.
Proof. reflexivity. Qed.

Lemma equality_one_diff
  : equality_8bit true false false false false false false false
                  false false false false false false false false = false.
Proof. reflexivity. Qed.

(** Symmetry: A = B iff B = A *)
Lemma equality_symmetric
  : forall a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0,
    equality_8bit a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0 =
    equality_8bit b7 b6 b5 b4 b3 b2 b1 b0 a7 a6 a5 a4 a3 a2 a1 a0.
Proof.
  intros.
  unfold equality_8bit, eq_bit.
  rewrite (xnor_comm a7 b7), (xnor_comm a6 b6).
  rewrite (xnor_comm a5 b5), (xnor_comm a4 b4).
  rewrite (xnor_comm a3 b3), (xnor_comm a2 b2).
  rewrite (xnor_comm a1 b1), (xnor_comm a0 b0).
  reflexivity.
Qed.

(** * Network Architecture *)

(** 8 XNOR gates (3 neurons each) + 7 AND gates for combining *)
Definition equality_8bit_num_neurons : nat := 31.
Definition equality_8bit_num_params : nat := 93.
Definition equality_8bit_depth : nat := 4.
