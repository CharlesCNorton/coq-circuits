(** * Boolean.NOR: NOR Gate

    Formally verified NOR gate (negated disjunction).
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Base.Definitions.
Require Import Base.Tactics.
Require Import Base.Verification.

Import ListNotations.

Open Scope Z_scope.

(** * Circuit Definition *)

(** NOR gate weights: [-1, -1]. *)
Definition nor_weights
  : list Z
  := [-1; -1].

(** NOR gate bias: 0. *)
Definition nor_bias
  : Z
  := 0.

(** NOR gate: threshold neuron computing negated disjunction.
    Fires only when both inputs are false: 0 + 0 + 0 = 0 >= 0. *)
Definition nor_circuit (x y : bool)
  : bool
  := gate nor_weights nor_bias [x; y].

(** Extend to 8-bit input (operates on first two bits only). *)
Definition nor_8bit (xs : list bool)
  : bool
  :=
  match xs with
  | x :: y :: _ => nor_circuit x y
  | _ => false
  end.

(** * Specification *)

Definition nor_spec (x y : bool)
  : bool
  := negb (orb x y).

(** * Verification *)

(** NOR circuit computes negated disjunction correctly. *)
Theorem nor_correct
  : forall x y, nor_circuit x y = nor_spec x y.
Proof.
  intros x y.
  destruct x, y; reflexivity.
Qed.

(** Exhaustive verification on all four inputs. *)
Theorem nor_exhaustive
  : nor_circuit false false = true /\
    nor_circuit false true = false /\
    nor_circuit true false = false /\
    nor_circuit true true = false.
Proof.
  repeat split; reflexivity.
Qed.

(** 8-bit version correct. *)
Theorem nor_8bit_correct
  : forall x0 x1 x2 x3 x4 x5 x6 x7,
    nor_8bit [x0; x1; x2; x3; x4; x5; x6; x7] = negb (orb x0 x1).
Proof.
  intros.
  simpl.
  apply nor_correct.
Qed.

(** * Properties *)

(** NOR is commutative. *)
Lemma nor_comm
  : forall x y, nor_circuit x y = nor_circuit y x.
Proof.
  intros x y.
  destruct x, y; reflexivity.
Qed.

(** NOR with itself gives NOT. *)
Lemma nor_self
  : forall x, nor_circuit x x = negb x.
Proof.
  intro x.
  destruct x; reflexivity.
Qed.

(** NOR is functionally complete (can build any Boolean function). *)
Lemma nor_not
  : forall x, nor_circuit x x = negb x.
Proof.
  intro x.
  destruct x; reflexivity.
Qed.

(** NOR with false gives NOT. *)
Lemma nor_false_r
  : forall x, nor_circuit x false = negb x.
Proof.
  intro x.
  destruct x; reflexivity.
Qed.

(** NOR with true gives false. *)
Lemma nor_true_r
  : forall x, nor_circuit x true = false.
Proof.
  intro x.
  destruct x; reflexivity.
Qed.

(** * Length Safety *)

(** NOR weights have length 2 *)
Lemma nor_weights_length
  : length nor_weights = 2%nat.
Proof. reflexivity. Qed.

(** NOR requires exactly 2 inputs *)
Theorem nor_length_requirement (x y : bool)
  : gate_length_ok nor_weights [x; y].
Proof.
  unfold gate_length_ok.
  rewrite nor_weights_length.
  reflexivity.
Qed.

(** Length-safe NOR circuit *)
Definition nor_circuit_safe (x y : bool)
  : bool
  := gate_safe nor_weights nor_bias [x; y] (nor_length_requirement x y).

(** Safe version equivalent to unsafe version *)
Theorem nor_safe_equiv (x y : bool)
  : nor_circuit_safe x y = nor_circuit x y.
Proof.
  unfold nor_circuit_safe, gate_safe.
  reflexivity.
Qed.

(** * Network Architecture *)

(** Total parameters: 3 (2 weights + 1 bias). *)
Definition nor_num_params : nat := 3.
