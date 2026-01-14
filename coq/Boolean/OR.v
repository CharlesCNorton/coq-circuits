(** * Boolean.OR: OR Gate

    Formally verified OR gate (two-input disjunction).
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

(** OR gate weights: [1, 1]. *)
Definition or_weights
  : list Z
  := [1; 1].

(** OR gate bias: -1. *)
Definition or_bias
  : Z
  := -1.

(** OR gate: threshold neuron computing disjunction.
    Fires when at least one input is true: 1 + 0 - 1 = 0 >= 0. *)
Definition or_circuit (x y : bool)
  : bool
  := gate or_weights or_bias [x; y].

(** Extend to 8-bit input (operates on first two bits only). *)
Definition or_8bit (xs : list bool)
  : bool
  :=
  match xs with
  | x :: y :: _ => or_circuit x y
  | _ => false
  end.

(** * Specification *)

Definition or_spec (x y : bool)
  : bool
  := orb x y.

(** * Verification *)

(** OR circuit computes disjunction correctly. *)
Theorem or_correct
  : forall x y, or_circuit x y = or_spec x y.
Proof.
  intros x y.
  destruct x, y; reflexivity.
Qed.

(** Exhaustive verification on all four inputs. *)
Theorem or_exhaustive
  : or_circuit false false = false /\
    or_circuit false true = true /\
    or_circuit true false = true /\
    or_circuit true true = true.
Proof.
  repeat split; reflexivity.
Qed.

(** 8-bit version correct. *)
Theorem or_8bit_correct
  : forall x0 x1 x2 x3 x4 x5 x6 x7,
    or_8bit [x0; x1; x2; x3; x4; x5; x6; x7] = orb x0 x1.
Proof.
  intros.
  simpl.
  apply or_correct.
Qed.

(** * Properties *)

(** OR is commutative. *)
Lemma or_comm
  : forall x y, or_circuit x y = or_circuit y x.
Proof.
  intros x y.
  destruct x, y; reflexivity.
Qed.

(** OR is associative. *)
Lemma or_assoc
  : forall x y z,
    or_circuit x (or_circuit y z) = or_circuit (or_circuit x y) z.
Proof.
  intros x y z.
  destruct x, y, z; reflexivity.
Qed.

(** OR with false is identity. *)
Lemma or_false_r
  : forall x, or_circuit x false = x.
Proof.
  intro x.
  destruct x; reflexivity.
Qed.

(** OR with true is absorption. *)
Lemma or_true_r
  : forall x, or_circuit x true = true.
Proof.
  intro x.
  destruct x; reflexivity.
Qed.

(** OR is idempotent. *)
Lemma or_idem
  : forall x, or_circuit x x = x.
Proof.
  intro x.
  destruct x; reflexivity.
Qed.

(** * Length Safety *)

(** OR weights have length 2 *)
Lemma or_weights_length
  : length or_weights = 2%nat.
Proof. reflexivity. Qed.

(** OR requires exactly 2 inputs *)
Theorem or_length_requirement (x y : bool)
  : gate_length_ok or_weights [x; y].
Proof.
  unfold gate_length_ok.
  rewrite or_weights_length.
  reflexivity.
Qed.

(** Length-safe OR circuit *)
Definition or_circuit_safe (x y : bool)
  : bool
  := gate_safe or_weights or_bias [x; y] (or_length_requirement x y).

(** Safe version equivalent to unsafe version *)
Theorem or_safe_equiv (x y : bool)
  : or_circuit_safe x y = or_circuit x y.
Proof.
  unfold or_circuit_safe, gate_safe.
  reflexivity.
Qed.

(** * Network Architecture *)

(** Total parameters: 3 (2 weights + 1 bias). *)
Definition or_num_params : nat := 3.
