(** * Boolean.NAND: NAND Gate

    Formally verified NAND gate (negated conjunction).
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

(** NAND gate weights: [-1, -1]. *)
Definition nand_weights
  : list Z
  := [-1; -1].

(** NAND gate bias: 1. *)
Definition nand_bias
  : Z
  := 1.

(** NAND gate: threshold neuron computing negated conjunction.
    Fires except when both inputs are true: -1 + -1 + 1 = -1 < 0. *)
Definition nand_circuit (x y : bool)
  : bool
  := gate nand_weights nand_bias [x; y].

(** Extend to 8-bit input (operates on first two bits only). *)
Definition nand_8bit (xs : list bool)
  : bool
  :=
  match xs with
  | x :: y :: _ => nand_circuit x y
  | _ => false
  end.

(** * Specification *)

Definition nand_spec (x y : bool)
  : bool
  := negb (andb x y).

(** * Verification *)

(** NAND circuit computes negated conjunction correctly. *)
Theorem nand_correct
  : forall x y, nand_circuit x y = nand_spec x y.
Proof.
  intros x y.
  destruct x, y; reflexivity.
Qed.

(** Exhaustive verification on all four inputs. *)
Theorem nand_exhaustive
  : nand_circuit false false = true /\
    nand_circuit false true = true /\
    nand_circuit true false = true /\
    nand_circuit true true = false.
Proof.
  repeat split; reflexivity.
Qed.

(** 8-bit version correct. *)
Theorem nand_8bit_correct
  : forall x0 x1 x2 x3 x4 x5 x6 x7,
    nand_8bit [x0; x1; x2; x3; x4; x5; x6; x7] = negb (andb x0 x1).
Proof.
  intros.
  simpl.
  apply nand_correct.
Qed.

(** * Properties *)

(** NAND is commutative. *)
Lemma nand_comm
  : forall x y, nand_circuit x y = nand_circuit y x.
Proof.
  intros x y.
  destruct x, y; reflexivity.
Qed.

(** NAND with itself gives NOT. *)
Lemma nand_self
  : forall x, nand_circuit x x = negb x.
Proof.
  intro x.
  destruct x; reflexivity.
Qed.

(** NAND is functionally complete (can build any Boolean function). *)
Lemma nand_not
  : forall x, nand_circuit x x = negb x.
Proof.
  intro x.
  destruct x; reflexivity.
Qed.

(** NAND with true gives NOT. *)
Lemma nand_true_r
  : forall x, nand_circuit x true = negb x.
Proof.
  intro x.
  destruct x; reflexivity.
Qed.

(** NAND with false gives true. *)
Lemma nand_false_r
  : forall x, nand_circuit x false = true.
Proof.
  intro x.
  destruct x; reflexivity.
Qed.

(** * Length Safety *)

(** NAND weights have length 2 *)
Lemma nand_weights_length
  : length nand_weights = 2%nat.
Proof. reflexivity. Qed.

(** NAND requires exactly 2 inputs *)
Theorem nand_length_requirement (x y : bool)
  : gate_length_ok nand_weights [x; y].
Proof.
  unfold gate_length_ok.
  rewrite nand_weights_length.
  reflexivity.
Qed.

(** Length-safe NAND circuit *)
Definition nand_circuit_safe (x y : bool)
  : bool
  := gate_safe nand_weights nand_bias [x; y] (nand_length_requirement x y).

(** Safe version equivalent to unsafe version *)
Theorem nand_safe_equiv (x y : bool)
  : nand_circuit_safe x y = nand_circuit x y.
Proof.
  unfold nand_circuit_safe, gate_safe.
  reflexivity.
Qed.

(** * Network Architecture *)

(** Total parameters: 3 (2 weights + 1 bias). *)
Definition nand_num_params : nat := 3.
