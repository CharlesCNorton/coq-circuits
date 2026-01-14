(** * Boolean.AND: AND Gate

    Formally verified AND gate (two-input conjunction).
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

(** AND gate weights: [1, 1]. *)
Definition and_weights
  : list Z
  := [1; 1].

(** AND gate bias: -2. *)
Definition and_bias
  : Z
  := -2.

(** AND gate: threshold neuron computing conjunction.
    Fires when both inputs are true: 1 + 1 - 2 = 0 >= 0. *)
Definition and_circuit (x y : bool)
  : bool
  := gate and_weights and_bias [x; y].

(** Extend to 8-bit input (operates on first two bits only). *)
Definition and_8bit (xs : list bool)
  : bool
  :=
  match xs with
  | x :: y :: _ => and_circuit x y
  | _ => false
  end.

(** * Specification *)

Definition and_spec (x y : bool)
  : bool
  := andb x y.

(** * Verification *)

(** AND circuit computes conjunction correctly. *)
Theorem and_correct
  : forall x y, and_circuit x y = and_spec x y.
Proof.
  intros x y.
  destruct x, y; reflexivity.
Qed.

(** Exhaustive verification on all four inputs. *)
Theorem and_exhaustive
  : and_circuit false false = false /\
    and_circuit false true = false /\
    and_circuit true false = false /\
    and_circuit true true = true.
Proof.
  repeat split; reflexivity.
Qed.

(** 8-bit version correct. *)
Theorem and_8bit_correct
  : forall x0 x1 x2 x3 x4 x5 x6 x7,
    and_8bit [x0; x1; x2; x3; x4; x5; x6; x7] = andb x0 x1.
Proof.
  intros.
  simpl.
  apply and_correct.
Qed.

(** * Properties *)

(** AND is commutative. *)
Lemma and_comm
  : forall x y, and_circuit x y = and_circuit y x.
Proof.
  intros x y.
  destruct x, y; reflexivity.
Qed.

(** AND is associative. *)
Lemma and_assoc
  : forall x y z,
    and_circuit x (and_circuit y z) = and_circuit (and_circuit x y) z.
Proof.
  intros x y z.
  destruct x, y, z; reflexivity.
Qed.

(** AND with true is identity. *)
Lemma and_true_r
  : forall x, and_circuit x true = x.
Proof.
  intro x.
  destruct x; reflexivity.
Qed.

(** AND with false is absorption. *)
Lemma and_false_r
  : forall x, and_circuit x false = false.
Proof.
  intro x.
  destruct x; reflexivity.
Qed.

(** AND is idempotent. *)
Lemma and_idem
  : forall x, and_circuit x x = x.
Proof.
  intro x.
  destruct x; reflexivity.
Qed.

(** * Length Safety *)

(** AND weights have length 2 *)
Lemma and_weights_length
  : length and_weights = 2%nat.
Proof. reflexivity. Qed.

(** AND requires exactly 2 inputs *)
Theorem and_length_requirement (x y : bool)
  : gate_length_ok and_weights [x; y].
Proof.
  unfold gate_length_ok.
  rewrite and_weights_length.
  reflexivity.
Qed.

(** Length-safe AND circuit *)
Definition and_circuit_safe (x y : bool)
  : bool
  := gate_safe and_weights and_bias [x; y] (and_length_requirement x y).

(** Safe version equivalent to unsafe version when lengths match *)
Theorem and_safe_equiv (x y : bool)
  : and_circuit_safe x y = and_circuit x y.
Proof.
  unfold and_circuit_safe, gate_safe.
  reflexivity.
Qed.

(** * Network Architecture *)

(** Total parameters: 3 (2 weights + 1 bias). *)
Definition and_num_params : nat := 3.
