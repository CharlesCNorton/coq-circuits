(** * Boolean.XNOR: XNOR Gate

    Formally verified XNOR gate (negated exclusive or, equivalence).
    XNOR is not linearly separable, so requires 2-layer network.
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Base.Definitions.
Require Import Base.Tactics.
Require Import Base.Verification.
Require Import Base.Composition.

Import ListNotations.

Open Scope Z_scope.

(** * Circuit Definition *)

(** XNOR requires 2 layers since it's not linearly separable.
    Layer 1: Compute NOR and AND in parallel.
    Layer 2: Compute OR of the two results.

    XNOR(x,y) = OR(NOR(x,y), AND(x,y))
*)

(** Layer 1, neuron 1: NOR gate *)
Definition xnor_layer1_neuron1
  : list Z * Z
  := ([-1; -1], 0).

(** Layer 1, neuron 2: AND gate *)
Definition xnor_layer1_neuron2
  : list Z * Z
  := ([1; 1], -2).

(** Layer 1: both neurons *)
Definition xnor_layer1
  : list (list Z * Z)
  := [xnor_layer1_neuron1; xnor_layer1_neuron2].

(** Layer 2: OR gate combining layer 1 outputs *)
Definition xnor_layer2_weights
  : list Z
  := [1; 1].

Definition xnor_layer2_bias
  : Z
  := -1.

(** XNOR circuit: 2-layer network *)
Definition xnor_circuit (x y : bool)
  : bool
  :=
  let layer1_out := layer xnor_layer1 [x; y] in
  gate xnor_layer2_weights xnor_layer2_bias layer1_out.

(** Extend to 8-bit input (operates on first two bits only). *)
Definition xnor_8bit (xs : list bool)
  : bool
  :=
  match xs with
  | x :: y :: _ => xnor_circuit x y
  | _ => false
  end.

(** * Specification *)

Definition xnor_spec (x y : bool)
  : bool
  := negb (xorb x y).

(** * Verification *)

(** XNOR circuit computes equivalence correctly. *)
Theorem xnor_correct
  : forall x y, xnor_circuit x y = xnor_spec x y.
Proof.
  intros x y.
  destruct x, y; reflexivity.
Qed.

(** Exhaustive verification on all four inputs. *)
Theorem xnor_exhaustive
  : xnor_circuit false false = true /\
    xnor_circuit false true = false /\
    xnor_circuit true false = false /\
    xnor_circuit true true = true.
Proof.
  repeat split; reflexivity.
Qed.

(** 8-bit version correct. *)
Theorem xnor_8bit_correct
  : forall x0 x1 x2 x3 x4 x5 x6 x7,
    xnor_8bit [x0; x1; x2; x3; x4; x5; x6; x7] = negb (xorb x0 x1).
Proof.
  intros.
  simpl.
  apply xnor_correct.
Qed.

(** * Properties *)

(** XNOR is commutative. *)
Lemma xnor_comm
  : forall x y, xnor_circuit x y = xnor_circuit y x.
Proof.
  intros x y.
  destruct x, y; reflexivity.
Qed.

(** XNOR with itself is true. *)
Lemma xnor_self
  : forall x, xnor_circuit x x = true.
Proof.
  intro x.
  destruct x; reflexivity.
Qed.

(** XNOR with false gives NOT. *)
Lemma xnor_false_r
  : forall x, xnor_circuit x false = negb x.
Proof.
  intro x.
  destruct x; reflexivity.
Qed.

(** XNOR with true is identity. *)
Lemma xnor_true_r
  : forall x, xnor_circuit x true = x.
Proof.
  intro x.
  destruct x; reflexivity.
Qed.

(** XNOR is equivalence relation (reflexive, symmetric). *)
Lemma xnor_reflexive
  : forall x, xnor_circuit x x = true.
Proof.
  intro x.
  destruct x; reflexivity.
Qed.

Lemma xnor_symmetric
  : forall x y, xnor_circuit x y = xnor_circuit y x.
Proof.
  intros x y.
  apply xnor_comm.
Qed.

(** * Length Safety *)

(** Layer 1 neurons have length 2 weights *)
Lemma xnor_layer1_neuron1_length
  : length (fst xnor_layer1_neuron1) = 2%nat.
Proof. reflexivity. Qed.

Lemma xnor_layer1_neuron2_length
  : length (fst xnor_layer1_neuron2) = 2%nat.
Proof. reflexivity. Qed.

(** Layer 2 has length 2 weights *)
Lemma xnor_layer2_weights_length
  : length xnor_layer2_weights = 2%nat.
Proof. reflexivity. Qed.

(** XNOR requires exactly 2 inputs for layer 1 *)
Theorem xnor_layer1_length_requirement (x y : bool)
  : gate_length_ok (fst xnor_layer1_neuron1) [x; y] /\
    gate_length_ok (fst xnor_layer1_neuron2) [x; y].
Proof.
  split; unfold gate_length_ok;
  [ rewrite xnor_layer1_neuron1_length | rewrite xnor_layer1_neuron2_length ];
  reflexivity.
Qed.

(** XNOR layer 2 requires exactly 2 inputs (from layer 1 outputs) *)
Theorem xnor_layer2_length_requirement (b1 b2 : bool)
  : gate_length_ok xnor_layer2_weights [b1; b2].
Proof.
  unfold gate_length_ok.
  rewrite xnor_layer2_weights_length.
  reflexivity.
Qed.

(** * Network Architecture *)

(** Total parameters: 9 (Layer 1: 2*(2 weights + 1 bias) = 6, Layer 2: 2 weights + 1 bias = 3) *)
Definition xnor_num_params : nat := 9.

(** Number of neurons: 3 (2 in layer 1, 1 in layer 2) *)
Definition xnor_num_neurons : nat := 3.

(** Network depth: 2 layers *)
Definition xnor_depth : nat := 2.
