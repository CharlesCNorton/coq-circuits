(** * Boolean.XOR: XOR Gate

    Formally verified XOR gate (exclusive or).
    XOR is not linearly separable, so requires 2-layer network.
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

(** XOR requires 2 layers since it's not linearly separable.
    Layer 1: Compute OR and NAND in parallel.
    Layer 2: Compute AND of the two results.

    XOR(x,y) = AND(OR(x,y), NAND(x,y))
*)

(** Layer 1, neuron 1: OR gate *)
Definition xor_layer1_neuron1
  : list Z * Z
  := ([1; 1], -1).

(** Layer 1, neuron 2: NAND gate *)
Definition xor_layer1_neuron2
  : list Z * Z
  := ([-1; -1], 1).

(** Layer 1: both neurons *)
Definition xor_layer1
  : list (list Z * Z)
  := [xor_layer1_neuron1; xor_layer1_neuron2].

(** Layer 2: AND gate combining layer 1 outputs *)
Definition xor_layer2_weights
  : list Z
  := [1; 1].

Definition xor_layer2_bias
  : Z
  := -2.

(** XOR circuit: 2-layer network *)
Definition xor_circuit (x y : bool)
  : bool
  :=
  let layer1_out := layer xor_layer1 [x; y] in
  gate xor_layer2_weights xor_layer2_bias layer1_out.

(** Extend to 8-bit input (operates on first two bits only). *)
Definition xor_8bit (xs : list bool)
  : bool
  :=
  match xs with
  | x :: y :: _ => xor_circuit x y
  | _ => false
  end.

(** * Specification *)

Definition xor_spec (x y : bool)
  : bool
  := xorb x y.

(** * Verification *)

(** XOR circuit computes exclusive or correctly. *)
Theorem xor_correct
  : forall x y, xor_circuit x y = xor_spec x y.
Proof.
  intros x y.
  destruct x, y; reflexivity.
Qed.

(** Exhaustive verification on all four inputs. *)
Theorem xor_exhaustive
  : xor_circuit false false = false /\
    xor_circuit false true = true /\
    xor_circuit true false = true /\
    xor_circuit true true = false.
Proof.
  repeat split; reflexivity.
Qed.

(** 8-bit version correct. *)
Theorem xor_8bit_correct
  : forall x0 x1 x2 x3 x4 x5 x6 x7,
    xor_8bit [x0; x1; x2; x3; x4; x5; x6; x7] = xorb x0 x1.
Proof.
  intros.
  simpl.
  apply xor_correct.
Qed.

(** * Properties *)

(** XOR is commutative. *)
Lemma xor_comm
  : forall x y, xor_circuit x y = xor_circuit y x.
Proof.
  intros x y.
  destruct x, y; reflexivity.
Qed.

(** XOR is associative. *)
Lemma xor_assoc
  : forall x y z,
    xor_circuit x (xor_circuit y z) = xor_circuit (xor_circuit x y) z.
Proof.
  intros x y z.
  destruct x, y, z; reflexivity.
Qed.

(** XOR with false is identity. *)
Lemma xor_false_r
  : forall x, xor_circuit x false = x.
Proof.
  intro x.
  destruct x; reflexivity.
Qed.

(** XOR with true is NOT. *)
Lemma xor_true_r
  : forall x, xor_circuit x true = negb x.
Proof.
  intro x.
  destruct x; reflexivity.
Qed.

(** XOR with itself is false. *)
Lemma xor_nilpotent
  : forall x, xor_circuit x x = false.
Proof.
  intro x.
  destruct x; reflexivity.
Qed.

(** XOR is its own inverse. *)
Lemma xor_involutive
  : forall x y, xor_circuit x (xor_circuit x y) = y.
Proof.
  intros x y.
  destruct x, y; reflexivity.
Qed.

(** * Length Safety *)

(** Layer 1 neurons have length 2 weights *)
Lemma xor_layer1_neuron1_length
  : length (fst xor_layer1_neuron1) = 2%nat.
Proof. reflexivity. Qed.

Lemma xor_layer1_neuron2_length
  : length (fst xor_layer1_neuron2) = 2%nat.
Proof. reflexivity. Qed.

(** Layer 2 has length 2 weights *)
Lemma xor_layer2_weights_length
  : length xor_layer2_weights = 2%nat.
Proof. reflexivity. Qed.

(** XOR requires exactly 2 inputs for layer 1 *)
Theorem xor_layer1_length_requirement (x y : bool)
  : gate_length_ok (fst xor_layer1_neuron1) [x; y] /\
    gate_length_ok (fst xor_layer1_neuron2) [x; y].
Proof.
  split; unfold gate_length_ok;
  [ rewrite xor_layer1_neuron1_length | rewrite xor_layer1_neuron2_length ];
  reflexivity.
Qed.

(** XOR layer 2 requires exactly 2 inputs (from layer 1 outputs) *)
Theorem xor_layer2_length_requirement (b1 b2 : bool)
  : gate_length_ok xor_layer2_weights [b1; b2].
Proof.
  unfold gate_length_ok.
  rewrite xor_layer2_weights_length.
  reflexivity.
Qed.

(** * Network Architecture *)

(** Total parameters: 9 (Layer 1: 2*(2 weights + 1 bias) = 6, Layer 2: 2 weights + 1 bias = 3) *)
Definition xor_num_params : nat := 9.

(** Number of neurons: 3 (2 in layer 1, 1 in layer 2) *)
Definition xor_num_neurons : nat := 3.

(** Network depth: 2 layers *)
Definition xor_depth : nat := 2.
