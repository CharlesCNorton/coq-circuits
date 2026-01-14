(** * Boolean.BiImplies: Biconditional Gate

    Formally verified biconditional gate (if and only if, equivalence).
    BiImplies is equivalent to XNOR and uses the same 2-layer architecture.
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

(** BiImplies requires 2 layers (same as XNOR).
    Layer 1: Compute NOR and AND in parallel.
    Layer 2: Compute OR of the two results.

    BiImplies(x,y) = OR(NOR(x,y), AND(x,y)) = XNOR(x,y)
*)

(** Layer 1, neuron 1: NOR gate *)
Definition biimplies_layer1_neuron1
  : list Z * Z
  := ([-1; -1], 0).

(** Layer 1, neuron 2: AND gate *)
Definition biimplies_layer1_neuron2
  : list Z * Z
  := ([1; 1], -2).

(** Layer 1: both neurons *)
Definition biimplies_layer1
  : list (list Z * Z)
  := [biimplies_layer1_neuron1; biimplies_layer1_neuron2].

(** Layer 2: OR gate combining layer 1 outputs *)
Definition biimplies_layer2_weights
  : list Z
  := [1; 1].

Definition biimplies_layer2_bias
  : Z
  := -1.

(** BiImplies circuit: 2-layer network *)
Definition biimplies_circuit (x y : bool)
  : bool
  :=
  let layer1_out := layer biimplies_layer1 [x; y] in
  gate biimplies_layer2_weights biimplies_layer2_bias layer1_out.

(** Extend to 8-bit input (operates on first two bits only). *)
Definition biimplies_8bit (xs : list bool)
  : bool
  :=
  match xs with
  | x :: y :: _ => biimplies_circuit x y
  | _ => false
  end.

(** * Specification *)

Definition biimplies_spec (x y : bool)
  : bool
  := eqb x y.

(** * Verification *)

(** BiImplies circuit computes biconditional correctly. *)
Theorem biimplies_correct
  : forall x y, biimplies_circuit x y = biimplies_spec x y.
Proof.
  intros x y.
  destruct x, y; reflexivity.
Qed.

(** Exhaustive verification on all four inputs. *)
Theorem biimplies_exhaustive
  : biimplies_circuit false false = true /\
    biimplies_circuit false true = false /\
    biimplies_circuit true false = false /\
    biimplies_circuit true true = true.
Proof.
  repeat split; reflexivity.
Qed.

(** 8-bit version correct. *)
Theorem biimplies_8bit_correct
  : forall x0 x1 x2 x3 x4 x5 x6 x7,
    biimplies_8bit [x0; x1; x2; x3; x4; x5; x6; x7] = eqb x0 x1.
Proof.
  intros.
  simpl.
  apply biimplies_correct.
Qed.

(** * Properties *)

(** BiImplies is commutative (symmetry of equivalence). *)
Lemma biimplies_comm
  : forall x y, biimplies_circuit x y = biimplies_circuit y x.
Proof.
  intros x y.
  destruct x, y; reflexivity.
Qed.

(** BiImplies is reflexive. *)
Lemma biimplies_refl
  : forall x, biimplies_circuit x x = true.
Proof.
  intro x.
  destruct x; reflexivity.
Qed.

(** BiImplies is symmetric. *)
Lemma biimplies_sym
  : forall x y, biimplies_circuit x y = biimplies_circuit y x.
Proof.
  apply biimplies_comm.
Qed.

(** BiImplies is transitive. *)
Lemma biimplies_trans
  : forall x y z,
    biimplies_circuit x y = true ->
    biimplies_circuit y z = true ->
    biimplies_circuit x z = true.
Proof.
  intros x y z Hxy Hyz.
  destruct x, y, z; try reflexivity; discriminate.
Qed.

(** BiImplies with true gives identity. *)
Lemma biimplies_true_r
  : forall x, biimplies_circuit x true = x.
Proof.
  intro x.
  destruct x; reflexivity.
Qed.

(** BiImplies with false gives negation. *)
Lemma biimplies_false_r
  : forall x, biimplies_circuit x false = negb x.
Proof.
  intro x.
  destruct x; reflexivity.
Qed.

(** * Length Safety *)

(** Layer 1 neurons have length 2 weights *)
Lemma biimplies_layer1_neuron1_length
  : length (fst biimplies_layer1_neuron1) = 2%nat.
Proof. reflexivity. Qed.

Lemma biimplies_layer1_neuron2_length
  : length (fst biimplies_layer1_neuron2) = 2%nat.
Proof. reflexivity. Qed.

(** Layer 2 has length 2 weights *)
Lemma biimplies_layer2_weights_length
  : length biimplies_layer2_weights = 2%nat.
Proof. reflexivity. Qed.

(** BiImplies requires exactly 2 inputs for layer 1 *)
Theorem biimplies_layer1_length_requirement (x y : bool)
  : gate_length_ok (fst biimplies_layer1_neuron1) [x; y] /\
    gate_length_ok (fst biimplies_layer1_neuron2) [x; y].
Proof.
  split; unfold gate_length_ok;
  [ rewrite biimplies_layer1_neuron1_length | rewrite biimplies_layer1_neuron2_length ];
  reflexivity.
Qed.

(** BiImplies layer 2 requires exactly 2 inputs (from layer 1 outputs) *)
Theorem biimplies_layer2_length_requirement (b1 b2 : bool)
  : gate_length_ok biimplies_layer2_weights [b1; b2].
Proof.
  unfold gate_length_ok.
  rewrite biimplies_layer2_weights_length.
  reflexivity.
Qed.

(** * Network Architecture *)

(** Total parameters: 9 (Layer 1: 2*(2 weights + 1 bias) = 6, Layer 2: 2 weights + 1 bias = 3) *)
Definition biimplies_num_params : nat := 9.

(** Number of neurons: 3 (2 in layer 1, 1 in layer 2) *)
Definition biimplies_num_neurons : nat := 3.

(** Network depth: 2 layers *)
Definition biimplies_depth : nat := 2.
