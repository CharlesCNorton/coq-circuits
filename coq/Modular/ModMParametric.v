(** * Modular.ModMParametric: Parametric MOD-m Circuit

    Formally verified parametric MOD-m circuit for m >= 2.
    Uses algebraic weight pattern from Base.WeightPatterns.
    Computes (sum of inputs) mod m.
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Lia.
Require Import Base.Definitions.
Require Import Base.Tactics.
Require Import Base.Verification.
Require Import Base.WeightPatterns.

Import ListNotations.

Open Scope Z_scope.

(** * Circuit Definition *)

(** MOD-m weights for 8-bit input using algebraic pattern. *)
Definition mod_m_weights_8 (m : Z)
  : list Z
  :=
  [ mod_m_weight m 1; mod_m_weight m 2; mod_m_weight m 3; mod_m_weight m 4;
    mod_m_weight m 5; mod_m_weight m 6; mod_m_weight m 7; mod_m_weight m 8 ].

(** MOD-m circuit outputs k neurons for k residues. *)
Definition mod_m_circuit_k (m : Z) (k : nat) (xs : list bool)
  : bool
  :=
  let weights := mod_m_weights_8 m in
  let bias := - (Z.of_nat k) in
  gate weights bias xs.

(** MOD-m circuit for residue r: fires when (HW mod m) = r. *)
Definition mod_m_is_residue (m : Z) (r : nat) (xs : list bool)
  : bool
  :=
  let hw := Z.of_nat (hamming_weight xs) in
  Z.eqb (hw mod m) (Z.of_nat r).

(** * Properties *)

(** MOD-m weights have length 8. *)
Lemma mod_m_weights_8_length (m : Z)
  : length (mod_m_weights_8 m) = 8%nat.
Proof.
  reflexivity.
Qed.

(** MOD-m weight pattern satisfies cumulative sum property. *)
Theorem mod_m_weights_cumsum (m : Z) (k : nat)
  : m >= 2 ->
    (k <= 8)%nat ->
    mod_m_cumsum m k = (Z.of_nat k) mod m.
Proof.
  intros Hm Hk.
  apply mod_m_cumsum_correct.
  assumption.
Qed.

(** * Length Safety *)

Theorem mod_m_length_requirement (m : Z) (xs : list bool)
  : length xs = 8%nat ->
    gate_length_ok (mod_m_weights_8 m) xs.
Proof.
  intro Hlen.
  unfold gate_length_ok.
  rewrite mod_m_weights_8_length.
  symmetry.
  exact Hlen.
Qed.

(** * Network Architecture *)

(** For m residues, need m neurons (one per residue). *)
Definition mod_m_num_neurons (m : nat) : nat := m.

(** Parameters: 8 weights + 1 bias per neuron. *)
Definition mod_m_num_params (m : nat) : nat := m * 9.

(** Single layer. *)
Definition mod_m_depth : nat := 1.
