(** * Base.WeightPatterns: Weight Generation Functions

    Algebraic weight patterns for threshold circuits.
    Weights are computed via functions, not enumerated.
*)

Require Import ZArith.
Require Import List.
Require Import Lia.
Require Import Base.Definitions.

Import ListNotations.

Open Scope Z_scope.

(** * Modular Weight Patterns *)

(** Weight pattern for MOD-m circuits.
    Pattern: (1, 1, ..., 1, 1-m) creates cumulative sum that cycles mod m. *)
Definition mod_m_weight (m : Z) (i : Z)
  : Z
  := if Z.eqb (i mod m) 0 then (1 - m) else 1.

(** Cumulative sum for MOD-m weight pattern. *)
Fixpoint mod_m_cumsum (m : Z) (k : nat)
  : Z
  :=
  match k with
  | O => 0
  | S k' => mod_m_cumsum m k' + mod_m_weight m (Z.of_nat k)
  end.

(** * Threshold Weight Patterns *)

(** All-ones pattern for simple threshold. *)
Definition threshold_weights (n : nat)
  : list Z
  := ones n.

(** Bias for k-out-of-n threshold. *)
Definition threshold_bias (k : nat)
  : Z
  := - Z.of_nat k.

(** * Comparison Weight Patterns *)

(** Weights for equality comparison (a = b).
    Use pattern: [1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1, -1, -1, -1, -1]. *)
Definition equality_weights (n : nat)
  : list Z
  :=
  ones n ++ map (fun _ => -1) (ones n).

(** Weights for greater-than comparison (a > b).
    More complex pattern involving difference computation. *)
Definition greater_than_weights (n : nat)
  : list Z
  :=
  ones n ++ map (fun _ => -1) (ones n).

(** * Parity Weight Patterns *)

(** Alternating weight pattern for parity.
    Used in multi-layer parity circuits. *)
Fixpoint parity_weights (n : nat)
  : list Z
  :=
  match n with
  | O => []
  | S n' => 1 :: parity_weights n'
  end.

(** * Arithmetic Weight Patterns *)

(** Power-of-two weights for binary-to-unary conversion. *)
Fixpoint power_weights (n : nat)
  : list Z
  :=
  match n with
  | O => []
  | S n' => Z.pow 2 (Z.of_nat n') :: power_weights n'
  end.

(** Position-dependent weights. *)
Definition positional_weight (pos : nat)
  : Z
  := Z.pow 2 (Z.of_nat pos).

(** * Pattern Properties *)

Lemma mod_m_weight_zero (m : Z)
  : m >= 2 ->
    mod_m_weight m 0 = (1 - m).
Proof.
  intro Hm.
  unfold mod_m_weight.
  rewrite Z.mod_0_l by lia.
  rewrite Z.eqb_refl.
  reflexivity.
Qed.

Lemma mod_m_weight_nonzero (m i : Z)
  : m >= 2 ->
    0 < i < m ->
    mod_m_weight m i = 1.
Proof.
  intros Hm Hi.
  unfold mod_m_weight.
  assert (i mod m = i) by (apply Z.mod_small; lia).
  rewrite H.
  assert (i <> 0) by lia.
  apply Z.eqb_neq in H0.
  rewrite H0.
  reflexivity.
Qed.

Lemma threshold_weights_length (n : nat)
  : length (threshold_weights n) = n.
Proof.
  unfold threshold_weights.
  apply ones_length.
Qed.

Lemma equality_weights_length (n : nat)
  : length (equality_weights n) = (2 * n)%nat.
Proof.
  unfold equality_weights.
  rewrite app_length.
  rewrite map_length.
  rewrite !ones_length.
  lia.
Qed.

(** * Weight Pattern Correctness *)

(** Key step: adding next weight maintains modulo property. *)
Lemma mod_m_weight_step (m kz : Z)
  : m >= 2 ->
    kz >= 0 ->
    kz mod m + mod_m_weight m (kz + 1) = (kz + 1) mod m.
Proof.
  intros Hm Hkz.
  unfold mod_m_weight.
  assert (Hbound: 0 <= kz mod m < m) by (apply Z.mod_pos_bound; lia).
  destruct (Z.eq_dec (kz mod m) (m - 1)) as [Hmax|Hnmax].
  - (* Case: kz mod m = m-1, so (kz+1) mod m = 0 *)
    assert (Hkp1: (kz + 1) mod m = 0).
    { rewrite <- Z.add_mod_idemp_l by lia.
      rewrite Hmax.
      replace (m - 1 + 1) with m by lia.
      apply Z.mod_same.
      lia. }
    rewrite Hkp1.
    rewrite Z.eqb_refl.
    rewrite Hmax.
    lia.
  - (* Case: kz mod m < m-1, so (kz+1) mod m = kz mod m + 1 *)
    assert (Hlt: kz mod m + 1 < m) by lia.
    assert (Hkp1: (kz + 1) mod m = kz mod m + 1).
    { rewrite <- Z.add_mod_idemp_l by lia.
      rewrite Z.mod_small by lia.
      reflexivity. }
    assert (Hne: (kz + 1) mod m <> 0) by lia.
    destruct (Z.eqb ((kz + 1) mod m) 0) eqn:Eeq.
    + apply Z.eqb_eq in Eeq. lia.
    + rewrite Hkp1. lia.
Qed.

(** MOD-m weight pattern produces correct cumulative sum. *)
Theorem mod_m_cumsum_correct (m : Z) (k : nat)
  : m >= 2 ->
    mod_m_cumsum m k = (Z.of_nat k) mod m.
Proof.
  intro Hm.
  induction k.
  - simpl.
    symmetry.
    apply Z.mod_0_l.
    lia.
  - unfold mod_m_cumsum; fold mod_m_cumsum.
    rewrite IHk.
    replace (Z.of_nat (S k)) with (Z.of_nat k + 1) at 1 2 by lia.
    rewrite <- (mod_m_weight_step m (Z.of_nat k)) by lia.
    reflexivity.
Qed.
