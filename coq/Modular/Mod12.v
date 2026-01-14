(** * Modular.Mod12: MOD-12 Circuit

    Computes (sum of inputs) mod 12.
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Lia.
Require Import Base.Definitions.
Require Import Base.Tactics.
Require Import Base.Verification.
Require Import Base.WeightPatterns.
Require Import Modular.ModMParametric.

Import ListNotations.

Open Scope Z_scope.

(** MOD-12 weights *)
Definition mod12_weights : list Z := mod_m_weights_8 12.

(** MOD-12 for residue r *)
Definition mod12_residue (r : nat) (xs : list bool) : bool :=
  mod_m_circuit_k 12 r xs.

(** MOD-12 equals zero (divisibility test) *)
Definition mod12_is_zero (xs : list bool) : bool :=
  mod_m_is_residue 12 0 xs.

Theorem mod12_correct_residue_0
  : forall x0 x1 x2 x3 x4 x5 x6 x7,
    mod12_is_zero [x0; x1; x2; x3; x4; x5; x6; x7] =
    Z.eqb ((Z.of_nat (hamming_weight [x0; x1; x2; x3; x4; x5; x6; x7])) mod 12) 0.
Proof.
  intros.
  unfold mod12_is_zero, mod_m_is_residue.
  reflexivity.
Qed.

Lemma mod12_weights_length : length mod12_weights = 8%nat.
Proof. unfold mod12_weights. apply mod_m_weights_8_length. Qed.

Theorem mod12_length_requirement (xs : list bool)
  : length xs = 8%nat -> gate_length_ok mod12_weights xs.
Proof.
  intro Hlen.
  unfold mod12_weights.
  apply mod_m_length_requirement.
  assumption.
Qed.

Definition mod12_num_params : nat := 108.
