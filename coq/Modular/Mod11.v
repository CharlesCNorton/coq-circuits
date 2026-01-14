(** * Modular.Mod11: MOD-11 Circuit

    Computes (sum of inputs) mod 11.
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

(** MOD-11 weights *)
Definition mod11_weights : list Z := mod_m_weights_8 11.

(** MOD-11 for residue r *)
Definition mod11_residue (r : nat) (xs : list bool) : bool :=
  mod_m_circuit_k 11 r xs.

(** MOD-11 equals zero (divisibility test) *)
Definition mod11_is_zero (xs : list bool) : bool :=
  mod_m_is_residue 11 0 xs.

Theorem mod11_correct_residue_0
  : forall x0 x1 x2 x3 x4 x5 x6 x7,
    mod11_is_zero [x0; x1; x2; x3; x4; x5; x6; x7] =
    Z.eqb ((Z.of_nat (hamming_weight [x0; x1; x2; x3; x4; x5; x6; x7])) mod 11) 0.
Proof.
  intros.
  unfold mod11_is_zero, mod_m_is_residue.
  reflexivity.
Qed.

Lemma mod11_weights_length : length mod11_weights = 8%nat.
Proof. unfold mod11_weights. apply mod_m_weights_8_length. Qed.

Theorem mod11_length_requirement (xs : list bool)
  : length xs = 8%nat -> gate_length_ok mod11_weights xs.
Proof.
  intro Hlen.
  unfold mod11_weights.
  apply mod_m_length_requirement.
  assumption.
Qed.

Definition mod11_num_params : nat := 99.
