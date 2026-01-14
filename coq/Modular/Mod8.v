(** * Modular.Mod8: MOD-8 Circuit

    Computes (sum of inputs) mod 8.
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

(** MOD-8 weights *)
Definition mod8_weights : list Z := mod_m_weights_8 8.

(** MOD-8 for residue r *)
Definition mod8_residue (r : nat) (xs : list bool) : bool :=
  mod_m_circuit_k 8 r xs.

(** MOD-8 equals zero (divisibility test) *)
Definition mod8_is_zero (xs : list bool) : bool :=
  mod_m_is_residue 8 0 xs.

Theorem mod8_correct_residue_0
  : forall x0 x1 x2 x3 x4 x5 x6 x7,
    mod8_is_zero [x0; x1; x2; x3; x4; x5; x6; x7] =
    Z.eqb ((Z.of_nat (hamming_weight [x0; x1; x2; x3; x4; x5; x6; x7])) mod 8) 0.
Proof.
  intros.
  unfold mod8_is_zero, mod_m_is_residue.
  reflexivity.
Qed.

Lemma mod8_weights_length : length mod8_weights = 8%nat.
Proof. unfold mod8_weights. apply mod_m_weights_8_length. Qed.

Theorem mod8_length_requirement (xs : list bool)
  : length xs = 8%nat -> gate_length_ok mod8_weights xs.
Proof.
  intro Hlen.
  unfold mod8_weights.
  apply mod_m_length_requirement.
  assumption.
Qed.

Definition mod8_num_params : nat := 72.
