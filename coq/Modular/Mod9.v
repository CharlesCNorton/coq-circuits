(** * Modular.Mod9: MOD-9 Circuit

    Computes (sum of inputs) mod 9.
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

(** MOD-9 weights *)
Definition mod9_weights : list Z := mod_m_weights_8 9.

(** MOD-9 for residue r *)
Definition mod9_residue (r : nat) (xs : list bool) : bool :=
  mod_m_circuit_k 9 r xs.

(** MOD-9 equals zero (divisibility test) *)
Definition mod9_is_zero (xs : list bool) : bool :=
  mod_m_is_residue 9 0 xs.

Theorem mod9_correct_residue_0
  : forall x0 x1 x2 x3 x4 x5 x6 x7,
    mod9_is_zero [x0; x1; x2; x3; x4; x5; x6; x7] =
    Z.eqb ((Z.of_nat (hamming_weight [x0; x1; x2; x3; x4; x5; x6; x7])) mod 9) 0.
Proof.
  intros.
  unfold mod9_is_zero, mod_m_is_residue.
  reflexivity.
Qed.

Lemma mod9_weights_length : length mod9_weights = 8%nat.
Proof. unfold mod9_weights. apply mod_m_weights_8_length. Qed.

Theorem mod9_length_requirement (xs : list bool)
  : length xs = 8%nat -> gate_length_ok mod9_weights xs.
Proof.
  intro Hlen.
  unfold mod9_weights.
  apply mod_m_length_requirement.
  assumption.
Qed.

Definition mod9_num_params : nat := 81.
