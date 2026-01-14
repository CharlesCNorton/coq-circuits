(** * Modular.Mod10: MOD-10 Circuit

    Computes (sum of inputs) mod 10.
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

(** MOD-10 weights *)
Definition mod10_weights : list Z := mod_m_weights_8 10.

(** MOD-10 for residue r *)
Definition mod10_residue (r : nat) (xs : list bool) : bool :=
  mod_m_circuit_k 10 r xs.

(** MOD-10 equals zero (divisibility test) *)
Definition mod10_is_zero (xs : list bool) : bool :=
  mod_m_is_residue 10 0 xs.

Theorem mod10_correct_residue_0
  : forall x0 x1 x2 x3 x4 x5 x6 x7,
    mod10_is_zero [x0; x1; x2; x3; x4; x5; x6; x7] =
    Z.eqb ((Z.of_nat (hamming_weight [x0; x1; x2; x3; x4; x5; x6; x7])) mod 10) 0.
Proof.
  intros.
  unfold mod10_is_zero, mod_m_is_residue.
  reflexivity.
Qed.

Lemma mod10_weights_length : length mod10_weights = 8%nat.
Proof. unfold mod10_weights. apply mod_m_weights_8_length. Qed.

Theorem mod10_length_requirement (xs : list bool)
  : length xs = 8%nat -> gate_length_ok mod10_weights xs.
Proof.
  intro Hlen.
  unfold mod10_weights.
  apply mod_m_length_requirement.
  assumption.
Qed.

Definition mod10_num_params : nat := 90.
