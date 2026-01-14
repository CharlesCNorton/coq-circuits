(** * Modular.Mod5: MOD-5 Circuit

    Computes (sum of inputs) mod 5.
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

(** MOD-5 weights *)
Definition mod5_weights : list Z := mod_m_weights_8 5.

(** MOD-5 for residue r *)
Definition mod5_residue (r : nat) (xs : list bool) : bool :=
  mod_m_circuit_k 5 r xs.

(** MOD-5 equals zero (divisibility test) *)
Definition mod5_is_zero (xs : list bool) : bool :=
  mod_m_is_residue 5 0 xs.

Theorem mod5_correct_residue_0
  : forall x0 x1 x2 x3 x4 x5 x6 x7,
    mod5_is_zero [x0; x1; x2; x3; x4; x5; x6; x7] =
    Z.eqb ((Z.of_nat (hamming_weight [x0; x1; x2; x3; x4; x5; x6; x7])) mod 5) 0.
Proof.
  intros.
  unfold mod5_is_zero, mod_m_is_residue.
  reflexivity.
Qed.

Lemma mod5_weights_length : length mod5_weights = 8%nat.
Proof. unfold mod5_weights. apply mod_m_weights_8_length. Qed.

Theorem mod5_length_requirement (xs : list bool)
  : length xs = 8%nat -> gate_length_ok mod5_weights xs.
Proof.
  intro Hlen.
  unfold mod5_weights.
  apply mod_m_length_requirement.
  assumption.
Qed.

Definition mod5_num_params : nat := 45.
