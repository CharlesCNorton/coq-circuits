(** * Modular.Mod2: MOD-2 Circuit

    Computes (sum of inputs) mod 2.
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

(** MOD-2 weights *)
Definition mod2_weights : list Z := mod_m_weights_8 2.

(** MOD-2 for residue r *)
Definition mod2_residue (r : nat) (xs : list bool) : bool :=
  mod_m_circuit_k 2 r xs.

(** MOD-2 equals zero (divisibility test) *)
Definition mod2_is_zero (xs : list bool) : bool :=
  mod_m_is_residue 2 0 xs.

Theorem mod2_correct_residue_0
  : forall x0 x1 x2 x3 x4 x5 x6 x7,
    mod2_is_zero [x0; x1; x2; x3; x4; x5; x6; x7] =
    Z.eqb ((Z.of_nat (hamming_weight [x0; x1; x2; x3; x4; x5; x6; x7])) mod 2) 0.
Proof.
  intros.
  unfold mod2_is_zero, mod_m_is_residue.
  reflexivity.
Qed.

Lemma mod2_weights_length : length mod2_weights = 8%nat.
Proof. unfold mod2_weights. apply mod_m_weights_8_length. Qed.

Theorem mod2_length_requirement (xs : list bool)
  : length xs = 8%nat -> gate_length_ok mod2_weights xs.
Proof.
  intro Hlen.
  unfold mod2_weights.
  apply mod_m_length_requirement.
  assumption.
Qed.

Definition mod2_num_params : nat := 18.
