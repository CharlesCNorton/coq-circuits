(** * Modular.Mod4: MOD-4 Circuit

    Computes (sum of inputs) mod 4.
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

(** MOD-4 weights *)
Definition mod4_weights : list Z := mod_m_weights_8 4.

(** MOD-4 for residue r *)
Definition mod4_residue (r : nat) (xs : list bool) : bool :=
  mod_m_circuit_k 4 r xs.

(** MOD-4 equals zero (divisibility test) *)
Definition mod4_is_zero (xs : list bool) : bool :=
  mod_m_is_residue 4 0 xs.

Theorem mod4_correct_residue_0
  : forall x0 x1 x2 x3 x4 x5 x6 x7,
    mod4_is_zero [x0; x1; x2; x3; x4; x5; x6; x7] =
    Z.eqb ((Z.of_nat (hamming_weight [x0; x1; x2; x3; x4; x5; x6; x7])) mod 4) 0.
Proof.
  intros.
  unfold mod4_is_zero, mod_m_is_residue.
  reflexivity.
Qed.

Lemma mod4_weights_length : length mod4_weights = 8%nat.
Proof. unfold mod4_weights. apply mod_m_weights_8_length. Qed.

Theorem mod4_length_requirement (xs : list bool)
  : length xs = 8%nat -> gate_length_ok mod4_weights xs.
Proof.
  intro Hlen.
  unfold mod4_weights.
  apply mod_m_length_requirement.
  assumption.
Qed.

Definition mod4_num_params : nat := 36.
