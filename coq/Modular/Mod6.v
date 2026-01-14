(** * Modular.Mod6: MOD-6 Circuit

    Computes (sum of inputs) mod 6.
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

(** MOD-6 weights *)
Definition mod6_weights : list Z := mod_m_weights_8 6.

(** MOD-6 for residue r *)
Definition mod6_residue (r : nat) (xs : list bool) : bool :=
  mod_m_circuit_k 6 r xs.

(** MOD-6 equals zero (divisibility test) *)
Definition mod6_is_zero (xs : list bool) : bool :=
  mod_m_is_residue 6 0 xs.

Theorem mod6_correct_residue_0
  : forall x0 x1 x2 x3 x4 x5 x6 x7,
    mod6_is_zero [x0; x1; x2; x3; x4; x5; x6; x7] =
    Z.eqb ((Z.of_nat (hamming_weight [x0; x1; x2; x3; x4; x5; x6; x7])) mod 6) 0.
Proof.
  intros.
  unfold mod6_is_zero, mod_m_is_residue.
  reflexivity.
Qed.

Lemma mod6_weights_length : length mod6_weights = 8%nat.
Proof. unfold mod6_weights. apply mod_m_weights_8_length. Qed.

Theorem mod6_length_requirement (xs : list bool)
  : length xs = 8%nat -> gate_length_ok mod6_weights xs.
Proof.
  intro Hlen.
  unfold mod6_weights.
  apply mod_m_length_requirement.
  assumption.
Qed.

Definition mod6_num_params : nat := 54.
