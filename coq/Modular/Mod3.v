(** * Modular.Mod3: MOD-3 Circuit

    Computes (sum of inputs) mod 3.
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

(** MOD-3 weights *)
Definition mod3_weights : list Z := mod_m_weights_8 3.

(** MOD-3 for residue r *)
Definition mod3_residue (r : nat) (xs : list bool) : bool :=
  mod_m_circuit_k 3 r xs.

(** MOD-3 equals zero (divisibility test) *)
Definition mod3_is_zero (xs : list bool) : bool :=
  mod_m_is_residue 3 0 xs.

Theorem mod3_correct_residue_0
  : forall x0 x1 x2 x3 x4 x5 x6 x7,
    mod3_is_zero [x0; x1; x2; x3; x4; x5; x6; x7] =
    Z.eqb ((Z.of_nat (hamming_weight [x0; x1; x2; x3; x4; x5; x6; x7])) mod 3) 0.
Proof.
  intros.
  unfold mod3_is_zero, mod_m_is_residue.
  reflexivity.
Qed.

Lemma mod3_weights_length : length mod3_weights = 8%nat.
Proof. unfold mod3_weights. apply mod_m_weights_8_length. Qed.

Theorem mod3_length_requirement (xs : list bool)
  : length xs = 8%nat -> gate_length_ok mod3_weights xs.
Proof.
  intro Hlen.
  unfold mod3_weights.
  apply mod_m_length_requirement.
  assumption.
Qed.

Definition mod3_num_params : nat := 27.
