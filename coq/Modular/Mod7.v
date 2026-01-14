(** * Modular.Mod7: MOD-7 Circuit

    Computes (sum of inputs) mod 7.
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

(** MOD-7 weights *)
Definition mod7_weights : list Z := mod_m_weights_8 7.

(** MOD-7 for residue r *)
Definition mod7_residue (r : nat) (xs : list bool) : bool :=
  mod_m_circuit_k 7 r xs.

(** MOD-7 equals zero (divisibility test) *)
Definition mod7_is_zero (xs : list bool) : bool :=
  mod_m_is_residue 7 0 xs.

Theorem mod7_correct_residue_0
  : forall x0 x1 x2 x3 x4 x5 x6 x7,
    mod7_is_zero [x0; x1; x2; x3; x4; x5; x6; x7] =
    Z.eqb ((Z.of_nat (hamming_weight [x0; x1; x2; x3; x4; x5; x6; x7])) mod 7) 0.
Proof.
  intros.
  unfold mod7_is_zero, mod_m_is_residue.
  reflexivity.
Qed.

Lemma mod7_weights_length : length mod7_weights = 8%nat.
Proof. unfold mod7_weights. apply mod_m_weights_8_length. Qed.

Theorem mod7_length_requirement (xs : list bool)
  : length xs = 8%nat -> gate_length_ok mod7_weights xs.
Proof.
  intro Hlen.
  unfold mod7_weights.
  apply mod_m_length_requirement.
  assumption.
Qed.

Definition mod7_num_params : nat := 63.
