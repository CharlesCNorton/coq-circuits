(** * Error.ParityChecker8Bit: 8-Bit Parity Checker

    Checks parity of 8 input bits.
    Fires when even number of inputs are true (even parity).
    Equivalent to MOD-2 = 0.
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Lia.
Require Import Base.Definitions.
Require Import Base.Tactics.
Require Import Base.Verification.
Require Import Modular.ModMParametric.
Require Import Modular.Mod2.

Import ListNotations.

Open Scope Z_scope.

(** * Circuit Definition *)

(** Even parity: fires when hamming weight is even *)
Definition even_parity_circuit (xs : list bool) : bool :=
  mod2_is_zero xs.

(** Odd parity: fires when hamming weight is odd *)
Definition odd_parity_circuit (xs : list bool) : bool :=
  negb (mod2_is_zero xs).

(** * Specification *)

Definition even_parity_spec (xs : list bool) : bool :=
  Nat.even (hamming_weight xs).

Definition odd_parity_spec (xs : list bool) : bool :=
  Nat.odd (hamming_weight xs).

(** * Verification *)

Theorem even_parity_correct
  : forall x0 x1 x2 x3 x4 x5 x6 x7,
    even_parity_circuit [x0; x1; x2; x3; x4; x5; x6; x7] =
    even_parity_spec [x0; x1; x2; x3; x4; x5; x6; x7].
Proof.
  intros.
  unfold even_parity_circuit, even_parity_spec, mod2_is_zero, mod_m_is_residue.
  destruct x0, x1, x2, x3, x4, x5, x6, x7; vm_compute; reflexivity.
Qed.

Theorem odd_parity_correct
  : forall x0 x1 x2 x3 x4 x5 x6 x7,
    odd_parity_circuit [x0; x1; x2; x3; x4; x5; x6; x7] =
    odd_parity_spec [x0; x1; x2; x3; x4; x5; x6; x7].
Proof.
  intros.
  unfold odd_parity_circuit, odd_parity_spec, mod2_is_zero, mod_m_is_residue.
  destruct x0, x1, x2, x3, x4, x5, x6, x7; vm_compute; reflexivity.
Qed.

Theorem even_parity_exhaustive
  : verify_all (fun xs =>
      Bool.eqb (even_parity_circuit xs) (even_parity_spec xs)) = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

(** * Properties *)

Lemma even_parity_all_zeros
  : even_parity_circuit [false; false; false; false; false; false; false; false] = true.
Proof. vm_compute. reflexivity. Qed.

Lemma even_parity_one_true
  : even_parity_circuit [true; false; false; false; false; false; false; false] = false.
Proof. vm_compute. reflexivity. Qed.

Lemma even_parity_two_true
  : even_parity_circuit [true; true; false; false; false; false; false; false] = true.
Proof. vm_compute. reflexivity. Qed.

Lemma odd_parity_all_zeros
  : odd_parity_circuit [false; false; false; false; false; false; false; false] = false.
Proof. vm_compute. reflexivity. Qed.

Lemma odd_parity_one_true
  : odd_parity_circuit [true; false; false; false; false; false; false; false] = true.
Proof. vm_compute. reflexivity. Qed.

(** * Complementarity *)

Theorem parity_complement
  : forall x0 x1 x2 x3 x4 x5 x6 x7,
    odd_parity_circuit [x0; x1; x2; x3; x4; x5; x6; x7] =
    negb (even_parity_circuit [x0; x1; x2; x3; x4; x5; x6; x7]).
Proof.
  intros.
  unfold odd_parity_circuit, even_parity_circuit.
  reflexivity.
Qed.

(** * Network Architecture *)

Definition even_parity_num_params : nat := 9.
Definition even_parity_num_neurons : nat := 1.
Definition even_parity_depth : nat := 1.
