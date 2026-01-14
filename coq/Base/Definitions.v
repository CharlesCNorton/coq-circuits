(** * Base.Definitions: Core Threshold Circuit Definitions

    Foundational definitions for all threshold logic circuits.
    All circuits in this library build on these primitives.
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Lia.

Import ListNotations.

Open Scope Z_scope.

(** * Core Boolean Functions *)

(** Hamming weight: count of set bits in a boolean list. *)
Fixpoint hamming_weight (xs : list bool)
  : nat
  :=
  match xs with
  | [] => 0
  | true :: xs' => S (hamming_weight xs')
  | false :: xs' => hamming_weight xs'
  end.

(** * Neural Network Primitives *)

(** Dot product of integer weights and boolean inputs.
    Boolean true contributes its weight, false contributes 0. *)
Fixpoint dot (ws : list Z) (xs : list bool)
  : Z
  :=
  match ws, xs with
  | [], _ => 0
  | _, [] => 0
  | w :: ws', x :: xs' => (if x then w else 0) + dot ws' xs'
  end.

(** Heaviside step function (threshold gate).
    Fires when weighted sum plus bias is non-negative. *)
Definition gate (ws : list Z) (b : Z) (xs : list bool)
  : bool
  := Z.geb (dot ws xs + b) 0.

(** Apply multiple gates (neurons) to same input.
    Each neuron has its own weights and bias. *)
Definition layer (neurons : list (list Z * Z)) (xs : list bool)
  : list bool
  := map (fun wb => gate (fst wb) (snd wb) xs) neurons.

(** * Common Weight Patterns *)

(** All-ones weight vector of length n. *)
Fixpoint ones (n : nat)
  : list Z
  :=
  match n with
  | O => []
  | S n' => 1 :: ones n'
  end.

(** Standard 8-bit all-ones vector. *)
Definition ones8
  : list Z
  := [1; 1; 1; 1; 1; 1; 1; 1].

(** * Utility Functions *)

(** Convert boolean to integer (0 or 1). *)
Definition bool_to_Z (b : bool)
  : Z
  := if b then 1 else 0.

(** Convert list of booleans to list of integers. *)
Definition bools_to_Zs (xs : list bool)
  : list Z
  := map bool_to_Z xs.

(** * Basic Lemmas *)

Lemma hamming_weight_nil
  : hamming_weight [] = 0%nat.
Proof. reflexivity. Qed.

Lemma hamming_weight_cons_true (xs : list bool)
  : hamming_weight (true :: xs) = S (hamming_weight xs).
Proof. reflexivity. Qed.

Lemma hamming_weight_cons_false (xs : list bool)
  : hamming_weight (false :: xs) = hamming_weight xs.
Proof. reflexivity. Qed.

Lemma dot_nil_left (xs : list bool)
  : dot [] xs = 0.
Proof. reflexivity. Qed.

Lemma dot_nil_right (ws : list Z)
  : dot ws [] = 0.
Proof. destruct ws; reflexivity. Qed.

Lemma dot_cons_true (w : Z) (ws : list Z) (xs : list bool)
  : dot (w :: ws) (true :: xs) = w + dot ws xs.
Proof. reflexivity. Qed.

Lemma dot_cons_false (w : Z) (ws : list Z) (xs : list bool)
  : dot (w :: ws) (false :: xs) = dot ws xs.
Proof. reflexivity. Qed.

Lemma ones_length (n : nat)
  : length (ones n) = n.
Proof.
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn.
    reflexivity.
Qed.

Lemma ones8_length
  : length ones8 = 8%nat.
Proof. reflexivity. Qed.

(** * Thermometer Encoding *)

(** Thermometer layer: neuron k fires when HW >= k.
    Creates 9 neurons for 8-bit input (thresholds 0 through 8). *)
Definition thermometer_layer
  : list (list Z * Z)
  :=
  [ (ones8, 0%Z); (ones8, (-1)%Z); (ones8, (-2)%Z); (ones8, (-3)%Z);
    (ones8, (-4)%Z); (ones8, (-5)%Z); (ones8, (-6)%Z); (ones8, (-7)%Z); (ones8, (-8)%Z) ].
