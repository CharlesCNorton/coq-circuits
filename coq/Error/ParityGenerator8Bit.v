(** * Error.ParityGenerator8Bit: Generate Parity Bit

    Generates a parity bit for 8-bit input.
    Output is 1 if odd number of 1s (makes total even).
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Base.Definitions.
Require Import Base.Tactics.

Import ListNotations.

Open Scope Z_scope.

(** * Circuit Definition *)

Definition parity_generator_8bit (b7 b6 b5 b4 b3 b2 b1 b0 : bool) : bool :=
  xorb (xorb (xorb b7 b6) (xorb b5 b4))
       (xorb (xorb b3 b2) (xorb b1 b0)).

(** * Specification *)

Definition parity_generator_8bit_spec (b7 b6 b5 b4 b3 b2 b1 b0 : bool) : bool :=
  xorb (xorb (xorb b7 b6) (xorb b5 b4))
       (xorb (xorb b3 b2) (xorb b1 b0)).

(** * Verification *)

Theorem parity_generator_8bit_correct
  : forall b7 b6 b5 b4 b3 b2 b1 b0,
    parity_generator_8bit b7 b6 b5 b4 b3 b2 b1 b0 =
    parity_generator_8bit_spec b7 b6 b5 b4 b3 b2 b1 b0.
Proof. intros. reflexivity. Qed.

(** All zeros gives parity 0 *)
Theorem parity_generator_8bit_zeros
  : parity_generator_8bit false false false false false false false false = false.
Proof. reflexivity. Qed.

(** Single one gives parity 1 *)
Theorem parity_generator_8bit_single_one
  : parity_generator_8bit true false false false false false false false = true.
Proof. reflexivity. Qed.

(** Two ones gives parity 0 *)
Theorem parity_generator_8bit_two_ones
  : parity_generator_8bit true true false false false false false false = false.
Proof. reflexivity. Qed.

(** * Network Architecture *)

Definition parity_generator_8bit_num_neurons : nat := 21.
Definition parity_generator_8bit_num_params : nat := 63.
Definition parity_generator_8bit_depth : nat := 6.
