(** * Arithmetic.Multiplier2x2: 2-bit by 2-bit Multiplier

    Multiplies two 2-bit unsigned numbers, producing 4-bit result.
    Uses AND gates for partial products and adders for summation.
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Base.Definitions.
Require Import Base.Tactics.
Require Import Boolean.AND.
Require Import Boolean.OR.
Require Import Boolean.XOR.
Require Import Boolean.NAND.
Require Import Arithmetic.HalfAdder.
Require Import Arithmetic.FullAdder.

Import ListNotations.

Open Scope nat_scope.

(** * Circuit Definition *)

(** Partial product: a AND b. *)
Definition pp (a b : bool) : bool := andb a b.

(** 2x2 multiplier using partial products and adders.
    A = a1*2 + a0
    B = b1*2 + b0
    Product = (a1*b1)*4 + (a1*b0 + a0*b1)*2 + (a0*b0)

    Array multiplication:
                a1  a0
              x b1  b0
              --------
              a1b0 a0b0   (partial product row 0)
         a1b1 a0b1        (partial product row 1)
         ----------------
         p3   p2   p1  p0

    p0 = a0*b0
    p1 = a1*b0 XOR a0*b1
    c1 = a1*b0 AND a0*b1
    p2 = a1*b1 XOR c1
    p3 = a1*b1 AND c1
*)
Definition multiplier_2x2 (a1 a0 b1 b0 : bool)
  : bool * bool * bool * bool :=
  let pp00 := pp a0 b0 in
  let pp10 := pp a1 b0 in
  let pp01 := pp a0 b1 in
  let pp11 := pp a1 b1 in
  let '(sum1, carry1) := half_adder pp10 pp01 in
  let '(sum2, carry2) := half_adder pp11 carry1 in
  (carry2, sum2, sum1, pp00).

(** * Specification *)

Definition bits2_to_N (b1 b0 : bool) : nat :=
  (if b1 then 2 else 0) + (if b0 then 1 else 0).

Definition bits4_to_N (b3 b2 b1 b0 : bool) : nat :=
  (if b3 then 8 else 0) + (if b2 then 4 else 0) +
  (if b1 then 2 else 0) + (if b0 then 1 else 0).

Definition N_to_bits4 (n : nat) : bool * bool * bool * bool :=
  (Nat.testbit n 3, Nat.testbit n 2, Nat.testbit n 1, Nat.testbit n 0).

Definition multiplier_2x2_spec (a1 a0 b1 b0 : bool) : bool * bool * bool * bool :=
  N_to_bits4 (bits2_to_N a1 a0 * bits2_to_N b1 b0).

(** * Verification *)

Theorem multiplier_2x2_correct
  : forall a1 a0 b1 b0,
    multiplier_2x2 a1 a0 b1 b0 = multiplier_2x2_spec a1 a0 b1 b0.
Proof.
  intros.
  unfold multiplier_2x2, multiplier_2x2_spec, pp, bits2_to_N, N_to_bits4.
  unfold half_adder, xor_circuit, and_circuit.
  unfold or_circuit, nand_circuit, gate.
  destruct a1, a0, b1, b0; reflexivity.
Qed.

(** * Properties *)

(** 0 * anything = 0. *)
Lemma mult_0_l
  : forall b1 b0, multiplier_2x2 false false b1 b0 = (false, false, false, false).
Proof.
  intros. destruct b1, b0; reflexivity.
Qed.

(** anything * 0 = 0. *)
Lemma mult_0_r
  : forall a1 a0, multiplier_2x2 a1 a0 false false = (false, false, false, false).
Proof.
  intros. destruct a1, a0; reflexivity.
Qed.

(** 1 * B = B. *)
Lemma mult_1_l
  : forall b1 b0, multiplier_2x2 false true b1 b0 = (false, false, b1, b0).
Proof.
  intros. destruct b1, b0; reflexivity.
Qed.

(** A * 1 = A. *)
Lemma mult_1_r
  : forall a1 a0, multiplier_2x2 a1 a0 false true = (false, false, a1, a0).
Proof.
  intros. destruct a1, a0; reflexivity.
Qed.

(** 3 * 3 = 9. *)
Lemma mult_3_3
  : multiplier_2x2 true true true true = (true, false, false, true).
Proof. reflexivity. Qed.

(** 2 * 3 = 6. *)
Lemma mult_2_3
  : multiplier_2x2 true false true true = (false, true, true, false).
Proof. reflexivity. Qed.

(** Commutativity. *)
Lemma mult_comm
  : forall a1 a0 b1 b0,
    multiplier_2x2 a1 a0 b1 b0 = multiplier_2x2 b1 b0 a1 a0.
Proof.
  intros.
  destruct a1, a0, b1, b0; reflexivity.
Qed.

(** * Network Architecture *)

Definition multiplier_2x2_num_neurons : nat := 12.
Definition multiplier_2x2_num_params : nat := 36.
Definition multiplier_2x2_depth : nat := 4.
