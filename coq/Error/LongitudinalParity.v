(** * Error.LongitudinalParity: Longitudinal Redundancy Check

    Computes longitudinal parity (LRC) for two 8-bit bytes.
    LRC is the XOR of all bytes, commonly used in serial communication.

    Input: Two 8-bit bytes (a7..a0, b7..b0)
    Output: 8-bit parity byte (p7..p0) where p_i = a_i XOR b_i
*)

Require Import List.
Require Import Bool.
Require Import Base.Definitions.
Require Import Base.Tactics.

Import ListNotations.

Open Scope nat_scope.

(** * Circuit Definition *)

(** Longitudinal parity: XOR corresponding bits of two bytes.
    This is the simplest form of LRC for 2-byte blocks.
    Can be extended to n bytes by chaining XORs.
*)
Definition longitudinal_parity
  (a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0 : bool)
  : bool * bool * bool * bool * bool * bool * bool * bool :=
  (xorb a7 b7, xorb a6 b6, xorb a5 b5, xorb a4 b4,
   xorb a3 b3, xorb a2 b2, xorb a1 b1, xorb a0 b0).

(** * Specification *)

Definition longitudinal_parity_spec
  (a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0 : bool)
  : bool * bool * bool * bool * bool * bool * bool * bool :=
  (xorb a7 b7, xorb a6 b6, xorb a5 b5, xorb a4 b4,
   xorb a3 b3, xorb a2 b2, xorb a1 b1, xorb a0 b0).

(** * Verification *)

Theorem longitudinal_parity_correct
  : forall a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0,
    longitudinal_parity a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0 =
    longitudinal_parity_spec a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0.
Proof.
  intros. reflexivity.
Qed.

(** * Properties *)

(** LRC of identical bytes is zero. *)
Lemma lrc_self_zero
  : forall a7 a6 a5 a4 a3 a2 a1 a0,
    longitudinal_parity a7 a6 a5 a4 a3 a2 a1 a0 a7 a6 a5 a4 a3 a2 a1 a0 =
    (false, false, false, false, false, false, false, false).
Proof.
  intros.
  unfold longitudinal_parity.
  destruct a7, a6, a5, a4, a3, a2, a1, a0; reflexivity.
Qed.

(** LRC with zero is identity. *)
Lemma lrc_zero_identity
  : forall a7 a6 a5 a4 a3 a2 a1 a0,
    longitudinal_parity a7 a6 a5 a4 a3 a2 a1 a0
                        false false false false false false false false =
    (a7, a6, a5, a4, a3, a2, a1, a0).
Proof.
  intros.
  unfold longitudinal_parity.
  destruct a7, a6, a5, a4, a3, a2, a1, a0; reflexivity.
Qed.

(** Commutativity: LRC(A, B) = LRC(B, A). *)
Lemma lrc_commutative
  : forall a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0,
    longitudinal_parity a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0 =
    longitudinal_parity b7 b6 b5 b4 b3 b2 b1 b0 a7 a6 a5 a4 a3 a2 a1 a0.
Proof.
  intros.
  unfold longitudinal_parity.
  destruct a7, a6, a5, a4, a3, a2, a1, a0,
           b7, b6, b5, b4, b3, b2, b1, b0; reflexivity.
Qed.

(** XOR of A, B, and LRC(A,B) is zero (verification property). *)
Lemma lrc_verification
  : forall a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0,
    let '(p7, p6, p5, p4, p3, p2, p1, p0) :=
        longitudinal_parity a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0 in
    longitudinal_parity a7 a6 a5 a4 a3 a2 a1 a0 p7 p6 p5 p4 p3 p2 p1 p0 =
    (b7, b6, b5, b4, b3, b2, b1, b0).
Proof.
  intros.
  unfold longitudinal_parity.
  destruct a7, a6, a5, a4, a3, a2, a1, a0,
           b7, b6, b5, b4, b3, b2, b1, b0; reflexivity.
Qed.

(** Exhaustive verification. *)
Theorem longitudinal_parity_exhaustive
  : forall a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0,
    longitudinal_parity a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0 =
    longitudinal_parity_spec a7 a6 a5 a4 a3 a2 a1 a0 b7 b6 b5 b4 b3 b2 b1 b0.
Proof.
  intros.
  destruct a7, a6, a5, a4, a3, a2, a1, a0,
           b7, b6, b5, b4, b3, b2, b1, b0; reflexivity.
Qed.

(** * Network Architecture *)

Definition longitudinal_parity_num_neurons : nat := 24.
Definition longitudinal_parity_num_params : nat := 72.
Definition longitudinal_parity_depth : nat := 2.
