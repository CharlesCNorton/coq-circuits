(** * ALU.ALUFlags: Status Flag Computation for 8-Bit ALU

    Computes the four standard ALU status flags:
    - Z (Zero): Result is all zeros
    - N (Negative): MSB of result is 1 (signed negative)
    - C (Carry): Carry out from arithmetic operation
    - V (Overflow): Signed overflow occurred
*)

Require Import Bool.
Require Import List.
Import ListNotations.

(** * Flag Definitions *)

(** Zero flag: true when all result bits are 0. *)
Definition zero_flag (r7 r6 r5 r4 r3 r2 r1 r0 : bool) : bool :=
  negb (orb r7 (orb r6 (orb r5 (orb r4 (orb r3 (orb r2 (orb r1 r0))))))).

(** Negative flag: true when MSB is 1 (two's complement negative). *)
Definition negative_flag (r7 : bool) : bool := r7.

(** Carry flag: directly from carry-out of adder. *)
Definition carry_flag (cout : bool) : bool := cout.

(** Overflow flag: signed overflow detection.
    Overflow occurs when:
    - Adding two positives yields negative, or
    - Adding two negatives yields positive.
    Formula: V = (A[7] = B[7]) AND (A[7] != R[7]) for addition.
    For subtraction with B inverted: V = (A[7] != B[7]) AND (A[7] != R[7]). *)
Definition overflow_flag_add (a7 b7 r7 : bool) : bool :=
  andb (Bool.eqb a7 b7) (negb (Bool.eqb a7 r7)).

Definition overflow_flag_sub (a7 b7 r7 : bool) : bool :=
  andb (negb (Bool.eqb a7 b7)) (negb (Bool.eqb a7 r7)).

(** Combined flag computation for addition. *)
Definition alu_flags_add
  (a7 b7 : bool)
  (r7 r6 r5 r4 r3 r2 r1 r0 : bool)
  (cout : bool)
  : bool * bool * bool * bool :=
  (zero_flag r7 r6 r5 r4 r3 r2 r1 r0,
   negative_flag r7,
   carry_flag cout,
   overflow_flag_add a7 b7 r7).

(** Combined flag computation for subtraction. *)
Definition alu_flags_sub
  (a7 b7 : bool)
  (r7 r6 r5 r4 r3 r2 r1 r0 : bool)
  (cout : bool)
  : bool * bool * bool * bool :=
  (zero_flag r7 r6 r5 r4 r3 r2 r1 r0,
   negative_flag r7,
   carry_flag cout,
   overflow_flag_sub a7 b7 r7).

(** * Specifications *)

Definition zero_flag_spec (r7 r6 r5 r4 r3 r2 r1 r0 : bool) : bool :=
  match (r7, r6, r5, r4, r3, r2, r1, r0) with
  | (false, false, false, false, false, false, false, false) => true
  | _ => false
  end.

(** * Verification *)

Theorem zero_flag_correct : forall r7 r6 r5 r4 r3 r2 r1 r0,
  zero_flag r7 r6 r5 r4 r3 r2 r1 r0 = zero_flag_spec r7 r6 r5 r4 r3 r2 r1 r0.
Proof.
  intros.
  unfold zero_flag, zero_flag_spec.
  destruct r7, r6, r5, r4, r3, r2, r1, r0; reflexivity.
Qed.

Theorem negative_flag_correct : forall r7,
  negative_flag r7 = r7.
Proof.
  reflexivity.
Qed.

Theorem carry_flag_correct : forall cout,
  carry_flag cout = cout.
Proof.
  reflexivity.
Qed.

(** Overflow detection for addition is correct. *)
Theorem overflow_add_positive_to_negative : forall r7,
  overflow_flag_add false false r7 = r7.
Proof.
  intros. unfold overflow_flag_add. destruct r7; reflexivity.
Qed.

Theorem overflow_add_negative_to_positive : forall r7,
  overflow_flag_add true true r7 = negb r7.
Proof.
  intros. unfold overflow_flag_add. destruct r7; reflexivity.
Qed.

Theorem overflow_add_mixed_signs : forall a7 r7,
  overflow_flag_add a7 (negb a7) r7 = false.
Proof.
  intros. unfold overflow_flag_add. destruct a7, r7; reflexivity.
Qed.

(** Overflow detection for subtraction. *)
Theorem overflow_sub_correct : forall a7 b7 r7,
  overflow_flag_sub a7 b7 r7 = andb (xorb a7 b7) (xorb a7 r7).
Proof.
  intros. unfold overflow_flag_sub.
  destruct a7, b7, r7; reflexivity.
Qed.

(** * Properties *)

(** Zero flag is true only for zero result. *)
Lemma zero_flag_all_false :
  zero_flag false false false false false false false false = true.
Proof. reflexivity. Qed.

Lemma zero_flag_any_true : forall r6 r5 r4 r3 r2 r1 r0,
  zero_flag true r6 r5 r4 r3 r2 r1 r0 = false.
Proof.
  intros. unfold zero_flag. reflexivity.
Qed.

(** Negative flag matches MSB. *)
Lemma negative_when_msb_set :
  negative_flag true = true.
Proof. reflexivity. Qed.

Lemma positive_when_msb_clear :
  negative_flag false = false.
Proof. reflexivity. Qed.

(** * Network Architecture *)

Definition zero_flag_neurons : nat := 1.
Definition zero_flag_params : nat := 9.

Definition negative_flag_neurons : nat := 1.
Definition negative_flag_params : nat := 2.

Definition carry_flag_neurons : nat := 1.
Definition carry_flag_params : nat := 2.

Definition overflow_flag_neurons : nat := 3.
Definition overflow_flag_params : nat := 9.

Definition alu_flags_total_neurons : nat := 6.
Definition alu_flags_total_params : nat := 22.
