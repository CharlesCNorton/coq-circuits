(** * ALU.ALU8Bit: Complete 8-Bit Arithmetic Logic Unit

    A complete 8-bit ALU supporting 16 operations with flag computation.
    This is the computational core for building an 8-bit computer.

    Operations:
    - Arithmetic: ADD, SUB, INC, DEC, NEG, CMP
    - Logic: AND, OR, XOR, NOT
    - Shift: SHL, SHR
    - Data: PASS, ZERO, ONES, NOP
*)

Require Import Bool.
Require Import List.
Import ListNotations.

(** * Basic Operations *)

(** 8-bit type. *)
Definition byte := (bool * bool * bool * bool * bool * bool * bool * bool)%type.

Definition byte_to_list (b : byte) : list bool :=
  match b with
  | (b7, b6, b5, b4, b3, b2, b1, b0) => [b7; b6; b5; b4; b3; b2; b1; b0]
  end.

(** * Bitwise Operations *)

Definition bitwise_and (a b : byte) : byte :=
  match a, b with
  | (a7,a6,a5,a4,a3,a2,a1,a0), (b7,b6,b5,b4,b3,b2,b1,b0) =>
    (andb a7 b7, andb a6 b6, andb a5 b5, andb a4 b4,
     andb a3 b3, andb a2 b2, andb a1 b1, andb a0 b0)
  end.

Definition bitwise_or (a b : byte) : byte :=
  match a, b with
  | (a7,a6,a5,a4,a3,a2,a1,a0), (b7,b6,b5,b4,b3,b2,b1,b0) =>
    (orb a7 b7, orb a6 b6, orb a5 b5, orb a4 b4,
     orb a3 b3, orb a2 b2, orb a1 b1, orb a0 b0)
  end.

Definition bitwise_xor (a b : byte) : byte :=
  match a, b with
  | (a7,a6,a5,a4,a3,a2,a1,a0), (b7,b6,b5,b4,b3,b2,b1,b0) =>
    (xorb a7 b7, xorb a6 b6, xorb a5 b5, xorb a4 b4,
     xorb a3 b3, xorb a2 b2, xorb a1 b1, xorb a0 b0)
  end.

Definition bitwise_not (a : byte) : byte :=
  match a with
  | (a7,a6,a5,a4,a3,a2,a1,a0) =>
    (negb a7, negb a6, negb a5, negb a4,
     negb a3, negb a2, negb a1, negb a0)
  end.

(** * Shift Operations *)

Definition shift_left (a : byte) : byte * bool :=
  match a with
  | (a7,a6,a5,a4,a3,a2,a1,a0) =>
    ((a6, a5, a4, a3, a2, a1, a0, false), a7)
  end.

Definition shift_right (a : byte) : byte * bool :=
  match a with
  | (a7,a6,a5,a4,a3,a2,a1,a0) =>
    ((false, a7, a6, a5, a4, a3, a2, a1), a0)
  end.

(** * Arithmetic Operations *)

(** Full adder for single bit. *)
Definition full_add (a b cin : bool) : bool * bool :=
  (xorb (xorb a b) cin, orb (andb a b) (andb cin (xorb a b))).

(** 8-bit ripple carry adder. Returns (result, carry_out). *)
Definition add_8bit (a b : byte) (cin : bool) : byte * bool :=
  match a, b with
  | (a7,a6,a5,a4,a3,a2,a1,a0), (b7,b6,b5,b4,b3,b2,b1,b0) =>
    let '(s0, c0) := full_add a0 b0 cin in
    let '(s1, c1) := full_add a1 b1 c0 in
    let '(s2, c2) := full_add a2 b2 c1 in
    let '(s3, c3) := full_add a3 b3 c2 in
    let '(s4, c4) := full_add a4 b4 c3 in
    let '(s5, c5) := full_add a5 b5 c4 in
    let '(s6, c6) := full_add a6 b6 c5 in
    let '(s7, c7) := full_add a7 b7 c6 in
    ((s7, s6, s5, s4, s3, s2, s1, s0), c7)
  end.

(** Subtraction via two's complement: A - B = A + (~B) + 1. *)
Definition sub_8bit (a b : byte) : byte * bool :=
  add_8bit a (bitwise_not b) true.

(** Increment: A + 1. *)
Definition inc_8bit (a : byte) : byte * bool :=
  add_8bit a (false,false,false,false,false,false,false,false) true.

(** Decrement: A - 1. *)
Definition dec_8bit (a : byte) : byte * bool :=
  add_8bit a (true,true,true,true,true,true,true,true) false.

(** Negate: -A = ~A + 1 (two's complement). *)
Definition neg_8bit (a : byte) : byte * bool :=
  add_8bit (bitwise_not a) (false,false,false,false,false,false,false,false) true.

(** * Constants *)

Definition byte_zero : byte := (false,false,false,false,false,false,false,false).
Definition byte_ones : byte := (true,true,true,true,true,true,true,true).
Definition byte_one  : byte := (false,false,false,false,false,false,false,true).

(** * Flag Computation *)

Definition zero_flag (r : byte) : bool :=
  match r with
  | (r7,r6,r5,r4,r3,r2,r1,r0) =>
    negb (orb r7 (orb r6 (orb r5 (orb r4 (orb r3 (orb r2 (orb r1 r0)))))))
  end.

Definition negative_flag (r : byte) : bool :=
  match r with (r7,_,_,_,_,_,_,_) => r7 end.

Definition overflow_flag (a7 b7 r7 : bool) (is_sub : bool) : bool :=
  if is_sub
  then andb (xorb a7 b7) (xorb a7 r7)
  else andb (Bool.eqb a7 b7) (xorb a7 r7).

(** Flags record: (Zero, Negative, Carry, Overflow). *)
Definition flags := (bool * bool * bool * bool)%type.

(** * ALU Core *)

(** ALU operation with result and flags. *)
Definition alu_op (op3 op2 op1 op0 : bool) (a b : byte) : byte * flags :=
  let a7 := match a with (x,_,_,_,_,_,_,_) => x end in
  let b7 := match b with (x,_,_,_,_,_,_,_) => x end in
  match (op3, op2, op1, op0) with
  | (false, false, false, false) =>
      let '(r, cout) := add_8bit a b false in
      let r7 := match r with (x,_,_,_,_,_,_,_) => x end in
      (r, (zero_flag r, negative_flag r, cout, overflow_flag a7 b7 r7 false))
  | (false, false, false, true) =>
      let '(r, cout) := sub_8bit a b in
      let r7 := match r with (x,_,_,_,_,_,_,_) => x end in
      (r, (zero_flag r, negative_flag r, cout, overflow_flag a7 b7 r7 true))
  | (false, false, true, false) =>
      let r := bitwise_and a b in
      (r, (zero_flag r, negative_flag r, false, false))
  | (false, false, true, true) =>
      let r := bitwise_or a b in
      (r, (zero_flag r, negative_flag r, false, false))
  | (false, true, false, false) =>
      let r := bitwise_xor a b in
      (r, (zero_flag r, negative_flag r, false, false))
  | (false, true, false, true) =>
      let r := bitwise_not a in
      (r, (zero_flag r, negative_flag r, false, false))
  | (false, true, true, false) =>
      let '(r, cout) := shift_left a in
      (r, (zero_flag r, negative_flag r, cout, false))
  | (false, true, true, true) =>
      let '(r, cout) := shift_right a in
      (r, (zero_flag r, negative_flag r, cout, false))
  | (true, false, false, false) =>
      let '(r, cout) := inc_8bit a in
      let r7 := match r with (x,_,_,_,_,_,_,_) => x end in
      (r, (zero_flag r, negative_flag r, cout, overflow_flag a7 false r7 false))
  | (true, false, false, true) =>
      let '(r, cout) := dec_8bit a in
      let r7 := match r with (x,_,_,_,_,_,_,_) => x end in
      (r, (zero_flag r, negative_flag r, cout, overflow_flag a7 true r7 true))
  | (true, false, true, false) =>
      let '(r, cout) := sub_8bit a b in
      let r7 := match r with (x,_,_,_,_,_,_,_) => x end in
      (r, (zero_flag r, negative_flag r, cout, overflow_flag a7 b7 r7 true))
  | (true, false, true, true) =>
      let '(r, cout) := neg_8bit a in
      let r7 := match r with (x,_,_,_,_,_,_,_) => x end in
      (r, (zero_flag r, negative_flag r, cout, andb a7 r7))
  | (true, true, false, false) =>
      (a, (zero_flag a, negative_flag a, false, false))
  | (true, true, false, true) =>
      (byte_zero, (true, false, false, false))
  | (true, true, true, false) =>
      (byte_ones, (false, true, false, false))
  | (true, true, true, true) =>
      (a, (zero_flag a, negative_flag a, false, false))
  end.

(** * Verification *)

(** ADD: 5 + 3 = 8. *)
Lemma alu_add_5_3 :
  fst (alu_op false false false false
    (false,false,false,false,false,true,false,true)
    (false,false,false,false,false,false,true,true))
  = (false,false,false,false,true,false,false,false).
Proof. reflexivity. Qed.

(** SUB: 10 - 3 = 7. *)
Lemma alu_sub_10_3 :
  fst (alu_op false false false true
    (false,false,false,false,true,false,true,false)
    (false,false,false,false,false,false,true,true))
  = (false,false,false,false,false,true,true,true).
Proof. reflexivity. Qed.

(** AND: 0xF0 AND 0x0F = 0x00. *)
Lemma alu_and_f0_0f :
  fst (alu_op false false true false
    (true,true,true,true,false,false,false,false)
    (false,false,false,false,true,true,true,true))
  = byte_zero.
Proof. reflexivity. Qed.

(** OR: 0xF0 OR 0x0F = 0xFF. *)
Lemma alu_or_f0_0f :
  fst (alu_op false false true true
    (true,true,true,true,false,false,false,false)
    (false,false,false,false,true,true,true,true))
  = byte_ones.
Proof. reflexivity. Qed.

(** XOR: 0xFF XOR 0xFF = 0x00. *)
Lemma alu_xor_ff_ff :
  fst (alu_op false true false false byte_ones byte_ones) = byte_zero.
Proof. reflexivity. Qed.

(** NOT: NOT 0x00 = 0xFF. *)
Lemma alu_not_00 :
  fst (alu_op false true false true byte_zero byte_zero) = byte_ones.
Proof. reflexivity. Qed.

(** SHL: 0x01 << 1 = 0x02. *)
Lemma alu_shl_01 :
  fst (alu_op false true true false byte_one byte_zero)
  = (false,false,false,false,false,false,true,false).
Proof. reflexivity. Qed.

(** SHR: 0x02 >> 1 = 0x01. *)
Lemma alu_shr_02 :
  fst (alu_op false true true true
    (false,false,false,false,false,false,true,false) byte_zero)
  = byte_one.
Proof. reflexivity. Qed.

(** INC: 0 + 1 = 1. *)
Lemma alu_inc_0 :
  fst (alu_op true false false false byte_zero byte_zero) = byte_one.
Proof. reflexivity. Qed.

(** DEC: 1 - 1 = 0. *)
Lemma alu_dec_1 :
  fst (alu_op true false false true byte_one byte_zero) = byte_zero.
Proof. reflexivity. Qed.

(** ZERO flag set when result is zero. *)
Lemma alu_zero_flag_set :
  match snd (alu_op false false false true byte_one byte_one) with
  | (z, _, _, _) => z
  end = true.
Proof. reflexivity. Qed.

(** Negative flag set when MSB is 1. *)
Lemma alu_negative_flag_set :
  match snd (alu_op false false false false
    (true,false,false,false,false,false,false,false)
    (false,false,false,false,false,false,false,false)) with
  | (_, n, _, _) => n
  end = true.
Proof. reflexivity. Qed.

(** PASS returns input unchanged. *)
Lemma alu_pass :
  forall a b, fst (alu_op true true false false a b) = a.
Proof. intros. reflexivity. Qed.

(** ZERO outputs zero. *)
Lemma alu_zero_output :
  forall a b, fst (alu_op true true false true a b) = byte_zero.
Proof. intros. reflexivity. Qed.

(** ONES outputs 0xFF. *)
Lemma alu_ones_output :
  forall a b, fst (alu_op true true true false a b) = byte_ones.
Proof. intros. reflexivity. Qed.

(** * Properties *)

(** * Algebraic Lemmas for Commutativity *)

Lemma andb_comm : forall a b, andb a b = andb b a.
Proof. destruct a, b; reflexivity. Qed.

Lemma orb_comm : forall a b, orb a b = orb b a.
Proof. destruct a, b; reflexivity. Qed.

Lemma xorb_comm : forall a b, xorb a b = xorb b a.
Proof. destruct a, b; reflexivity. Qed.

(** Full adder is commutative in first two arguments. *)
Lemma full_add_comm : forall a b c,
  full_add a b c = full_add b a c.
Proof.
  intros. unfold full_add.
  rewrite (xorb_comm a b).
  rewrite (andb_comm a b).
  reflexivity.
Qed.

(** Bitwise AND is commutative. *)
Lemma bitwise_and_comm : forall a b, bitwise_and a b = bitwise_and b a.
Proof.
  intros.
  destruct a as [[[[[[[a7 a6] a5] a4] a3] a2] a1] a0].
  destruct b as [[[[[[[b7 b6] b5] b4] b3] b2] b1] b0].
  unfold bitwise_and.
  rewrite (andb_comm a7 b7), (andb_comm a6 b6), (andb_comm a5 b5), (andb_comm a4 b4).
  rewrite (andb_comm a3 b3), (andb_comm a2 b2), (andb_comm a1 b1), (andb_comm a0 b0).
  reflexivity.
Qed.

(** Bitwise OR is commutative. *)
Lemma bitwise_or_comm : forall a b, bitwise_or a b = bitwise_or b a.
Proof.
  intros.
  destruct a as [[[[[[[a7 a6] a5] a4] a3] a2] a1] a0].
  destruct b as [[[[[[[b7 b6] b5] b4] b3] b2] b1] b0].
  unfold bitwise_or.
  rewrite (orb_comm a7 b7), (orb_comm a6 b6), (orb_comm a5 b5), (orb_comm a4 b4).
  rewrite (orb_comm a3 b3), (orb_comm a2 b2), (orb_comm a1 b1), (orb_comm a0 b0).
  reflexivity.
Qed.

(** Bitwise XOR is commutative. *)
Lemma bitwise_xor_comm : forall a b, bitwise_xor a b = bitwise_xor b a.
Proof.
  intros.
  destruct a as [[[[[[[a7 a6] a5] a4] a3] a2] a1] a0].
  destruct b as [[[[[[[b7 b6] b5] b4] b3] b2] b1] b0].
  unfold bitwise_xor.
  rewrite (xorb_comm a7 b7), (xorb_comm a6 b6), (xorb_comm a5 b5), (xorb_comm a4 b4).
  rewrite (xorb_comm a3 b3), (xorb_comm a2 b2), (xorb_comm a1 b1), (xorb_comm a0 b0).
  reflexivity.
Qed.

(** 8-bit addition is commutative. *)
Lemma add_8bit_comm : forall a b cin, add_8bit a b cin = add_8bit b a cin.
Proof.
  intros.
  destruct a as [[[[[[[a7 a6] a5] a4] a3] a2] a1] a0].
  destruct b as [[[[[[[b7 b6] b5] b4] b3] b2] b1] b0].
  unfold add_8bit.
  rewrite (full_add_comm a0 b0 cin).
  remember (full_add b0 a0 cin) as r0. destruct r0 as [s0 c0].
  rewrite (full_add_comm a1 b1 c0).
  remember (full_add b1 a1 c0) as r1. destruct r1 as [s1 c1].
  rewrite (full_add_comm a2 b2 c1).
  remember (full_add b2 a2 c1) as r2. destruct r2 as [s2 c2].
  rewrite (full_add_comm a3 b3 c2).
  remember (full_add b3 a3 c2) as r3. destruct r3 as [s3 c3].
  rewrite (full_add_comm a4 b4 c3).
  remember (full_add b4 a4 c3) as r4. destruct r4 as [s4 c4].
  rewrite (full_add_comm a5 b5 c4).
  remember (full_add b5 a5 c4) as r5. destruct r5 as [s5 c5].
  rewrite (full_add_comm a6 b6 c5).
  remember (full_add b6 a6 c5) as r6. destruct r6 as [s6 c6].
  rewrite (full_add_comm a7 b7 c6).
  reflexivity.
Qed.

(** * ALU Properties *)

(** ADD result is commutative. *)
Theorem alu_add_comm : forall a b,
  fst (alu_op false false false false a b) =
  fst (alu_op false false false false b a).
Proof.
  intros.
  destruct a as [[[[[[[a7 a6] a5] a4] a3] a2] a1] a0].
  destruct b as [[[[[[[b7 b6] b5] b4] b3] b2] b1] b0].
  unfold alu_op.
  rewrite add_8bit_comm. reflexivity.
Qed.

(** AND is commutative. *)
Theorem alu_and_comm : forall a b,
  fst (alu_op false false true false a b) =
  fst (alu_op false false true false b a).
Proof.
  intros. unfold alu_op.
  rewrite bitwise_and_comm. reflexivity.
Qed.

(** OR is commutative. *)
Theorem alu_or_comm : forall a b,
  fst (alu_op false false true true a b) =
  fst (alu_op false false true true b a).
Proof.
  intros. unfold alu_op.
  rewrite bitwise_or_comm. reflexivity.
Qed.

(** XOR is commutative. *)
Theorem alu_xor_comm : forall a b,
  fst (alu_op false true false false a b) =
  fst (alu_op false true false false b a).
Proof.
  intros. unfold alu_op.
  rewrite bitwise_xor_comm. reflexivity.
Qed.

(** NOT is involutive. *)
Theorem alu_not_involutive : forall a,
  fst (alu_op false true false true
    (fst (alu_op false true false true a byte_zero)) byte_zero) = a.
Proof.
  intros.
  destruct a as [[[[[[[a7 a6] a5] a4] a3] a2] a1] a0].
  unfold alu_op, bitwise_not.
  destruct a7, a6, a5, a4, a3, a2, a1, a0;
  reflexivity.
Qed.

(** ADD with zero is identity. *)
Theorem alu_add_zero_right : forall a,
  fst (alu_op false false false false a byte_zero) = a.
Proof.
  intros.
  destruct a as [[[[[[[a7 a6] a5] a4] a3] a2] a1] a0].
  unfold alu_op, add_8bit, full_add, byte_zero.
  destruct a7, a6, a5, a4, a3, a2, a1, a0;
  reflexivity.
Qed.

(** AND with ones is identity. *)
Theorem alu_and_ones_right : forall a,
  fst (alu_op false false true false a byte_ones) = a.
Proof.
  intros.
  destruct a as [[[[[[[a7 a6] a5] a4] a3] a2] a1] a0].
  unfold alu_op, bitwise_and, byte_ones.
  destruct a7, a6, a5, a4, a3, a2, a1, a0;
  reflexivity.
Qed.

(** OR with zero is identity. *)
Theorem alu_or_zero_right : forall a,
  fst (alu_op false false true true a byte_zero) = a.
Proof.
  intros.
  destruct a as [[[[[[[a7 a6] a5] a4] a3] a2] a1] a0].
  unfold alu_op, bitwise_or, byte_zero.
  destruct a7, a6, a5, a4, a3, a2, a1, a0;
  reflexivity.
Qed.

(** XOR with zero is identity. *)
Theorem alu_xor_zero_right : forall a,
  fst (alu_op false true false false a byte_zero) = a.
Proof.
  intros.
  destruct a as [[[[[[[a7 a6] a5] a4] a3] a2] a1] a0].
  unfold alu_op, bitwise_xor, byte_zero.
  destruct a7, a6, a5, a4, a3, a2, a1, a0;
  reflexivity.
Qed.

(** XOR with self is zero. *)
Theorem alu_xor_self : forall a,
  fst (alu_op false true false false a a) = byte_zero.
Proof.
  intros.
  destruct a as [[[[[[[a7 a6] a5] a4] a3] a2] a1] a0].
  unfold alu_op, bitwise_xor, byte_zero.
  destruct a7, a6, a5, a4, a3, a2, a1, a0;
  reflexivity.
Qed.

(** SUB from self is zero. *)
Theorem alu_sub_self : forall a,
  fst (alu_op false false false true a a) = byte_zero.
Proof.
  intros.
  destruct a as [[[[[[[a7 a6] a5] a4] a3] a2] a1] a0].
  unfold alu_op, sub_8bit, add_8bit, bitwise_not, full_add, byte_zero.
  destruct a7, a6, a5, a4, a3, a2, a1, a0;
  reflexivity.
Qed.

(** * Network Architecture *)

Definition alu_8bit_neurons : nat := 256.
Definition alu_8bit_params : nat := 1024.
Definition alu_8bit_depth : nat := 8.
