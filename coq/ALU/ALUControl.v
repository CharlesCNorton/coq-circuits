(** * ALU.ALUControl: Opcode Decoder for 8-Bit ALU

    Decodes 4-bit opcodes into control signals for ALU operations.

    Opcodes:
    - 0000 (0):  ADD  - Addition
    - 0001 (1):  SUB  - Subtraction
    - 0010 (2):  AND  - Bitwise AND
    - 0011 (3):  OR   - Bitwise OR
    - 0100 (4):  XOR  - Bitwise XOR
    - 0101 (5):  NOT  - Bitwise NOT (unary, uses A only)
    - 0110 (6):  SHL  - Shift left by 1
    - 0111 (7):  SHR  - Shift right by 1
    - 1000 (8):  INC  - Increment A
    - 1001 (9):  DEC  - Decrement A
    - 1010 (10): CMP  - Compare (SUB but discard result, flags only)
    - 1011 (11): NEG  - Negate (two's complement)
    - 1100 (12): PASS - Pass A through unchanged
    - 1101 (13): ZERO - Output zero
    - 1110 (14): ONES - Output all ones (0xFF)
    - 1111 (15): NOP  - No operation (pass A)
*)

Require Import Bool.
Require Import List.
Import ListNotations.

(** * Opcode Definitions *)

(** Opcode type as 4 bits. *)
Definition opcode := (bool * bool * bool * bool)%type.

Definition OP_ADD  : opcode := (false, false, false, false).
Definition OP_SUB  : opcode := (false, false, false, true).
Definition OP_AND  : opcode := (false, false, true, false).
Definition OP_OR   : opcode := (false, false, true, true).
Definition OP_XOR  : opcode := (false, true, false, false).
Definition OP_NOT  : opcode := (false, true, false, true).
Definition OP_SHL  : opcode := (false, true, true, false).
Definition OP_SHR  : opcode := (false, true, true, true).
Definition OP_INC  : opcode := (true, false, false, false).
Definition OP_DEC  : opcode := (true, false, false, true).
Definition OP_CMP  : opcode := (true, false, true, false).
Definition OP_NEG  : opcode := (true, false, true, true).
Definition OP_PASS : opcode := (true, true, false, false).
Definition OP_ZERO : opcode := (true, true, false, true).
Definition OP_ONES : opcode := (true, true, true, false).
Definition OP_NOP  : opcode := (true, true, true, true).

(** * Control Signal Decoding *)

(** Is this an arithmetic operation (ADD, SUB, INC, DEC, NEG, CMP)? *)
Definition is_arithmetic (op3 op2 op1 op0 : bool) : bool :=
  match (op3, op2, op1, op0) with
  | (false, false, false, false) => true
  | (false, false, false, true)  => true
  | (true, false, false, false)  => true
  | (true, false, false, true)   => true
  | (true, false, true, false)   => true
  | (true, false, true, true)    => true
  | _ => false
  end.

(** Is this a logic operation (AND, OR, XOR, NOT)? *)
Definition is_logic (op3 op2 op1 op0 : bool) : bool :=
  match (op3, op2, op1, op0) with
  | (false, false, true, false) => true
  | (false, false, true, true)  => true
  | (false, true, false, false) => true
  | (false, true, false, true)  => true
  | _ => false
  end.

(** Is this a shift operation (SHL, SHR)? *)
Definition is_shift (op3 op2 op1 op0 : bool) : bool :=
  match (op3, op2, op1, op0) with
  | (false, true, true, false) => true
  | (false, true, true, true)  => true
  | _ => false
  end.

(** Does operation use subtraction path (SUB, CMP, DEC, NEG)? *)
Definition use_subtract (op3 op2 op1 op0 : bool) : bool :=
  match (op3, op2, op1, op0) with
  | (false, false, false, true)  => true
  | (true, false, false, true)   => true
  | (true, false, true, false)   => true
  | (true, false, true, true)    => true
  | _ => false
  end.

(** Does operation use B input (vs constant or A only)? *)
Definition use_b_input (op3 op2 op1 op0 : bool) : bool :=
  match (op3, op2, op1, op0) with
  | (false, false, false, false) => true
  | (false, false, false, true)  => true
  | (false, false, true, false)  => true
  | (false, false, true, true)   => true
  | (false, true, false, false)  => true
  | (true, false, true, false)   => true
  | _ => false
  end.

(** Should result be written (false for CMP, NOP)? *)
Definition write_result (op3 op2 op1 op0 : bool) : bool :=
  match (op3, op2, op1, op0) with
  | (true, false, true, false) => false
  | (true, true, true, true)   => false
  | _ => true
  end.

(** * Operation Selection *)

(** Decode opcode to operation selector (one-hot for 16 operations). *)
Definition decode_op (op3 op2 op1 op0 : bool) : nat :=
  (if op3 then 8 else 0) + (if op2 then 4 else 0) +
  (if op1 then 2 else 0) + (if op0 then 1 else 0).

(** * Verification *)

Theorem decode_add : decode_op false false false false = 0.
Proof. reflexivity. Qed.

Theorem decode_sub : decode_op false false false true = 1.
Proof. reflexivity. Qed.

Theorem decode_and : decode_op false false true false = 2.
Proof. reflexivity. Qed.

Theorem decode_or : decode_op false false true true = 3.
Proof. reflexivity. Qed.

Theorem decode_xor : decode_op false true false false = 4.
Proof. reflexivity. Qed.

Theorem decode_not : decode_op false true false true = 5.
Proof. reflexivity. Qed.

Theorem decode_shl : decode_op false true true false = 6.
Proof. reflexivity. Qed.

Theorem decode_shr : decode_op false true true true = 7.
Proof. reflexivity. Qed.

Theorem decode_inc : decode_op true false false false = 8.
Proof. reflexivity. Qed.

Theorem decode_dec : decode_op true false false true = 9.
Proof. reflexivity. Qed.

Theorem decode_cmp : decode_op true false true false = 10.
Proof. reflexivity. Qed.

Theorem decode_neg : decode_op true false true true = 11.
Proof. reflexivity. Qed.

Theorem decode_pass : decode_op true true false false = 12.
Proof. reflexivity. Qed.

Theorem decode_zero : decode_op true true false true = 13.
Proof. reflexivity. Qed.

Theorem decode_ones : decode_op true true true false = 14.
Proof. reflexivity. Qed.

Theorem decode_nop : decode_op true true true true = 15.
Proof. reflexivity. Qed.

(** Control signal correctness. *)
Theorem arithmetic_ops_correct : forall op3 op2 op1 op0,
  is_arithmetic op3 op2 op1 op0 = true ->
  (decode_op op3 op2 op1 op0 = 0 \/
   decode_op op3 op2 op1 op0 = 1 \/
   decode_op op3 op2 op1 op0 = 8 \/
   decode_op op3 op2 op1 op0 = 9 \/
   decode_op op3 op2 op1 op0 = 10 \/
   decode_op op3 op2 op1 op0 = 11).
Proof.
  intros op3 op2 op1 op0 H.
  destruct op3, op2, op1, op0; simpl in H; try discriminate; simpl;
  (left; reflexivity) ||
  (right; left; reflexivity) ||
  (right; right; left; reflexivity) ||
  (right; right; right; left; reflexivity) ||
  (right; right; right; right; left; reflexivity) ||
  (right; right; right; right; right; reflexivity).
Qed.

Theorem logic_ops_correct : forall op3 op2 op1 op0,
  is_logic op3 op2 op1 op0 = true ->
  (decode_op op3 op2 op1 op0 = 2 \/
   decode_op op3 op2 op1 op0 = 3 \/
   decode_op op3 op2 op1 op0 = 4 \/
   decode_op op3 op2 op1 op0 = 5).
Proof.
  intros op3 op2 op1 op0 H.
  destruct op3, op2, op1, op0; simpl in H; try discriminate; simpl;
  (left; reflexivity) ||
  (right; left; reflexivity) ||
  (right; right; left; reflexivity) ||
  (right; right; right; reflexivity).
Qed.

Theorem shift_ops_correct : forall op3 op2 op1 op0,
  is_shift op3 op2 op1 op0 = true ->
  (decode_op op3 op2 op1 op0 = 6 \/
   decode_op op3 op2 op1 op0 = 7).
Proof.
  intros op3 op2 op1 op0 H.
  destruct op3, op2, op1, op0; simpl in H; try discriminate; simpl;
  (left; reflexivity) || (right; reflexivity).
Qed.

(** * Properties *)

(** All opcodes decode to valid range. *)
Theorem decode_range : forall op3 op2 op1 op0,
  Nat.ltb (decode_op op3 op2 op1 op0) 16 = true.
Proof.
  intros.
  destruct op3, op2, op1, op0; reflexivity.
Qed.

(** Decoding is injective. *)
Theorem decode_injective : forall a3 a2 a1 a0 b3 b2 b1 b0,
  decode_op a3 a2 a1 a0 = decode_op b3 b2 b1 b0 ->
  (a3, a2, a1, a0) = (b3, b2, b1, b0).
Proof.
  intros.
  unfold decode_op in H.
  destruct a3, a2, a1, a0, b3, b2, b1, b0; simpl in H;
  try reflexivity; try discriminate.
Qed.

(** * Network Architecture *)

Definition control_decoder_neurons : nat := 16.
Definition control_decoder_params : nat := 80.
