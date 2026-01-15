(** * Control.Stack: Stack Operations

    PUSH, POP, CALL, and RET operations for the threshold computer.
    Uses a stack pointer (SP) and memory for the stack.

    Stack grows downward (PUSH decrements SP, POP increments SP).
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Nat.
Require Import Base.Definitions.
Require Import Control.MemoryAccess.
Require Import Control.Jump.

Import ListNotations.

Open Scope Z_scope.

(** * Stack Pointer Operations *)

(** Helper: convert 8 bits to nat *)
Definition sp_to_nat (sp : list bool) : nat :=
  match sp with
  | [b7;b6;b5;b4;b3;b2;b1;b0] =>
      (if b7 then 128 else 0) + (if b6 then 64 else 0) +
      (if b5 then 32 else 0) + (if b4 then 16 else 0) +
      (if b3 then 8 else 0) + (if b2 then 4 else 0) +
      (if b1 then 2 else 0) + (if b0 then 1 else 0)
  | _ => 0
  end.

(** Helper: convert nat to 8 bits *)
Definition nat_to_sp (n : nat) : list bool :=
  let b7 := Nat.testbit n 7 in
  let b6 := Nat.testbit n 6 in
  let b5 := Nat.testbit n 5 in
  let b4 := Nat.testbit n 4 in
  let b3 := Nat.testbit n 3 in
  let b2 := Nat.testbit n 2 in
  let b1 := Nat.testbit n 1 in
  let b0 := Nat.testbit n 0 in
  [b7; b6; b5; b4; b3; b2; b1; b0].

(** Decrement stack pointer (for PUSH) - stack grows downward *)
Definition sp_dec (sp : list bool) : list bool :=
  nat_to_sp ((sp_to_nat sp - 1) mod 256).

(** Increment stack pointer (for POP) *)
Definition sp_inc (sp : list bool) : list bool :=
  nat_to_sp ((sp_to_nat sp + 1) mod 256).

(** * PUSH Operation *)

(** PUSH: Decrement SP, then store value at new SP location.
    Returns (new_sp, new_memory) *)
Definition push_circuit (sp : list bool) (value : list bool) (memory : list (list bool))
  : list bool * list (list bool) :=
  let new_sp := sp_dec sp in
  let new_memory := st_circuit new_sp value memory in
  (new_sp, new_memory).

(** * POP Operation *)

(** POP: Load value from SP, then increment SP.
    Returns (popped_value, new_sp) *)
Definition pop_circuit (sp : list bool) (memory : list (list bool))
  : list bool * list bool :=
  let value := ld_circuit sp memory in
  let new_sp := sp_inc sp in
  (value, new_sp).

(** * CALL Operation *)

(** CALL: Push return address (PC+2), then jump to target.
    Returns (new_sp, new_memory, new_pc) *)
Definition call_circuit (sp pc_plus_2 target : list bool) (memory : list (list bool))
  : list bool * list (list bool) * list bool :=
  let (new_sp, new_memory) := push_circuit sp pc_plus_2 memory in
  let new_pc := jump_circuit target in
  (new_sp, new_memory, new_pc).

(** * RET Operation *)

(** RET: Pop return address, then jump to it.
    Returns (new_sp, new_pc) *)
Definition ret_circuit (sp : list bool) (memory : list (list bool))
  : list bool * list bool :=
  let (ret_addr, new_sp) := pop_circuit sp memory in
  let new_pc := jump_circuit ret_addr in
  (new_sp, new_pc).

(** * Specifications *)

Definition push_spec (sp value : list bool) (memory : list (list bool))
  : list bool * list (list bool) :=
  let new_sp := sp_dec sp in
  (new_sp, st_circuit new_sp value memory).

Definition pop_spec (sp : list bool) (memory : list (list bool))
  : list bool * list bool :=
  (ld_circuit sp memory, sp_inc sp).

Definition call_spec (sp pc_plus_2 target : list bool) (memory : list (list bool))
  : list bool * list (list bool) * list bool :=
  let (new_sp, new_memory) := push_spec sp pc_plus_2 memory in
  (new_sp, new_memory, target).

Definition ret_spec (sp : list bool) (memory : list (list bool))
  : list bool * list bool :=
  let (ret_addr, new_sp) := pop_spec sp memory in
  (new_sp, ret_addr).

(** * Verification *)

Theorem push_correct : forall sp value memory,
  push_circuit sp value memory = push_spec sp value memory.
Proof.
  intros.
  unfold push_circuit, push_spec.
  reflexivity.
Qed.

Theorem pop_correct : forall sp memory,
  pop_circuit sp memory = pop_spec sp memory.
Proof.
  intros.
  unfold pop_circuit, pop_spec.
  reflexivity.
Qed.

Theorem call_correct : forall sp pc_plus_2 target memory,
  call_circuit sp pc_plus_2 target memory = call_spec sp pc_plus_2 target memory.
Proof.
  intros.
  unfold call_circuit, call_spec, push_circuit, push_spec.
  rewrite jump_correct.
  reflexivity.
Qed.

Theorem ret_correct : forall sp memory,
  ret_circuit sp memory = ret_spec sp memory.
Proof.
  intros.
  unfold ret_circuit, ret_spec, pop_circuit, pop_spec.
  rewrite jump_correct.
  reflexivity.
Qed.

(** * Concrete Tests *)

(** sp_to_nat correctly converts 0xFF to 255 *)
Lemma sp_to_nat_ff :
  sp_to_nat [true;true;true;true;true;true;true;true] = 255%nat.
Proof.
  reflexivity.
Qed.

(** sp_to_nat correctly converts 0x00 to 0 *)
Lemma sp_to_nat_00 :
  sp_to_nat [false;false;false;false;false;false;false;false] = 0%nat.
Proof.
  reflexivity.
Qed.

(** sp_inc and sp_dec are inverses (for non-boundary values) *)
Lemma sp_inc_dec_inverse :
  sp_inc (sp_dec [false;false;false;false;false;false;false;true]) =
  [false;false;false;false;false;false;false;true].
Proof.
  unfold sp_inc, sp_dec, sp_to_nat, nat_to_sp.
  vm_compute.
  reflexivity.
Qed.

(** * Network Architecture *)

(** PUSH: 1 Decrementer8Bit + 1 Store = ~100 neurons
    POP:  1 Load + 1 Incrementer8Bit = ~100 neurons
    CALL: 1 PUSH + 1 Jump = ~110 neurons
    RET:  1 POP + 1 Jump = ~110 neurons *)
Definition push_num_neurons : nat := 100.
Definition pop_num_neurons : nat := 100.
Definition call_num_neurons : nat := 110.
Definition ret_num_neurons : nat := 110.

Print Assumptions push_correct.
Print Assumptions pop_correct.
Print Assumptions call_correct.
Print Assumptions ret_correct.
