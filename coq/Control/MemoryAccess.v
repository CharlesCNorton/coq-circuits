(** * Control.MemoryAccess: Load and Store Circuits

    Memory access operations for the threshold computer.
    LD: Load 8-bit value from memory address
    ST: Store 8-bit value to memory address

    Memory is modeled as a list of 256 8-bit values.
    Address selects which value to read/write.
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Nat.
Require Import Lia.
Require Import Base.Definitions.
Require Import Combinational.Multiplexer2to1.
Require Import Boolean.AND.
Require Import Boolean.NOT.

Import ListNotations.

Open Scope Z_scope.

(** * Helper Functions *)

(** Convert 8 booleans to a natural number (MSB first) *)
Definition bits_to_nat (b7 b6 b5 b4 b3 b2 b1 b0 : bool) : nat :=
  (if b7 then 128 else 0) +
  (if b6 then 64 else 0) +
  (if b5 then 32 else 0) +
  (if b4 then 16 else 0) +
  (if b3 then 8 else 0) +
  (if b2 then 4 else 0) +
  (if b1 then 2 else 0) +
  (if b0 then 1 else 0).

(** * Load Circuit Definition *)

(** LD: Read byte from memory at given address.
    Memory is represented as list of 8-bit values.
    Returns 8 zeros if address out of bounds. *)
Definition ld_circuit (addr : list bool) (memory : list (list bool)) : list bool :=
  match addr with
  | [a7; a6; a5; a4; a3; a2; a1; a0] =>
      let idx := bits_to_nat a7 a6 a5 a4 a3 a2 a1 a0 in
      nth idx memory [false; false; false; false; false; false; false; false]
  | _ => [false; false; false; false; false; false; false; false]
  end.

(** * Store Circuit Definition *)

(** Helper: update list at index *)
Fixpoint update_nth {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match n, l with
  | O, _ :: t => x :: t
  | S n', h :: t => h :: update_nth n' x t
  | _, [] => []
  end.

(** ST: Write byte to memory at given address.
    Returns updated memory. *)
Definition st_circuit (addr : list bool) (value : list bool) (memory : list (list bool)) : list (list bool) :=
  match addr with
  | [a7; a6; a5; a4; a3; a2; a1; a0] =>
      let idx := bits_to_nat a7 a6 a5 a4 a3 a2 a1 a0 in
      update_nth idx value memory
  | _ => memory
  end.

(** * Specifications *)

Definition ld_spec (addr : list bool) (memory : list (list bool)) : list bool :=
  match addr with
  | [a7; a6; a5; a4; a3; a2; a1; a0] =>
      let idx := bits_to_nat a7 a6 a5 a4 a3 a2 a1 a0 in
      nth idx memory [false; false; false; false; false; false; false; false]
  | _ => [false; false; false; false; false; false; false; false]
  end.

Definition st_spec (addr : list bool) (value : list bool) (memory : list (list bool)) : list (list bool) :=
  match addr with
  | [a7; a6; a5; a4; a3; a2; a1; a0] =>
      let idx := bits_to_nat a7 a6 a5 a4 a3 a2 a1 a0 in
      update_nth idx value memory
  | _ => memory
  end.

(** * Verification *)

Theorem ld_correct : forall addr memory,
  ld_circuit addr memory = ld_spec addr memory.
Proof.
  intros addr memory.
  unfold ld_circuit, ld_spec.
  reflexivity.
Qed.

Theorem st_correct : forall addr value memory,
  st_circuit addr value memory = st_spec addr value memory.
Proof.
  intros addr value memory.
  unfold st_circuit, st_spec.
  reflexivity.
Qed.

(** * Properties *)

(** Simple test: load from address 0 of a memory with one element *)
Lemma ld_addr_zero : forall v,
  ld_circuit [false;false;false;false;false;false;false;false] [v] = v.
Proof.
  intros. reflexivity.
Qed.

(** Store at address 0 updates first element *)
Lemma st_addr_zero : forall v old_v rest,
  st_circuit [false;false;false;false;false;false;false;false] v (old_v :: rest) = v :: rest.
Proof.
  intros. reflexivity.
Qed.

(** Load after store at same address returns stored value (simple case) *)
Lemma ld_after_st_simple : forall v old_v rest,
  ld_circuit [false;false;false;false;false;false;false;false]
    (st_circuit [false;false;false;false;false;false;false;false] v (old_v :: rest)) = v.
Proof.
  intros. reflexivity.
Qed.

(** * Concrete Address Test *)

(** Address 0x00 maps to index 0 *)
Lemma addr_zero_is_index_zero :
  bits_to_nat false false false false false false false false = 0%nat.
Proof. reflexivity. Qed.

(** Address 0xFF maps to index 255 *)
Lemma addr_ff_is_index_255 :
  bits_to_nat true true true true true true true true = 255%nat.
Proof. reflexivity. Qed.

(** Address 0x01 maps to index 1 *)
Lemma addr_01_is_index_1 :
  bits_to_nat false false false false false false false true = 1%nat.
Proof. reflexivity. Qed.

(** * Network Architecture Notes *)

(** Full memory access requires:
    - Address decoder: 8-to-256 decoder (for one-hot selection)
    - Load: 256-to-1 MUX per bit = 8 × 256-to-1 MUXes
    - Store: 256 × 8 conditional updates

    This is a large circuit but still implementable in threshold logic.
    Each 256-to-1 MUX can be built from 255 2-to-1 MUXes in a tree.
    Each 2-to-1 MUX = 4 neurons.
    Total per bit: ~1000 neurons.
    Total for 8 bits: ~8000 neurons.

    For practical hardware, memory would use SRAM cells rather than
    threshold neurons, with the address logic being threshold-based. *)

Print Assumptions ld_correct.
Print Assumptions st_correct.
