(** * Base.Composition: Circuit Composition Rules

    Rules and utilities for composing threshold circuits.
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Lia.
Require Import Base.Definitions.
Require Import Base.Tactics.
Require Import Base.Verification.

Import ListNotations.

Open Scope Z_scope.

(** * Sequential Composition *)

(** Compose two boolean functions sequentially.
    Output of f feeds into g (when g takes single boolean input). *)
Definition compose_seq_bool (f : list bool -> bool) (g : bool -> bool)
  : list bool -> bool
  := fun xs => g (f xs).

(** Compose two natural-valued functions sequentially. *)
Definition compose_seq_nat (f : list bool -> nat) (g : nat -> nat)
  : list bool -> nat
  := fun xs => g (f xs).

(** * Parallel Composition *)

(** Apply multiple circuits to same input, collect outputs. *)
Definition parallel_compose (fs : list (list bool -> bool))
  : list bool -> list bool
  := fun xs => map (fun f => f xs) fs.

(** Apply multiple natural-valued circuits to same input. *)
Definition parallel_compose_nat (fs : list (list bool -> nat))
  : list bool -> list nat
  := fun xs => map (fun f => f xs) fs.

(** * Layered Composition *)

(** Apply first circuit, feed output to second circuit.
    Second circuit must accept boolean list input. *)
Definition layered_compose (f : list bool -> list bool) (g : list bool -> bool)
  : list bool -> bool
  := fun xs => g (f xs).

(** Multi-layer composition for natural output. *)
Definition layered_compose_nat (f : list bool -> list bool) (g : list bool -> nat)
  : list bool -> nat
  := fun xs => g (f xs).

(** * Conditional Composition *)

(** If condition holds, use f, otherwise use g. *)
Definition conditional_compose (cond f g : list bool -> bool)
  : list bool -> bool
  := fun xs => if cond xs then f xs else g xs.

(** Conditional for natural-valued circuits. *)
Definition conditional_compose_nat (cond : list bool -> bool) (f g : list bool -> nat)
  : list bool -> nat
  := fun xs => if cond xs then f xs else g xs.

(** * Combining Outputs *)

(** Combine two boolean circuits with AND. *)
Definition and_combine (f g : list bool -> bool)
  : list bool -> bool
  := fun xs => andb (f xs) (g xs).

(** Combine two boolean circuits with OR. *)
Definition or_combine (f g : list bool -> bool)
  : list bool -> bool
  := fun xs => orb (f xs) (g xs).

(** Combine with XOR. *)
Definition xor_combine (f g : list bool -> bool)
  : list bool -> bool
  := fun xs => xorb (f xs) (g xs).

(** Negate circuit output. *)
Definition negate_circuit (f : list bool -> bool)
  : list bool -> bool
  := fun xs => negb (f xs).

(** * Multi-Bit Output Composition *)

(** Create multi-bit output from list of circuits.
    Each circuit produces one bit of output. *)
Definition multi_bit_output (fs : list (list bool -> bool))
  : list bool -> list bool
  := parallel_compose fs.

(** Convert natural output to boolean (true if non-zero). *)
Definition nat_to_bool_circuit (f : list bool -> nat)
  : list bool -> bool
  := fun xs => negb (Nat.eqb (f xs) 0).

(** * Composition Properties *)

Lemma compose_seq_bool_correct (f : list bool -> bool) (g : bool -> bool) (xs : list bool)
  : compose_seq_bool f g xs = g (f xs).
Proof.
  reflexivity.
Qed.

Lemma parallel_compose_length (fs : list (list bool -> bool)) (xs : list bool)
  : length (parallel_compose fs xs) = length fs.
Proof.
  unfold parallel_compose.
  apply map_length.
Qed.

Lemma and_combine_comm (f g : list bool -> bool)
  : forall xs, and_combine f g xs = and_combine g f xs.
Proof.
  intro xs.
  unfold and_combine.
  apply andb_comm.
Qed.

Lemma or_combine_comm (f g : list bool -> bool)
  : forall xs, or_combine f g xs = or_combine g f xs.
Proof.
  intro xs.
  unfold or_combine.
  apply orb_comm.
Qed.

Lemma xor_combine_comm (f g : list bool -> bool)
  : forall xs, xor_combine f g xs = xor_combine g f xs.
Proof.
  intro xs.
  unfold xor_combine.
  apply xorb_comm.
Qed.

Lemma negate_involutive (f : list bool -> bool)
  : forall xs, negate_circuit (negate_circuit f) xs = f xs.
Proof.
  intro xs.
  unfold negate_circuit.
  apply negb_involutive.
Qed.

(** * Composition Verification *)

(** If f and g are equivalent, their sequential compositions are equivalent. *)
Theorem compose_seq_preserves_equiv (f1 f2 : list bool -> bool) (g : bool -> bool)
  : (forall xs, f1 xs = f2 xs) ->
    forall xs, compose_seq_bool f1 g xs = compose_seq_bool f2 g xs.
Proof.
  intros Heq xs.
  unfold compose_seq_bool.
  rewrite Heq.
  reflexivity.
Qed.

(** Parallel composition preserves equivalence pointwise. *)
Theorem parallel_preserves_equiv (fs gs : list (list bool -> bool))
  : length fs = length gs ->
    (forall i, (i < length fs)%nat -> forall xs, nth i fs (fun _ => false) xs = nth i gs (fun _ => false) xs) ->
    forall xs, parallel_compose fs xs = parallel_compose gs xs.
Proof.
  intros Hlen Heq xs.
  unfold parallel_compose.
  generalize dependent gs.
  induction fs; intros gs Hlen Heq.
  - destruct gs; try discriminate. reflexivity.
  - destruct gs; try discriminate.
    simpl.
    f_equal.
    + apply (Heq 0%nat). simpl. lia.
    + apply IHfs.
      * simpl in Hlen. lia.
      * intros i Hi.
        specialize (Heq (S i)).
        simpl in Heq.
        apply Heq.
        simpl. lia.
Qed.

(** AND combination is associative. *)
Lemma and_combine_assoc (f g h : list bool -> bool)
  : forall xs, and_combine f (and_combine g h) xs = and_combine (and_combine f g) h xs.
Proof.
  intro xs.
  unfold and_combine.
  apply andb_assoc.
Qed.

(** OR combination is associative. *)
Lemma or_combine_assoc (f g h : list bool -> bool)
  : forall xs, or_combine f (or_combine g h) xs = or_combine (or_combine f g) h xs.
Proof.
  intro xs.
  unfold or_combine.
  apply orb_assoc.
Qed.

(** * De Morgan's Laws for Composition *)

Lemma de_morgan_and (f g : list bool -> bool)
  : forall xs, negate_circuit (and_combine f g) xs = or_combine (negate_circuit f) (negate_circuit g) xs.
Proof.
  intro xs.
  unfold negate_circuit, and_combine, or_combine.
  apply negb_andb.
Qed.

Lemma de_morgan_or (f g : list bool -> bool)
  : forall xs, negate_circuit (or_combine f g) xs = and_combine (negate_circuit f) (negate_circuit g) xs.
Proof.
  intro xs.
  unfold negate_circuit, and_combine, or_combine.
  apply negb_orb.
Qed.

(** * Identity and Absorption Laws *)

(** AND with constant true is identity. *)
Lemma and_true_identity (f : list bool -> bool)
  : forall xs, and_combine f (fun _ => true) xs = f xs.
Proof.
  intro xs.
  unfold and_combine.
  apply andb_true_r.
Qed.

(** OR with constant false is identity. *)
Lemma or_false_identity (f : list bool -> bool)
  : forall xs, or_combine f (fun _ => false) xs = f xs.
Proof.
  intro xs.
  unfold or_combine.
  apply orb_false_r.
Qed.

(** AND with constant false is absorption. *)
Lemma and_false_absorb (f : list bool -> bool)
  : forall xs, and_combine f (fun _ => false) xs = false.
Proof.
  intro xs.
  unfold and_combine.
  apply andb_false_r.
Qed.

(** OR with constant true is absorption. *)
Lemma or_true_absorb (f : list bool -> bool)
  : forall xs, or_combine f (fun _ => true) xs = true.
Proof.
  intro xs.
  unfold or_combine.
  apply orb_true_r.
Qed.
