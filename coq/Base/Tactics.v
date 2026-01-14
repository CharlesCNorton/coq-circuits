(** * Base.Tactics: Standard Proof Tactics

    Reusable tactics for threshold circuit proofs.
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Lia.
Require Import Base.Definitions.

(** * Case Analysis Tactics *)

(** Destruct an 8-bit boolean list into individual variables. *)
Ltac destruct_8bit xs :=
  destruct xs as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|x6 [|x7 [|]]]]]]]]].

(** Destruct all 8 boolean variables. *)
Ltac destruct_all_8 :=
  repeat match goal with
  | x : bool |- _ => destruct x
  end.

(** Solve by exhaustive case analysis on 8 bits. *)
Ltac solve_exhaustive_8 :=
  intros;
  destruct_all_8;
  vm_compute;
  reflexivity.

(** * Verification Tactics *)

(** Prove equality by computation. *)
Ltac prove_by_compute :=
  vm_compute; reflexivity.

(** Prove all verification goals by computation. *)
Ltac verify_by_compute :=
  prove_by_compute.

(** * Arithmetic Tactics *)

(** Simplify dot product expressions. *)
Ltac simpl_dot :=
  repeat (rewrite dot_cons_true || rewrite dot_cons_false);
  simpl.

(** Simplify gate expressions. *)
Ltac simpl_gate :=
  unfold gate; simpl_dot; simpl.

(** * List Manipulation Tactics *)

(** Simplify list length computations. *)
Ltac simpl_length :=
  repeat (rewrite app_length || rewrite map_length); simpl.

(** * Common Proof Patterns *)

(** Prove lemma by case analysis and reflexivity. *)
Ltac cases_reflexivity :=
  intros; destruct_all_8; reflexivity.

(** Prove lemma by case analysis and lia. *)
Ltac cases_lia :=
  intros; destruct_all_8; simpl; lia.

(** * Modular Arithmetic Tactics *)

(** Simplify modulo expressions. *)
Ltac simpl_mod :=
  repeat (rewrite Nat.add_mod || rewrite Nat.mul_mod); try lia.

(** Unfold modulo definitions. *)
Ltac unfold_mod :=
  unfold Nat.modulo; simpl.

(** * Debugging Tactics *)

(** Show current goal with context. *)
Ltac show_goal :=
  match goal with
  | |- ?G => idtac "Goal:" G
  end.

(** Show all hypotheses. *)
Ltac show_hyps :=
  match goal with
  | H : _ |- _ => idtac "Hypothesis:" H
  end.
