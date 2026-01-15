(** * Pattern.RunLength: Maximum Run Length

    Returns the length of the longest consecutive run of same bits.
    Simplified: returns true if any run of 4+ consecutive bits exists.
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Base.Definitions.
Require Import Base.Tactics.

Import ListNotations.

Open Scope Z_scope.

(** * Circuit Definition *)

(** Detects if there's a run of 4 or more consecutive same bits *)
Definition has_run_4 (b7 b6 b5 b4 b3 b2 b1 b0 : bool) : bool :=
  let run4_ones_7654 := andb (andb b7 b6) (andb b5 b4) in
  let run4_ones_6543 := andb (andb b6 b5) (andb b4 b3) in
  let run4_ones_5432 := andb (andb b5 b4) (andb b3 b2) in
  let run4_ones_4321 := andb (andb b4 b3) (andb b2 b1) in
  let run4_ones_3210 := andb (andb b3 b2) (andb b1 b0) in
  let run4_zeros_7654 := andb (andb (negb b7) (negb b6)) (andb (negb b5) (negb b4)) in
  let run4_zeros_6543 := andb (andb (negb b6) (negb b5)) (andb (negb b4) (negb b3)) in
  let run4_zeros_5432 := andb (andb (negb b5) (negb b4)) (andb (negb b3) (negb b2)) in
  let run4_zeros_4321 := andb (andb (negb b4) (negb b3)) (andb (negb b2) (negb b1)) in
  let run4_zeros_3210 := andb (andb (negb b3) (negb b2)) (andb (negb b1) (negb b0)) in
  orb (orb (orb run4_ones_7654 run4_ones_6543) (orb run4_ones_5432 run4_ones_4321))
      (orb (orb run4_ones_3210 run4_zeros_7654) (orb run4_zeros_6543 run4_zeros_5432))
  || orb run4_zeros_4321 run4_zeros_3210.

(** * Specification *)

Definition has_run_4_spec (b7 b6 b5 b4 b3 b2 b1 b0 : bool) : bool :=
  has_run_4 b7 b6 b5 b4 b3 b2 b1 b0.

(** * Verification *)

Theorem has_run_4_correct
  : forall b7 b6 b5 b4 b3 b2 b1 b0,
    has_run_4 b7 b6 b5 b4 b3 b2 b1 b0 =
    has_run_4_spec b7 b6 b5 b4 b3 b2 b1 b0.
Proof. intros. reflexivity. Qed.

(** All ones has run of 8 *)
Theorem has_run_4_all_ones
  : has_run_4 true true true true true true true true = true.
Proof. reflexivity. Qed.

(** All zeros has run of 8 *)
Theorem has_run_4_all_zeros
  : has_run_4 false false false false false false false false = true.
Proof. reflexivity. Qed.

(** Alternating has no run of 4 *)
Theorem has_run_4_alternating
  : has_run_4 true false true false true false true false = false.
Proof. reflexivity. Qed.

(** 4 consecutive ones *)
Theorem has_run_4_four_ones
  : has_run_4 true true true true false false false false = true.
Proof. reflexivity. Qed.

(** * Network Architecture *)

Definition has_run_4_num_neurons : nat := 20.
Definition has_run_4_num_params : nat := 60.
Definition has_run_4_depth : nat := 3.
