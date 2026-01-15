(** * Combinational.BarrelShifter8Bit: 8-Bit Barrel Shifter

    Performs logical left shift of 8-bit input by 0-7 positions.
    Uses three stages of multiplexers for shift amounts 1, 2, 4.
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Base.Definitions.
Require Import Base.Tactics.
Require Import Combinational.Multiplexer2to1.

Import ListNotations.

Open Scope Z_scope.

(** * Circuit Definition *)

(** Stage 1: shift by 0 or 1 *)
Definition barrel_stage1 (s0 b7 b6 b5 b4 b3 b2 b1 b0 : bool)
  : bool * bool * bool * bool * bool * bool * bool * bool :=
  if s0 then (b6, b5, b4, b3, b2, b1, b0, false)
  else (b7, b6, b5, b4, b3, b2, b1, b0).

(** Stage 2: shift by 0 or 2 *)
Definition barrel_stage2 (s1 b7 b6 b5 b4 b3 b2 b1 b0 : bool)
  : bool * bool * bool * bool * bool * bool * bool * bool :=
  if s1 then (b5, b4, b3, b2, b1, b0, false, false)
  else (b7, b6, b5, b4, b3, b2, b1, b0).

(** Stage 3: shift by 0 or 4 *)
Definition barrel_stage3 (s2 b7 b6 b5 b4 b3 b2 b1 b0 : bool)
  : bool * bool * bool * bool * bool * bool * bool * bool :=
  if s2 then (b3, b2, b1, b0, false, false, false, false)
  else (b7, b6, b5, b4, b3, b2, b1, b0).

(** Full barrel shifter: compose three stages *)
Definition barrel_shifter_8bit (s2 s1 s0 b7 b6 b5 b4 b3 b2 b1 b0 : bool)
  : bool * bool * bool * bool * bool * bool * bool * bool :=
  let '(t7, t6, t5, t4, t3, t2, t1, t0) := barrel_stage1 s0 b7 b6 b5 b4 b3 b2 b1 b0 in
  let '(u7, u6, u5, u4, u3, u2, u1, u0) := barrel_stage2 s1 t7 t6 t5 t4 t3 t2 t1 t0 in
  barrel_stage3 s2 u7 u6 u5 u4 u3 u2 u1 u0.

(** * Specification *)

Definition barrel_shifter_8bit_spec (s2 s1 s0 b7 b6 b5 b4 b3 b2 b1 b0 : bool)
  : bool * bool * bool * bool * bool * bool * bool * bool :=
  let shift := (if s2 then 4 else 0) + (if s1 then 2 else 0) + (if s0 then 1 else 0) in
  match shift with
  | 0 => (b7, b6, b5, b4, b3, b2, b1, b0)
  | 1 => (b6, b5, b4, b3, b2, b1, b0, false)
  | 2 => (b5, b4, b3, b2, b1, b0, false, false)
  | 3 => (b4, b3, b2, b1, b0, false, false, false)
  | 4 => (b3, b2, b1, b0, false, false, false, false)
  | 5 => (b2, b1, b0, false, false, false, false, false)
  | 6 => (b1, b0, false, false, false, false, false, false)
  | _ => (b0, false, false, false, false, false, false, false)
  end.

(** * Verification *)

Theorem barrel_shifter_8bit_correct
  : forall s2 s1 s0 b7 b6 b5 b4 b3 b2 b1 b0,
    barrel_shifter_8bit s2 s1 s0 b7 b6 b5 b4 b3 b2 b1 b0 =
    barrel_shifter_8bit_spec s2 s1 s0 b7 b6 b5 b4 b3 b2 b1 b0.
Proof.
  intros.
  unfold barrel_shifter_8bit, barrel_shifter_8bit_spec.
  unfold barrel_stage1, barrel_stage2, barrel_stage3.
  destruct s2, s1, s0, b7, b6, b5, b4, b3, b2, b1, b0; reflexivity.
Qed.

(** Shift by 0 is identity *)
Theorem barrel_shifter_8bit_zero
  : forall b7 b6 b5 b4 b3 b2 b1 b0,
    barrel_shifter_8bit false false false b7 b6 b5 b4 b3 b2 b1 b0 =
    (b7, b6, b5, b4, b3, b2, b1, b0).
Proof.
  intros. destruct b7, b6, b5, b4, b3, b2, b1, b0; reflexivity.
Qed.

(** Shift by 7 leaves only LSB in MSB *)
Theorem barrel_shifter_8bit_seven
  : forall b7 b6 b5 b4 b3 b2 b1 b0,
    barrel_shifter_8bit true true true b7 b6 b5 b4 b3 b2 b1 b0 =
    (b0, false, false, false, false, false, false, false).
Proof.
  intros. destruct b7, b6, b5, b4, b3, b2, b1, b0; reflexivity.
Qed.

(** * Network Architecture *)

Definition barrel_shifter_8bit_num_neurons : nat := 24.
Definition barrel_shifter_8bit_num_params : nat := 72.
Definition barrel_shifter_8bit_depth : nat := 6.
