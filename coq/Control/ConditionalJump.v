(** * Control.ConditionalJump: Conditional Jump Circuits

    Computes next program counter for conditional jumps.
    JZ, JNZ, JC, JNC, JN, JP: PC_next = if condition then target else pc_plus_2

    Implemented using 8-bit MUX controlled by flag evaluation.
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Base.Definitions.
Require Import Combinational.Multiplexer2to1.
Require Import Boolean.NOT.

Import ListNotations.

Open Scope Z_scope.

(** * Circuit Definitions *)

(** 8-bit conditional MUX: selects target or pc_plus_2 based on condition.
    condition=true → target, condition=false → pc_plus_2 *)
Definition cond_mux_8bit (condition : bool) (target pc_plus_2 : list bool) : list bool :=
  match target, pc_plus_2 with
  | [t7;t6;t5;t4;t3;t2;t1;t0], [p7;p6;p5;p4;p3;p2;p1;p0] =>
      [mux2to1 condition p7 t7;
       mux2to1 condition p6 t6;
       mux2to1 condition p5 t5;
       mux2to1 condition p4 t4;
       mux2to1 condition p3 t3;
       mux2to1 condition p2 t2;
       mux2to1 condition p1 t1;
       mux2to1 condition p0 t0]
  | _, _ => pc_plus_2
  end.

(** JZ: Jump if Zero flag is set *)
Definition jz_circuit (z_flag : bool) (target pc_plus_2 : list bool) : list bool :=
  cond_mux_8bit z_flag target pc_plus_2.

(** JNZ: Jump if Zero flag is NOT set *)
Definition jnz_circuit (z_flag : bool) (target pc_plus_2 : list bool) : list bool :=
  cond_mux_8bit (not_circuit z_flag) target pc_plus_2.

(** JC: Jump if Carry flag is set *)
Definition jc_circuit (c_flag : bool) (target pc_plus_2 : list bool) : list bool :=
  cond_mux_8bit c_flag target pc_plus_2.

(** JNC: Jump if Carry flag is NOT set *)
Definition jnc_circuit (c_flag : bool) (target pc_plus_2 : list bool) : list bool :=
  cond_mux_8bit (not_circuit c_flag) target pc_plus_2.

(** JN: Jump if Negative flag is set *)
Definition jn_circuit (n_flag : bool) (target pc_plus_2 : list bool) : list bool :=
  cond_mux_8bit n_flag target pc_plus_2.

(** JP: Jump if Positive (Negative flag NOT set) *)
Definition jp_circuit (n_flag : bool) (target pc_plus_2 : list bool) : list bool :=
  cond_mux_8bit (not_circuit n_flag) target pc_plus_2.

(** JV: Jump if Overflow flag is set *)
Definition jv_circuit (v_flag : bool) (target pc_plus_2 : list bool) : list bool :=
  cond_mux_8bit v_flag target pc_plus_2.

(** JNV: Jump if Overflow flag is NOT set *)
Definition jnv_circuit (v_flag : bool) (target pc_plus_2 : list bool) : list bool :=
  cond_mux_8bit (not_circuit v_flag) target pc_plus_2.

(** * Specifications *)

Definition cond_jump_spec (condition : bool) (target pc_plus_2 : list bool) : list bool :=
  if condition then target else pc_plus_2.

Definition jz_spec (z_flag : bool) (target pc_plus_2 : list bool) : list bool :=
  cond_jump_spec z_flag target pc_plus_2.

Definition jnz_spec (z_flag : bool) (target pc_plus_2 : list bool) : list bool :=
  cond_jump_spec (negb z_flag) target pc_plus_2.

Definition jc_spec (c_flag : bool) (target pc_plus_2 : list bool) : list bool :=
  cond_jump_spec c_flag target pc_plus_2.

Definition jnc_spec (c_flag : bool) (target pc_plus_2 : list bool) : list bool :=
  cond_jump_spec (negb c_flag) target pc_plus_2.

Definition jn_spec (n_flag : bool) (target pc_plus_2 : list bool) : list bool :=
  cond_jump_spec n_flag target pc_plus_2.

Definition jp_spec (n_flag : bool) (target pc_plus_2 : list bool) : list bool :=
  cond_jump_spec (negb n_flag) target pc_plus_2.

(** * Verification *)

Lemma cond_mux_8bit_true : forall t7 t6 t5 t4 t3 t2 t1 t0 p7 p6 p5 p4 p3 p2 p1 p0,
  cond_mux_8bit true [t7;t6;t5;t4;t3;t2;t1;t0] [p7;p6;p5;p4;p3;p2;p1;p0] =
  [t7;t6;t5;t4;t3;t2;t1;t0].
Proof.
  intros.
  unfold cond_mux_8bit.
  repeat rewrite mux2to1_select_b.
  reflexivity.
Qed.

Lemma cond_mux_8bit_false : forall t7 t6 t5 t4 t3 t2 t1 t0 p7 p6 p5 p4 p3 p2 p1 p0,
  cond_mux_8bit false [t7;t6;t5;t4;t3;t2;t1;t0] [p7;p6;p5;p4;p3;p2;p1;p0] =
  [p7;p6;p5;p4;p3;p2;p1;p0].
Proof.
  intros.
  unfold cond_mux_8bit.
  repeat rewrite mux2to1_select_a.
  reflexivity.
Qed.

Theorem jz_correct : forall z_flag t7 t6 t5 t4 t3 t2 t1 t0 p7 p6 p5 p4 p3 p2 p1 p0,
  jz_circuit z_flag [t7;t6;t5;t4;t3;t2;t1;t0] [p7;p6;p5;p4;p3;p2;p1;p0] =
  jz_spec z_flag [t7;t6;t5;t4;t3;t2;t1;t0] [p7;p6;p5;p4;p3;p2;p1;p0].
Proof.
  intros.
  unfold jz_circuit, jz_spec, cond_jump_spec.
  destruct z_flag.
  - apply cond_mux_8bit_true.
  - apply cond_mux_8bit_false.
Qed.

Theorem jnz_correct : forall z_flag t7 t6 t5 t4 t3 t2 t1 t0 p7 p6 p5 p4 p3 p2 p1 p0,
  jnz_circuit z_flag [t7;t6;t5;t4;t3;t2;t1;t0] [p7;p6;p5;p4;p3;p2;p1;p0] =
  jnz_spec z_flag [t7;t6;t5;t4;t3;t2;t1;t0] [p7;p6;p5;p4;p3;p2;p1;p0].
Proof.
  intros.
  unfold jnz_circuit, jnz_spec, cond_jump_spec.
  rewrite not_correct.
  destruct z_flag; simpl.
  - apply cond_mux_8bit_false.
  - apply cond_mux_8bit_true.
Qed.

Theorem jc_correct : forall c_flag t7 t6 t5 t4 t3 t2 t1 t0 p7 p6 p5 p4 p3 p2 p1 p0,
  jc_circuit c_flag [t7;t6;t5;t4;t3;t2;t1;t0] [p7;p6;p5;p4;p3;p2;p1;p0] =
  jc_spec c_flag [t7;t6;t5;t4;t3;t2;t1;t0] [p7;p6;p5;p4;p3;p2;p1;p0].
Proof.
  intros.
  unfold jc_circuit, jc_spec, cond_jump_spec.
  destruct c_flag.
  - apply cond_mux_8bit_true.
  - apply cond_mux_8bit_false.
Qed.

Theorem jnc_correct : forall c_flag t7 t6 t5 t4 t3 t2 t1 t0 p7 p6 p5 p4 p3 p2 p1 p0,
  jnc_circuit c_flag [t7;t6;t5;t4;t3;t2;t1;t0] [p7;p6;p5;p4;p3;p2;p1;p0] =
  jnc_spec c_flag [t7;t6;t5;t4;t3;t2;t1;t0] [p7;p6;p5;p4;p3;p2;p1;p0].
Proof.
  intros.
  unfold jnc_circuit, jnc_spec, cond_jump_spec.
  rewrite not_correct.
  destruct c_flag; simpl.
  - apply cond_mux_8bit_false.
  - apply cond_mux_8bit_true.
Qed.

Theorem jn_correct : forall n_flag t7 t6 t5 t4 t3 t2 t1 t0 p7 p6 p5 p4 p3 p2 p1 p0,
  jn_circuit n_flag [t7;t6;t5;t4;t3;t2;t1;t0] [p7;p6;p5;p4;p3;p2;p1;p0] =
  jn_spec n_flag [t7;t6;t5;t4;t3;t2;t1;t0] [p7;p6;p5;p4;p3;p2;p1;p0].
Proof.
  intros.
  unfold jn_circuit, jn_spec, cond_jump_spec.
  destruct n_flag.
  - apply cond_mux_8bit_true.
  - apply cond_mux_8bit_false.
Qed.

Theorem jp_correct : forall n_flag t7 t6 t5 t4 t3 t2 t1 t0 p7 p6 p5 p4 p3 p2 p1 p0,
  jp_circuit n_flag [t7;t6;t5;t4;t3;t2;t1;t0] [p7;p6;p5;p4;p3;p2;p1;p0] =
  jp_spec n_flag [t7;t6;t5;t4;t3;t2;t1;t0] [p7;p6;p5;p4;p3;p2;p1;p0].
Proof.
  intros.
  unfold jp_circuit, jp_spec, cond_jump_spec.
  rewrite not_correct.
  destruct n_flag; simpl.
  - apply cond_mux_8bit_false.
  - apply cond_mux_8bit_true.
Qed.

(** * Properties *)

(** When condition matches, we take the branch *)
Lemma cond_jump_takes_branch : forall target pc_plus_2,
  length target = 8%nat ->
  length pc_plus_2 = 8%nat ->
  cond_jump_spec true target pc_plus_2 = target.
Proof.
  intros.
  unfold cond_jump_spec.
  reflexivity.
Qed.

(** When condition doesn't match, we fall through *)
Lemma cond_jump_falls_through : forall target pc_plus_2,
  length target = 8%nat ->
  length pc_plus_2 = 8%nat ->
  cond_jump_spec false target pc_plus_2 = pc_plus_2.
Proof.
  intros.
  unfold cond_jump_spec.
  reflexivity.
Qed.

(** JZ and JNZ are complementary *)
Lemma jz_jnz_complementary : forall z_flag target pc_plus_2,
  jz_spec z_flag target pc_plus_2 = jnz_spec (negb z_flag) target pc_plus_2.
Proof.
  intros.
  unfold jz_spec, jnz_spec, cond_jump_spec.
  rewrite negb_involutive.
  reflexivity.
Qed.

(** * Network Architecture *)

(** Each conditional jump uses:
    - 1 NOT neuron (for negated conditions)
    - 8 MUX2to1 circuits (4 neurons each) = 32 neurons
    Total: 33 neurons max, depth 3 *)
Definition cond_jump_num_neurons : nat := 33.
Definition cond_jump_num_params : nat := 99.
Definition cond_jump_depth : nat := 3.

Print Assumptions jz_correct.
Print Assumptions jnz_correct.
Print Assumptions jc_correct.
Print Assumptions jnc_correct.
Print Assumptions jn_correct.
Print Assumptions jp_correct.
