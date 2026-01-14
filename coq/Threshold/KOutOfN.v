(** * Threshold.KOutOfN: General K-out-of-N Threshold

    Fully parametric k-out-of-n threshold function.
    Fires when at least k of n inputs are true.
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Lia.
Require Import Base.Definitions.
Require Import Base.Tactics.

Import ListNotations.

Open Scope Z_scope.

(** * Circuit Definition *)

(** K-out-of-N circuit with parametric weights and bias. *)
Definition k_out_of_n_circuit (n k : nat) (xs : list bool)
  : bool
  :=
  let weights := ones n in
  let bias := - (Z.of_nat k) in
  gate weights bias xs.

(** * Specification *)

Definition k_out_of_n_spec (k : nat) (xs : list bool)
  : bool
  := Nat.leb k (hamming_weight xs).

(** * Properties *)

(** K-out-of-N for 8 inputs, k=5 is majority. *)
Lemma k_out_of_8_is_5_out_of_8
  : forall xs,
    length xs = 8%nat ->
    k_out_of_n_circuit 8 5 xs = k_out_of_n_spec 5 xs.
Proof.
  intros xs Hlen.
  unfold k_out_of_n_circuit, k_out_of_n_spec, gate.
  destruct xs as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|x6 [|x7 [|]]]]]]]]]; try discriminate.
  clear Hlen.
  destruct x0, x1, x2, x3, x4, x5, x6, x7; vm_compute; reflexivity.
Qed.

(** K-out-of-N weights have correct length. *)
Lemma k_out_of_n_weights_length (n : nat)
  : length (ones n) = n.
Proof.
  apply ones_length.
Qed.

(** * Network Architecture *)

Definition k_out_of_n_num_params (n : nat) : nat := S n.
Definition k_out_of_n_num_neurons : nat := 1.
Definition k_out_of_n_depth : nat := 1.
