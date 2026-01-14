(** * Base.Verification: Verification Framework

    Standard verification patterns for all threshold circuits.
    Provides exhaustive input generation and verification utilities.
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Lia.
Require Import Base.Definitions.
Require Import Base.Tactics.

Import ListNotations.

Open Scope Z_scope.

(** * Input Generation *)

(** Generate all possible n-bit boolean inputs.
    Returns list of 2^n inputs in binary order. *)
Fixpoint all_inputs (n : nat)
  : list (list bool)
  :=
  match n with
  | O => [[]]
  | S n' =>
    let prev := all_inputs n' in
    map (cons false) prev ++ map (cons true) prev
  end.

(** Standard 8-bit input enumeration. *)
Definition all_inputs_8
  : list (list bool)
  := all_inputs 8.

(** * Verification Predicates *)

(** Generic verification: check predicate on all n-bit inputs. *)
Definition verify_all_n (n : nat) (pred : list bool -> bool)
  : bool
  := forallb pred (all_inputs n).

(** Standard 8-bit verification. *)
Definition verify_all (pred : list bool -> bool)
  : bool
  := verify_all_n 8 pred.

(** Verify two circuits produce identical outputs. *)
Definition verify_equiv (f g : list bool -> bool)
  : bool
  := verify_all (fun xs => Bool.eqb (f xs) (g xs)).

(** Verify two natural-valued circuits produce identical outputs. *)
Definition verify_equiv_nat (f g : list bool -> nat)
  : bool
  := verify_all (fun xs => Nat.eqb (f xs) (g xs)).

(** * Distribution Analysis *)

(** Count inputs satisfying a predicate. *)
Definition count_satisfying (n : nat) (pred : list bool -> bool)
  : nat
  := length (filter pred (all_inputs n)).

(** Distribution of outputs for natural-valued function. *)
Definition output_distribution (n : nat) (f : list bool -> nat) (k : nat)
  : nat
  := count_satisfying n (fun xs => Nat.eqb (f xs) k).

(** * Properties *)

Lemma all_inputs_length (n : nat)
  : length (all_inputs n) = Nat.pow 2 n.
Proof.
  induction n.
  - reflexivity.
  - simpl.
    rewrite app_length.
    rewrite !map_length.
    rewrite IHn.
    lia.
Qed.

Lemma all_inputs_8_length
  : length all_inputs_8 = 256%nat.
Proof.
  unfold all_inputs_8.
  rewrite all_inputs_length.
  reflexivity.
Qed.

Lemma all_inputs_complete (n : nat) (xs : list bool)
  : length xs = n ->
    In xs (all_inputs n).
Proof.
  revert xs.
  induction n; intros xs Hlen.
  - destruct xs; try discriminate.
    simpl.
    left.
    reflexivity.
  - destruct xs; try discriminate.
    simpl in Hlen.
    injection Hlen as Hlen.
    simpl.
    apply in_app_iff.
    destruct b.
    + right.
      apply in_map_iff.
      exists xs.
      split; try reflexivity.
      apply IHn.
      assumption.
    + left.
      apply in_map_iff.
      exists xs.
      split; try reflexivity.
      apply IHn.
      assumption.
Qed.

(** * Verification Theorems *)

Lemma all_inputs_8_all_length_8
  : forall xs, In xs (all_inputs 8) -> length xs = 8%nat.
Proof.
  intros xs Hin.
  apply in_split in Hin.
  destruct Hin as [l1 [l2 Heq]].
  assert (Hlen: length (all_inputs 8) = 256%nat) by apply all_inputs_8_length.
  rewrite Heq in Hlen.
  rewrite !app_length in Hlen.
  simpl in Hlen.
  assert (Hall: forall ys, In ys (all_inputs 8) -> length ys = 8%nat).
  { clear Heq Hlen xs l1 l2.
    intro ys.
    unfold all_inputs_8.
    generalize 8%nat as n.
    intro n.
    revert ys.
    induction n; intros ys Hiny.
    - simpl in Hiny.
      destruct Hiny as [Heq|Hf]; try contradiction.
      subst. reflexivity.
    - simpl in Hiny.
      apply in_app_or in Hiny.
      destruct Hiny as [Hinf|Hint].
      + apply in_map_iff in Hinf.
        destruct Hinf as [ys' [Heq Hin']].
        subst. simpl.
        rewrite (IHn ys'); try assumption; reflexivity.
      + apply in_map_iff in Hint.
        destruct Hint as [ys' [Heq Hin']].
        subst. simpl.
        rewrite (IHn ys'); try assumption; reflexivity. }
  unfold all_inputs_8 in *.
  rewrite Heq in Hall.
  apply Hall.
  apply in_app_iff. right. simpl. left. reflexivity.
Qed.

Theorem verify_all_correct (pred : list bool -> bool)
  : verify_all pred = true <->
    forall x0 x1 x2 x3 x4 x5 x6 x7,
      pred [x0; x1; x2; x3; x4; x5; x6; x7] = true.
Proof.
  split; intro H.
  - intros.
    unfold verify_all, verify_all_n in H.
    rewrite forallb_forall in H.
    apply H.
    apply all_inputs_complete.
    reflexivity.
  - unfold verify_all, verify_all_n.
    rewrite forallb_forall.
    intros xs Hin.
    unfold all_inputs_8 in Hin.
    assert (Hlen : length xs = 8%nat) by (apply all_inputs_8_all_length_8; assumption).
    destruct xs as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|x6 [|x7 [|]]]]]]]]];
    try discriminate.
    apply H.
Qed.

Theorem verify_equiv_correct (f g : list bool -> bool)
  : verify_equiv f g = true <->
    forall x0 x1 x2 x3 x4 x5 x6 x7,
      f [x0; x1; x2; x3; x4; x5; x6; x7] = g [x0; x1; x2; x3; x4; x5; x6; x7].
Proof.
  unfold verify_equiv.
  rewrite verify_all_correct.
  split; intro H; intros.
  - specialize (H x0 x1 x2 x3 x4 x5 x6 x7).
    apply Bool.eqb_prop in H.
    assumption.
  - rewrite Bool.eqb_true_iff.
    apply H.
Qed.

(** * Helper Functions for Testing *)

(** Check if input has specific Hamming weight. *)
Definition has_hamming_weight (k : nat) (xs : list bool)
  : bool
  := Nat.eqb (hamming_weight xs) k.

(** Check if input is all zeros. *)
Definition is_all_zeros (xs : list bool)
  : bool
  := forallb (fun b => negb b) xs.

(** Check if input is all ones. *)
Definition is_all_ones (xs : list bool)
  : bool
  := forallb (fun b => b) xs.

(** Count inputs with specific Hamming weight. *)
Definition hamming_weight_distribution (n k : nat)
  : nat
  := count_satisfying n (has_hamming_weight k).
