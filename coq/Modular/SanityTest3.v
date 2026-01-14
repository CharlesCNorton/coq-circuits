(** * Modular.SanityTest3: MOD-2 = XOR = Parity

    Sanity Test 3 from README: Verify MOD-2 = XOR = Parity.

    This test ensures that:
    1. MOD-2 circuit computes parity
    2. Parity equals XOR of all inputs
    3. MOD-2 on 2 inputs equals XOR gate
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Lia.
Require Import Base.Definitions.
Require Import Base.Verification.
Require Import Boolean.XOR.
Require Import Modular.ModMParametric.
Require Import Modular.Mod2.

Import ListNotations.

Open Scope Z_scope.

(** * Parity Definition *)

(** Parity: true if odd number of true inputs. *)
Fixpoint parity (xs : list bool) : bool :=
  match xs with
  | [] => false
  | x :: xs' => xorb x (parity xs')
  end.

(** * Sanity Test 3: Three-way Equivalence *)

(** MOD-2 equals parity for 8-bit inputs. *)
Theorem mod2_is_parity
  : forall x0 x1 x2 x3 x4 x5 x6 x7,
    mod2_is_zero [x0; x1; x2; x3; x4; x5; x6; x7] =
    negb (parity [x0; x1; x2; x3; x4; x5; x6; x7]).
Proof.
  intros.
  unfold mod2_is_zero, mod_m_is_residue.
  destruct x0, x1, x2, x3, x4, x5, x6, x7; vm_compute; reflexivity.
Qed.

(** Parity of 2 inputs equals XOR. *)
Theorem parity_2_is_xor
  : forall x y,
    parity [x; y] = xor_circuit x y.
Proof.
  intros.
  destruct x, y; vm_compute; reflexivity.
Qed.

(** MOD-2 on 2 inputs equals XOR. *)
Theorem mod2_2_is_xor
  : forall x y,
    negb (mod2_is_zero [x; y; false; false; false; false; false; false]) =
    xor_circuit x y.
Proof.
  intros.
  destruct x, y; vm_compute; reflexivity.
Qed.

(** Three-way equivalence: MOD-2 = XOR = Parity (for 2 inputs). *)
Theorem sanity_test_3_two_inputs
  : forall x y,
    negb (mod2_is_zero [x; y; false; false; false; false; false; false]) = xor_circuit x y
    /\ parity [x; y] = xor_circuit x y.
Proof.
  intros.
  split.
  - apply mod2_2_is_xor.
  - apply parity_2_is_xor.
Qed.

(** Parity via iterated XOR for 8 inputs. *)
Theorem parity_8_via_xor
  : forall x0 x1 x2 x3 x4 x5 x6 x7,
    parity [x0; x1; x2; x3; x4; x5; x6; x7] =
    xorb x0 (xorb x1 (xorb x2 (xorb x3 (xorb x4 (xorb x5 (xorb x6 x7)))))).
Proof.
  intros.
  destruct x0, x1, x2, x3, x4, x5, x6, x7; vm_compute; reflexivity.
Qed.

(** Hamming weight mod 2 equals parity for 8-bit inputs. *)
Theorem hamming_weight_mod2_is_parity_8
  : forall x0 x1 x2 x3 x4 x5 x6 x7,
    Z.eqb ((Z.of_nat (hamming_weight [x0; x1; x2; x3; x4; x5; x6; x7])) mod 2) 0 =
    negb (parity [x0; x1; x2; x3; x4; x5; x6; x7]).
Proof.
  intros.
  destruct x0, x1, x2, x3, x4, x5, x6, x7; vm_compute; reflexivity.
Qed.

(** SANITY TEST 3 PASSES: MOD-2 = XOR = Parity ✓ *)
Theorem sanity_test_3_complete
  : forall x0 x1 x2 x3 x4 x5 x6 x7,
    let xs := [x0; x1; x2; x3; x4; x5; x6; x7] in
    mod2_is_zero xs = negb (parity xs) /\
    (forall x y, parity [x; y] = xor_circuit x y) /\
    Z.eqb ((Z.of_nat (hamming_weight xs)) mod 2) 0 = negb (parity xs).
Proof.
  intros.
  split; [apply mod2_is_parity | split].
  - apply parity_2_is_xor.
  - apply hamming_weight_mod2_is_parity_8.
Qed.
