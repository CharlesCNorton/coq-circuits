(** * Error.SanityTest10: EvenParity = NOT(OddParity)

    Sanity Test 10: Verify even and odd parity are complements.

    This demonstrates:
    1. Even parity = even number of 1s
    2. Odd parity = odd number of 1s
    3. These are logical complements
*)

Require Import ZArith.
Require Import List.
Require Import Bool.
Require Import Base.Definitions.
Require Import Base.Tactics.
Require Import Base.Verification.
Require Import Error.ParityChecker8Bit.

Import ListNotations.

Open Scope Z_scope.

(** * Sanity Test 10: EvenParity = NOT(OddParity) *)

(** Parity complement already proven in ParityChecker8Bit *)
Theorem sanity_test_10_complement
  : forall x0 x1 x2 x3 x4 x5 x6 x7,
    odd_parity_circuit [x0; x1; x2; x3; x4; x5; x6; x7] =
    negb (even_parity_circuit [x0; x1; x2; x3; x4; x5; x6; x7]).
Proof.
  apply parity_complement.
Qed.

(** Equivalently: EvenParity = NOT(OddParity) *)
Theorem sanity_test_10_even_is_not_odd
  : forall x0 x1 x2 x3 x4 x5 x6 x7,
    even_parity_circuit [x0; x1; x2; x3; x4; x5; x6; x7] =
    negb (odd_parity_circuit [x0; x1; x2; x3; x4; x5; x6; x7]).
Proof.
  intros.
  rewrite parity_complement.
  rewrite negb_involutive.
  reflexivity.
Qed.

(** Exhaustive verification *)
Theorem sanity_test_10_exhaustive
  : verify_all (fun xs =>
      Bool.eqb (even_parity_circuit xs)
               (negb (odd_parity_circuit xs))) = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

(** Zero bits: even parity, not odd *)
Theorem sanity_test_10_zero_bits
  : even_parity_circuit [false; false; false; false; false; false; false; false] = true /\
    odd_parity_circuit [false; false; false; false; false; false; false; false] = false.
Proof.
  split; vm_compute; reflexivity.
Qed.

(** One bit: odd parity, not even *)
Theorem sanity_test_10_one_bit
  : even_parity_circuit [true; false; false; false; false; false; false; false] = false /\
    odd_parity_circuit [true; false; false; false; false; false; false; false] = true.
Proof.
  split; vm_compute; reflexivity.
Qed.

(** Two bits: even parity, not odd *)
Theorem sanity_test_10_two_bits
  : even_parity_circuit [true; true; false; false; false; false; false; false] = true /\
    odd_parity_circuit [true; true; false; false; false; false; false; false] = false.
Proof.
  split; vm_compute; reflexivity.
Qed.

(** All bits: even parity (8 is even), not odd *)
Theorem sanity_test_10_all_bits
  : even_parity_circuit [true; true; true; true; true; true; true; true] = true /\
    odd_parity_circuit [true; true; true; true; true; true; true; true] = false.
Proof.
  split; vm_compute; reflexivity.
Qed.

(** SANITY TEST 10 PASSES: EvenParity = NOT(OddParity) *)
Theorem sanity_test_10_complete
  : forall x0 x1 x2 x3 x4 x5 x6 x7,
    (even_parity_circuit [x0; x1; x2; x3; x4; x5; x6; x7] =
     negb (odd_parity_circuit [x0; x1; x2; x3; x4; x5; x6; x7])) /\
    (odd_parity_circuit [x0; x1; x2; x3; x4; x5; x6; x7] =
     negb (even_parity_circuit [x0; x1; x2; x3; x4; x5; x6; x7])).
Proof.
  intros.
  split.
  - apply sanity_test_10_even_is_not_odd.
  - apply sanity_test_10_complement.
Qed.
