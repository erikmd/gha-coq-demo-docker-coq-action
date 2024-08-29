From Coq Require Import ssreflect.
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition primes_upto n :=
  filter prime (iota 1 n).

Lemma primes_le n : forall p, p \in primes_upto n -> p <= n.
Proof.
  move=> p; rewrite /primes_upto mem_filter.
  by case/andP=> /prime_gt0; rewrite mem_iota =>->.
Qed.
