From Coq Require Import ssreflect.
From mathcomp Require Import all_ssreflect.
From Demo Require Import demo.

Eval vm_compute in primes_upto 100.

Check primes_le.
Print Assumptions primes_le.
