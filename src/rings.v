Require Import SetoidClass.
Require groups.

Module Make(Import M: groups.T).

Class ring (F: Set) (s: Setoid F) (op1 op2: F -> F -> F) (zero one: F) (inv1: F -> F)
                     (g1: @group F s op1 zero inv1) :=
{
  r_assoc     : forall {a b c}, op2 (op2 a b) c == op2 a (op2 b c);
  r_identity  : forall {a}, op2 one a == a;
  r_inverser  : forall a: F, op1 (inv1 a) a == zero;
  r_idsdiffer : ~ one == zero;
  r_comm      : forall {a b}, op1 a b == op1 b a;
  r_distrib   : forall {a b c}, (op2 a (op1 b c)) == op1 (op2 a b) (op2 a c)
}.
Check ring.

Require Import Psatz.
Require Import Nsatz.
Require Import ZArith.
Open Scope Z_scope.

Definition zmult (n m: Z):= n * m.
Definition zid2 := 1%Z.

Program Instance Zeq_setoid : Setoid Z :=
  { equiv := eq ; setoid_equiv := eq_equivalence }.

(** < Z, +, 0, ^{-1+} > as a group instance **)
Program Instance ring_integers: (@ring Z (Zeq_setoid) _ zmult _ zid2 _ group_integers).
Obligation 1. unfold zmult. rewrite Zmult_assoc. reflexivity. Qed.
Next Obligation. destruct a; reflexivity. Qed.
Next Obligation. unfold zadd, zinv, zid. omega. Qed.
Next Obligation. unfold zadd. omega. Qed.
Next Obligation. unfold zadd, zmult. apply Zmult_plus_distr_r. Qed.
Check ring_integers.

(* TODO:= proving Coq rationals and reels aZmult_1_ls ring instances *)

End Make.