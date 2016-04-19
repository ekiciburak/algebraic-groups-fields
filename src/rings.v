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

(** < Z, +, *, 0, 1, ^{-1+} > as a ring instance **)
Program Instance ring_integers: (@ring Z (Zeq_setoid) _ zmult _ zid2 _ group_integers).
Obligation 1. unfold zmult. rewrite Zmult_assoc. reflexivity. Qed.
Next Obligation. destruct a; reflexivity. Qed.
Next Obligation. unfold zadd, zinv, zid. omega. Qed.
Next Obligation. unfold zadd. omega. Qed.
Next Obligation. unfold zadd, zmult. apply Zmult_plus_distr_r. Qed.
Check ring_integers.

Require Import Psatz.
Require Import Nsatz.
Require Import QArith.
Open Scope Q_scope.

Definition qmult (n m: Q) := n * m.
Definition qid2 := 1.

(** < Q, +, *, 0, 1, ^{-1+} > as a ring instance **)
Program Instance ring_rationals: `(@ring Q (Qeq_setoid) _ qmult _ qid2 _ group_rationals).
Obligation 1. unfold qmult. symmetry. apply Qmult_assoc. Qed. 
Next Obligation. unfold qmult, qid2. apply Qmult_1_l. Qed.
Next Obligation. unfold qadd, qinv, qid. rewrite Qplus_comm, Qplus_opp_r. reflexivity. Qed. 
Next Obligation. unfold qadd. apply Qplus_comm. Qed.
Next Obligation. unfold qadd, qmult. apply Qmult_plus_distr_r. Qed.
Check ring_rationals.

Require Import ZArith_base.
Require Import Rdefinitions.
Require Import Coq.Reals.Raxioms.
Local Open Scope R_scope.

Definition rmult (n m: R) := n * m.
Definition rid2 := 1.

(** < R, +, *, 0, 1, ^{-1+} > as a ring instance **)
Program Instance ring_reals: `(@ring R _ _ rmult _ rid2 _ group_reals).
Obligation 1. unfold rmult. apply Rmult_assoc. Qed.
Next Obligation. unfold rmult, rid2. apply Rmult_1_l. Qed.
Next Obligation. unfold radd, rinv, rid. rewrite Rplus_comm, Rplus_opp_r. reflexivity. Qed. 
Next Obligation. unfold rid, rid2. apply R1_neq_R0. Qed.
Next Obligation. unfold radd. apply Rplus_comm. Qed.
Next Obligation. unfold radd, rmult. apply  Rmult_plus_distr_l. Qed.
Check ring_reals.

End Make.