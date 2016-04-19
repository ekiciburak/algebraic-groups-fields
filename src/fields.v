Require Import SetoidClass.
Require groups rings.

Module Make(Import M: groups.T).
 Module Export fields_exp := rings.Make(M).

Class field (F: Set) (s: Setoid F) (op1 op2: F -> F -> F) (zero one: F) (inv1 inv2: F -> F)
                     (g1: @group F s op1 zero inv1) :=
{

  f_assoc     : forall {a b c}, op2 (op2 a b) c == op2 a (op2 b c);
  f_identity  : forall {a}, op2 one a == a;
  f_inverse1  : forall a: F, op1 (inv1 a) a == zero;
  f_inverse2  : forall a: F, a == zero -> op2 (inv2 a) a == one -> False;
  f_idsdiffer : ~ one == zero;
  f_comm1     : forall {a b}, op1 a b == op1 b a;
  f_comm2     : forall {a b}, op2 a b == op2 b a;
  f_distrib   : forall {a b c}, (op2 a (op1 b c)) == op1 (op2 a b) (op2 a c)
}.
Check field.

Require Import Psatz.
Require Import Nsatz.
Require Import QArith.
Open Scope Q_scope.

Definition qmult (n m: Q) := n * m.
Definition qid2 := 1.
Definition qinv2 (n: Q) := 1 / n.

(** < Q, +, *, 0, 1, ^{-1+}, ^{-1*} > as a field instance **)
Program Instance field_rationals: `(@field Q (Qeq_setoid) _ qmult _ qid2 _ qinv2 group_rationals).
Obligation 1. unfold qmult. symmetry. apply Qmult_assoc. Qed. 
Next Obligation. unfold qmult, qid2. apply Qmult_1_l. Qed.
Next Obligation. unfold qadd, qinv, qid. rewrite Qplus_comm, Qplus_opp_r. reflexivity. Qed. 
Next Obligation. unfold qmult, qinv2, qid2, qid in *. revert H0. rewrite H. psatz Q 1. Qed.
Next Obligation. unfold qadd. apply Qplus_comm. Qed.
Next Obligation. unfold qmult. apply Qmult_comm. Qed.
Next Obligation. unfold qadd, qmult. apply Qmult_plus_distr_r. Qed.
Check field_rationals.

Require Import ZArith_base.
Require Import Rdefinitions.
Require Import Coq.Reals.Raxioms.
Local Open Scope R_scope.

Definition rmult (n m: R) := n * m.
Definition rid2 := 1.
Definition rinv2 (n: R) := 1 / n.

(** < R, +, *, 0, 1, ^{-1+}, ^{-1*} > as a field instance **)
(** Obligation 3 has currently no witness FIXED **)
Program Instance field_reals: `(@field R _ _ rmult _ rid2 _ rinv2 group_reals).
Obligation 1. unfold rmult. apply Rmult_assoc. Qed.
Next Obligation. unfold rmult, rid2. apply Rmult_1_l. Qed.
Next Obligation. unfold radd, rinv, rid. rewrite Rplus_comm, Rplus_opp_r. reflexivity. Qed. 
Next Obligation. unfold rmult, rinv2, rid2, rid in *. revert H0; generalize (1/0). intros. psatz R 1. Qed. 
Next Obligation. unfold rid, rid2. apply R1_neq_R0. Qed.
Next Obligation. unfold radd. apply Rplus_comm. Qed.
Next Obligation. unfold rmult. apply Rmult_comm. Qed.
Next Obligation. unfold radd, rmult. apply  Rmult_plus_distr_l. Qed.
Check field_reals.

End Make.