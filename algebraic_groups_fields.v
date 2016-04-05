Require Import SetoidClass.

Class group (G: Type) `(Setoid G) (op: G -> G -> G) (zero: G) (inv: G -> G) :=
{
  g_assoc    : forall {a b c}, op (op a b) c == op a (op b c);
  g_identity : forall {a}, op zero a == a;
  g_inverse  : forall {a}, op (inv a) a == zero
}.
Check group.

Class field (F: Type) `(s: Setoid F) (op1 op2: F -> F -> F) (zero one: F) (inv1 inv2: F -> F)
                      `(@group F s op1 zero inv1) :=
{
  f_assoc     : forall {a b c}, op2 (op2 a b) c == op2 a (op2 b c);
  f_identity  : forall {a}, op2 one a == a;
  f_idsdiffer : ~ one == zero; 
  f_inverse   : forall a: F, (a == zero) -> op2 (inv2 a) a == one -> False;
  f_comm1     : forall {a b}, op1 a b == op1 b a;
  f_comm2     : forall {a b}, op2 a b == op2 b a;
  f_distrib   : forall {a b c}, (op2 a (op1 b c)) == op1 (op2 a b) (op2 a c)
}.
Check field.

Section int_instances.

Require Import Psatz.
Require Import Nsatz.
Require Import ZArith.
Open Scope Z_scope.

Definition zadd (n m: Z) := n + m.
Definition zid := 0%Z.
Definition zinv (n: Z) := -n.

Program Instance Zeq_setoid : Setoid Z :=
  { equiv := eq ; setoid_equiv := eq_equivalence }.

(** < Z, +, 0, ^{-1+} > as a group instance **)
Program Instance group_integers: (@group Z (Zeq_setoid) zadd zid zinv).
Obligation 1. unfold zadd. omega. Qed.
Next Obligation. unfold zadd, zinv, zid. omega. Qed.

Check group_integers.

Definition zmult (n m: Z) := n * m.
Definition zid2 := 1.
Definition zinv2 (n: Z) := 1 / n.

(** < Z, +, *, 0, 1, ^{-1+}, ^{-1*} > as a field instance **)
Program Instance field_integers: `(@field Z (Zeq_setoid) _ zmult _ zid2 _ zinv2 group_integers).
Obligation 1. unfold zmult. apply Zmult_assoc_reverse. Qed.
Next Obligation. induction a; reflexivity. Qed.
(** If it fails here that means that obligations 3 and 4 cannot be proven automatically.
To get these proofs, please make sure that csdp is installed and added to the PATH **)
Next Obligation. unfold zadd. omega. Qed.
Next Obligation. unfold zmult. apply Zmult_comm. Qed.
Next Obligation. unfold zadd,zmult. apply Zmult_plus_distr_r. Qed.
Check field_integers.
End int_instances.

Section rat_instances.

Require Import QArith.
Open Scope Q_scope.

Definition qadd (n m: Q) := n + m.
Definition qid := 0%Q.
Definition qinv (n: Q) := -n.

Program Instance Qeq_setoid : Setoid Q :=
  { equiv := Qeq ; setoid_equiv := Q_Setoid}.

(** < Q, +, 0, ^{-1+} > as a group instance **)
Program Instance group_rationals: (@group Q (Qeq_setoid) qadd qid qinv).
Obligation 1. unfold qadd. symmetry. apply Qplus_assoc. Qed.
Next Obligation. unfold qadd, qid. apply Qplus_0_l. Qed.
Next Obligation. unfold qadd, qid, qinv. specialize (@Qplus_opp_r (-a)). intros.
  rewrite Qopp_involutive in H. exact H. Qed.

Check group_rationals.

Definition qmult (n m: Q) := n * m.
Definition qid2 := 1.
Definition qinv2 (n: Q) := 1 / n.

(** < Q, +, *, 0, 1, ^{-1+}, ^{-1*} > as a field instance **)
Program Instance field_rationals: `(@field Q (Qeq_setoid) _ qmult _ qid2 _ qinv2 group_rationals).
Obligation 1. unfold qmult. symmetry. apply Qmult_assoc. Qed.
Next Obligation. unfold qmult, qid2. apply Qmult_1_l. Qed.
Next Obligation. unfold qmult, qinv2, qid2, qid in *. revert H0. rewrite H. psatz Q 1. Qed.
Next Obligation. unfold qadd. apply Qplus_comm. Qed.
Next Obligation. unfold qmult. apply Qmult_comm. Qed.
Next Obligation. unfold qadd, qmult. apply Qmult_plus_distr_r. Qed.

Check field_rationals.

End rat_instances.

Section real_instances.

Require Import ZArith_base.
Require Import Rdefinitions.
Require Import Coq.Reals.Raxioms.
Local Open Scope R_scope.

Definition radd (n m: R) := n + m.
Definition rid := 0.
Definition rinv (n: R) := -n.

Program Instance Req_setoid : Setoid R :=
  { equiv := eq ; setoid_equiv :=  eq_equivalence}.

(** < R, +, 0, ^{-1+} > as a group instance **)
Program Instance group_reals: (@group R (Req_setoid) radd rid rinv).
Obligation 1. unfold radd. apply Rplus_assoc. Qed.
Next Obligation. unfold radd, rinv, rid. apply Rplus_0_l. Qed.
Next Obligation. unfold radd, rinv, rid. specialize (@Rplus_opp_r a).
  intros. rewrite <- H. apply Rplus_comm. Qed.

Check group_reals.

Definition rmult (n m: R) := n * m.
Definition rid2 := 1.
Definition rinv2 (n: R) := 1 / n.

(** < R, +, *, 0, 1, ^{-1+}, ^{-1*} > as a field instance **)
(** Obligation 4 has currently no witness **)
Program Instance field_reals: `(@field R (Req_setoid) _ rmult _ rid2 _ rinv2 group_reals).
Obligation 1. unfold rmult. apply Rmult_assoc. Qed.
Obligation 2. unfold rmult, rid2. apply Rmult_1_l. Qed.
Obligation 3. unfold rid, rid2. apply R1_neq_R0. Qed.
(* Obligation 4. unfold rmult, rinv2, rid2, rid in *. intros. revert H0. psatz R. admit. Qed. *)
Obligation 5. unfold radd. apply Rplus_comm. Qed.
Obligation 6. unfold rmult. apply Rmult_comm. Qed.
Obligation 7. unfold radd, rmult. apply  Rmult_plus_distr_l. Qed.

(* Check field_reals.
End real_instances. *)
