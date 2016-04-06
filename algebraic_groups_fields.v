Require Import SetoidClass.

Class group (G: Set) `(Setoid G) (opG: G -> G -> G) (zeroG: G) (invG: G -> G) :=
{
  g_assoc    : forall {a b c}, opG (opG a b) c == opG a (opG b c);
  g_identity : forall {a}, opG zeroG a == a;
  g_inverse  : forall {a}, opG (invG a) a == zeroG
}.
Check group.

Class abelian_group (G: Set) (sG: Setoid G) (opG: G -> G -> G) (zeroG: G) (invG: G -> G)
                    (gG: (@group G sG opG zeroG invG)) :=
{
  g_comm    : forall {a b: G}, (opG a b) == (opG b a)
}.
Check abelian_group.


Class group_hom (G H: Set) (h: G -> H) (sG: Setoid G) (opG: G -> G -> G) (zeroG: G) (invG: G -> G)
                                       (sH: Setoid H) (opH: H -> H -> H) (zeroH: H) (invH: H -> H) 
                                       `(@group G sG opG zeroG invG)
                                       `(@group H sH opH zeroH invH)
:=
{
  h1 : forall (a b: G), h (opG a b) == opH (h a) (h b);
  h2 : forall (a: G),   h (invG a)  == invH (h a)
}.
Check group_hom.


Definition kernel (G H: Set) (h: G -> H) (sG: Setoid G) (opG: G -> G -> G) (zeroG: G) (invG: G -> G)
                                         (sH: Setoid H) (opH: H -> H -> H) (zeroH: H) (invH: H -> H)
                  (gG: (@group G sG opG zeroG invG))
                  (gH: (@group H sH opH zeroH invH))
                  `(@group_hom G H h sG opG zeroG invG sH opH zeroH invH gG gH) := { u: G | h u == zeroH }.
Check kernel.

Definition image (G H: Set) (h: G -> H) (sG: Setoid G) (opG: G -> G -> G) (zeroG: G) (invG: G -> G)
                                        (sH: Setoid H) (opH: H -> H -> H) (zeroH: H) (invH: H -> H)
                 (u: G)
                 (gG: (@group G sG opG zeroG invG))
                 (gH: (@group H sH opH zeroH invH))
                 `(@group_hom G H h sG opG zeroG invG sH opH zeroH invH gG gH) := { hu: H | hu == h u}.
Check image.

Class field (F: Set) (s: Setoid F) (op1 op2: F -> F -> F) (zero one: F) (inv1 inv2: F -> F)
                     (g1: @group F s op1 zero inv1) :=
{

  f_assoc     : forall {a b c}, op2 (op2 a b) c == op2 a (op2 b c);
  f_identity  : forall {a}, op2 one a == a;
  f_inverse   : forall a: F, a == zero -> op2 (inv2 a) a == one -> False;
  f_idsdiffer : ~ one == zero;
  f_comm1     : forall {a b}, op1 a b == op1 b a;
  f_comm2     : forall {a b}, op2 a b == op2 b a;
  f_distrib   : forall {a b c}, (op2 a (op1 b c)) == op1 (op2 a b) (op2 a c)
}.
Check field.

(** subgroups
Definition subgroup (G: Set) (sG: Setoid G) (opG: G -> G -> G) (zeroG: G) (invG: G -> G)
                             (gG: (@group G sG opG zeroG invG))
                    (P: G -> Prop)
                             {sSG: Setoid { u: G | P u }} {opSG: { u: G | P u } -> { u: G | P u } -> { u: G | P u }} {zeroSG: { u: G | P u }} 
                             {invSG: { u: G | P u } -> { u: G | P u }} :=
                    (@group { u: G | P u } sSG opSG zeroSG invSG).

Check subgroup.
**)

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

Program Instance abelian_group_integers: (@abelian_group Z (Zeq_setoid) zadd zid zinv group_integers).
Obligation 1. unfold zadd. omega. Qed.

Check abelian_group_integers.

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
  { equiv := (eq(A:=R)) ; setoid_equiv := eq_equivalence}.

(** < R, +, 0, ^{-1+} > as a group instance **)
Program Instance group_reals: (@group R (Req_setoid) radd rid rinv).
Obligation 1. unfold radd. apply Rplus_assoc. Qed.
Next Obligation. unfold radd, rinv, rid. apply Rplus_0_l. Qed.
Next Obligation. unfold radd, rinv, rid. specialize (@Rplus_opp_r a).
  intros. rewrite <- H. apply Rplus_comm. Qed.

Check group_reals.

Definition rmult (n m: R) := n * m.
Definition rid2 := 1%R.
Definition rinv2 (n: R) := 1 / n.

(** < R, +, *, 0, 1, ^{-1+}, ^{-1*} > as a field instance **)
(** Obligation 3 has currently no witness **)
Program Instance field_reals: `(@field R _ _ rmult _ rid2 _ rinv2 group_reals).
Obligation 1. unfold rmult. apply Rmult_assoc. Qed.
Next Obligation. unfold rmult, rid2. apply Rmult_1_l. Qed.
Next Obligation. unfold rmult, rinv2, rid2, rid in *. psatz R 1. intros. contradict H0. intros. admit. (**mind the admit here**) Qed. 
Next Obligation. unfold rid, rid2. apply R1_neq_R0. Qed.
Next Obligation. unfold radd. apply Rplus_comm. Qed.
Next Obligation. unfold rmult. apply Rmult_comm. Qed.
Next Obligation. unfold radd, rmult. apply  Rmult_plus_distr_l. Qed.

Check field_reals.
End real_instances.