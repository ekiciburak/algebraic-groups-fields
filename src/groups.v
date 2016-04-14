Require Import SetoidClass.

Module Type T.
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


(** subgroups
Definition subgroup (G: Set) (sG: Setoid G) (opG: G -> G -> G) (zeroG: G) (invG: G -> G)
                             (gG: (@group G sG opG zeroG invG))
                    (P: G -> Prop)
                             {sSG: Setoid { u: G | P u }} {opSG: { u: G | P u } -> { u: G | P u } -> { u: G | P u }} {zeroSG: { u: G | P u }} 
                             {invSG: { u: G | P u } -> { u: G | P u }} :=
                    (@group { u: G | P u } sSG opSG zeroSG invSG).

Check subgroup.
**)

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

End T.