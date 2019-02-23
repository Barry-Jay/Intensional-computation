(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(**********************************************************************)
(*                   Substitution.v                                   *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(* adapted from Substitution.v of Project Coq  to act on SF-terms     *)
(**********************************************************************)

Require Import Arith Omega List.
Require Import IntensionalLib.SF_calculus.Test.  
Require Import IntensionalLib.SF_calculus.General.  
Require Import IntensionalLib.Wave_as_SF.SF_Terms.  
Require Import IntensionalLib.Wave_as_SF.SF_Tactics.  
Require Import IntensionalLib.Wave_as_SF.SF_reduction.  
Require Import IntensionalLib.Wave_as_SF.SF_Normal.  
Require Import IntensionalLib.Wave_as_SF.SF_Closed.  



(* Lifting *)

Definition relocate (i k n : nat) :=
  match test k i with
   (* k<=i *) | left _ => n+i
   (* k>i  *) | _ => i
  end.

Lemma relocate_null :
forall (n n0 : nat), relocate n n0 0 = n.
Proof. split_all. unfold relocate. case (test n0 n); intro; auto with arith. Qed.

Lemma relocate_lessthan : forall m n k, m<=k -> relocate k m n = (n+k). 
Proof. split_all. unfold relocate. elim(test m k); split_all; try noway. Qed. 
Lemma relocate_greaterthan : forall m n k, m>k -> relocate k m n = k. 
Proof. split_all. unfold relocate. elim(test m k); split_all; try noway. Qed. 

Ltac relocate_lt := 
try (rewrite relocate_lessthan; [| omega]; relocate_lt); 
try (rewrite relocate_greaterthan; [| omega]; relocate_lt);
try(rewrite relocate_null). 


Lemma relocate_zero_succ :
forall n k, relocate 0 (S n) k = 0.
Proof.  split_all. Qed.

Lemma relocate_succ :
forall n n0 k, relocate (S n) (S n0) k = S(relocate n n0 k).
Proof. 
intros; unfold relocate. elim(test(S n0) (S n)); elim(test n0 n); split_all. 
noway. 
noway. 
Qed. 

Lemma relocate_mono : forall M N n k, relocate M n k = relocate N n k -> M=N. 
Proof. 
intros M N n k. 
unfold relocate.
elim(test n M); elim(test n N); split_all; omega. 
Qed. 

Lemma relocate_null2 :
forall n k, relocate 0 (S n) k = 0.
Proof. split_all. Qed. 


Fixpoint lift_rec (L : SF) : nat -> nat -> SF :=
  fun k n => 
  match L with
  | Ref i => Ref (relocate i k n)
  | Op o => Op o
  | App M N => App (lift_rec M k n) (lift_rec N k n)
   end.

Definition lift (n : nat) (N : SF) := lift_rec N 0 n.


(* Lifting lemmas *)

Lemma lift_rec_null_term : 
forall (U : SF)(n: nat), lift_rec U n 0 = U.
Proof. 
simple induction U; split_all.  
relocate_lt; auto. 
rewrite H; auto. rewrite H0; auto. 
Qed.

Lemma lift1 :
 forall (U : SF) (j i k : nat),
 lift_rec (lift_rec U i j) (j + i) k = lift_rec U i (j + k).
Proof.
simple induction U; simpl in |- *;  split_all. 
unfold relocate. 
elim (test i n); elim (test (j+i) (j+ n)); split_all; try noway. 
assert(k + (j + n) = j + k + n) by omega. congruence. 
elim (test (j + i) n); split_all; try noway. rewrite H; auto. rewrite H0; auto. 
Qed. 

Lemma lift_lift_rec :
 forall (U : SF) (k p n i : nat),
 i <= n ->
 lift_rec (lift_rec U i p) (p + n) k = lift_rec (lift_rec U n k) i p.
Proof.
simple induction U; simpl in |- *;  split_all.
(* Ref *) 
unfold relocate.
elim(test i n); split_all; try noway. 
elim(test n0 n); split_all; try noway. 
elim(test (p+n0) (p+n)); split_all; try noway. 
elim(test i (k+n)); split_all; try noway. 
assert(k+(p+n) = p+ (k+n)) by omega. 
rewrite H0; auto. 
elim(test (p+n0) (p+n)); split_all; try noway. 
elim(test i n); split_all; try noway. 
elim(test n0 n); split_all; try noway. 
elim(test (p+n0) n); split_all; try noway. 
elim(test i n); split_all; try noway. 
(* Ap *)
rewrite H; split_all.  rewrite H0; split_all. 
Qed. 


Lemma lift_lift_term :
 forall (U : SF) (k p n : nat),
 lift_rec (lift p U) (p+ n) k = lift p (lift_rec U n k).
Proof.
unfold lift in |- *; intros; apply lift_lift_rec; trivial with arith.
Qed.

Lemma liftrecO : forall (U : SF) (n : nat), lift_rec U n 0 = U.
Proof.
simple induction U; simpl in |- *; intros; split_all; relocate_lt; congruence. 
Qed.

Lemma liftO : forall (U : SF) , lift 0 U = U.
Proof.
unfold lift in |- *; split_all; apply liftrecO.
Qed.

Lemma lift_rec_lift_rec :
 forall (U : SF) (n p k i : nat),
 k <= i + n ->
 i <= k -> lift_rec (lift_rec U i n) k p = lift_rec U i (p + n).

Proof.
simple induction U; split_all.
(* Ref *) 
unfold relocate. 
elim(test i n); split_all; try noway. 
elim(test k (n0 + n)); split_all; try noway. 
replace (p+(n0+n)) with (p + n0 + n) by omega. auto. 
elim(test k n); split_all; try noway. 
(* Ap *)
rewrite H; split_all; rewrite H0; split_all; split_all.
Qed. 

Lemma lift_rec_lift :
 forall (U : SF)  (n p k i : nat),
 k <= n -> lift_rec (lift  n U)  k p = lift (p + n) U.
Proof.
unfold lift in |- *; intros; rewrite lift_rec_lift_rec; trivial with arith.
Qed.

Lemma lift_rec_lift2 : 
forall M n k, lift_rec (lift 1 M) (S n) k = lift 1 (lift_rec M n k).
Proof.
split_all.
unfold lift. 
replace (S n) with (1+n) by omega.
rewrite lift_lift_rec; auto. 
omega.
Qed.

Lemma lift_rec_app: forall M N n k, lift_rec (App M N) n k = App (lift_rec M n k) (lift_rec N n k). 
Proof. split_all. Qed. 
Lemma lift_rec_op: forall o n k, lift_rec (Op o) n k = Op o. 
Proof. split_all. Qed. 
Lemma lift_rec_ref: forall i n k, lift_rec (Ref i) n k = Ref (relocate i n k). 
Proof. split_all. Qed. 

Lemma lift_rec_not_ref_0 : forall M, lift_rec M 0 1 <> Ref 0.
Proof. induction M; split_all; try discriminate. case n; split_all; discriminate. Qed. 


Lemma lift_rec_null : 
forall (U : SF) (n: nat), lift_rec U n 0 = U.
Proof. simple induction U; split_all.
 rewrite relocate_null; congruence.
rewrite H; auto. rewrite H0; auto. 
Qed.

Ltac  lift_tac := 
unfold_op; rewrite ? lift_rec_app; rewrite ? lift_rec_op; rewrite ? lift_rec_ref; relocate_lt; 
rewrite ? lift_rec_not_ref_0. 



Lemma lift_rec_preserves_compound : 
forall (M: SF), compound M -> forall (n k : nat), compound(lift_rec M n k).
Proof. 
intros M c; induction c; split_all. 
Qed. 
Hint Resolve lift_rec_preserves_compound.



Lemma lift_rec_preserves_status: 
forall M n k, status (lift_rec M n k) = status M.
Proof.
match goal with 
  | |- forall M, ?P  =>   cut (forall p M, p >= rank M -> P );
      [intros H M;  eapply2 H |
       intro p; induction p; intro M;  [ assert(rank M >0) by eapply2 rank_positive; noway |]
      ]
  end.

induction M; split_all.
rewrite IHM1. (* pepm 2: omega.  *) 
gen_case H M1. gen_case H s. gen_case H s1. gen_case H o. eapply2 IHp; omega. omega.
Qed. 

Lemma lift_rec_preserves_normal: forall M n k, normal M -> normal (lift_rec M n k).
Proof. induction M; intros. split_all. split_all. 
inversion H. apply nf_active; fold lift_rec; auto.
replace  (App (lift_rec M1 n k) (lift_rec M2 n k)) 
with (lift_rec (App M1 M2) n k) by auto. 
rewrite lift_rec_preserves_status. auto. 
simpl. eapply2 nf_compound. 
replace  (App (lift_rec M1 n k) (lift_rec M2 n k)) 
with (lift_rec (App M1 M2) n k) by auto. 
eapply2 lift_rec_preserves_compound. 
Qed. 



Lemma lift_rec_closed: forall M n k, maxvar M = 0 -> lift_rec M n k = M. 
Proof. induction M; split_all. omega. max_out. rewrite IHM1; auto;  rewrite IHM2; auto. Qed. 

Lemma map_lift0 : forall Ms, map (lift 0) Ms = Ms. 
Proof. induction Ms; split_all.   rewrite IHMs. unfold lift; rewrite lift_rec_null. auto. Qed.


Lemma lift_preserves_maxvar2:
  forall M, forall k, maxvar (lift k M) - k = maxvar M.
Proof.
  induction M; split_all. relocate_lt. induction k; split_all.
  rewrite max_minus. unfold lift in *; rewrite IHM1; rewrite IHM2; auto.
Qed.
  
Lemma lift_rec_reflects_compound : forall M n k, compound (lift_rec M n k) -> compound M. 
Proof. 
induction M; split_all; inversion H; subst; split_all. 
gen_case H1 M1; try discriminate.  invsub.
case o; auto.  
gen_case H1 M1; try discriminate. inversion H1. 
gen_case H2 s; try discriminate. case o; auto. 
Qed. 

Lemma lift_rec_reflects_normal : forall M n k, normal (lift_rec M n k) -> normal M. 
Proof. 
induction M; split_all. inversion H; split_all. 
replace (App (lift_rec M1 n k) (lift_rec M2 n k)) with (lift_rec (App M1 M2) n k) in H4 by auto. 
rewrite lift_rec_preserves_status in *. eapply2 nf_active. 
replace (App (lift_rec M1 n k) (lift_rec M2 n k)) with (lift_rec (App M1 M2) n k) in H4 by auto. 
eapply2 nf_compound. eapply2 lift_rec_reflects_compound.
Qed. 

(* Substitution *)


Definition insert_Ref (N : SF) (i k : nat) :=
  match compare k i with
  
   (* k<i *) | inleft (left _) => Ref (pred i)
   (* k=i *) | inleft _ => lift k N
   (* k>i *) | _ => Ref i
  end.

Fixpoint subst_rec (L : SF) : SF -> nat -> SF :=
  fun (N : SF) (k : nat) =>
  match L with
  | Ref i => insert_Ref N i k
  | Op o => Op o
  | App M M' => App (subst_rec M N k) (subst_rec M' N k)
  end.

Lemma subst_rec_op: 
forall o N k, subst_rec (Op o) N k = Op o.
Proof.  split_all. Qed. 

Lemma subst_rec_app: 
forall M1 M2 N k, subst_rec (App M1 M2) N k = App (subst_rec M1 N k) (subst_rec M2 N k).
Proof.  split_all. Qed. 

Lemma subst_rec_ref: forall i N k,  subst_rec (Ref i) N k = insert_Ref N i k.
Proof.  split_all. Qed. 
                                                      

Definition subst (M N : SF) := subst_rec M N 0.


(* The three cases of substitution of U for (Ref n) *)

Lemma subst_eq :
 forall (M U : SF) (n : nat), subst_rec (Ref n) U n = lift n U. 
Proof.
simpl in |- *; unfold insert_Ref in |- *; split_all. 
elim (compare n n); intro P; try noway. 
elim P; intro Q; simpl in |- *; trivial with arith; try noway.
Qed.

Lemma subst_gt :
 forall (M U : SF) (n p : nat),
 n > p -> subst_rec (Ref n) U p = Ref (pred n).
Proof.
simpl in |- *; unfold insert_Ref in |- *.
intros; elim (compare p n); intro P.
elim P; intro Q; trivial with arith.
absurd (n > p); trivial with arith; rewrite Q; trivial with arith.
absurd (n > p); auto with arith.
Qed. 

Lemma subst_lt :
 forall (M U : SF) (n p : nat), p > n -> subst_rec (Ref n) U p = Ref n.
Proof.
simpl in |- *; unfold insert_Ref in |- *.
intros; elim (compare p n); intro P; trivial with arith.
absurd (p > n); trivial with arith; elim P; intro Q; auto with arith.
rewrite Q; trivial with arith.
Qed.

(* Substitution lemma *)

Lemma lift_rec_subst_rec :
 forall (V U : SF) (k p n : nat),
 lift_rec (subst_rec V U p) (p + n) k =
 subst_rec (lift_rec V (S (p + n)) k) (lift_rec U n k) p.
Proof.
simple induction V; split_all. 
(* 1 Ref *)
unfold insert_Ref, relocate in |- *.
elim (test (S(p + n0)) n); elim (compare p n); split_all.
elim a; elim(compare p (k+n)); split_all. 
unfold relocate. 
elim(test (p+n0) (pred n)); elim a1; split_all; try noway. 
replace (k + pred n) with (pred (k + n)) by omega; auto.
noway. 
noway. 
noway. 
noway. 
elim a; split_all.
unfold relocate. elim(test(p+n0) (pred n)); split_all. 
noway.
unfold lift.
rewrite lift_lift_rec; auto; omega. 
unfold relocate. 
elim(test (p+n0) n); split_all. 
noway.
rewrite H; auto; rewrite H0; auto. 
Qed. 


Lemma lift_subst :
 forall (U V : SF) (k n : nat),
 lift_rec (subst U V) n k =
 subst (lift_rec U (S n) k) (lift_rec V n k).
Proof.
unfold subst in |- *; intros.
replace n with (0 + n).
rewrite lift_rec_subst_rec; trivial with arith.
auto. 
Qed.

Lemma subst_rec_lift_rec1 :
 forall (U V : SF) (n p k : nat),
 k <= n ->
 subst_rec (lift_rec U k p) V (p + n) =
 lift_rec (subst_rec U V n) k p.
Proof.
simple induction U; intros; simpl in |- *; split_all.
(* Ref *) 
unfold insert_Ref, relocate. 
elim(test k n); split_all. 
elim(compare n0 n); split_all; try noway. 
elim a0; split_all; try noway. 
elim(compare (p+n0) (p+n)); split_all. 
elim a2; split_all; try noway. 
unfold relocate. 
elim(test k (pred n)); split_all; try noway. 
assert(pred (p+n) = p + pred n) by omega. auto. 
noway. 
elim(compare (p+n0) (p+n)); split_all. 
elim a1; split_all; try noway. 
unfold lift. rewrite lift_rec_lift_rec; split_all; try omega.  
unfold lift. rewrite lift_rec_lift_rec; split_all; try omega.  
elim(compare (p+n0) (p+n)); split_all. 
elim a0; split_all; try noway. 
unfold relocate. 
elim(test k n); split_all; try noway. 
elim(compare (p+n0) n); split_all; try noway. 
elim a; split_all; try noway. 
elim(compare n0 n); split_all; try noway. 
elim a; split_all; try noway. 
unfold relocate. 
elim(test k n); split_all; try noway. 
(* 1 *) 
rewrite H; split_all.  rewrite H0; split_all. 
Qed. 

Lemma subst_rec_lift1 :
 forall (U V : SF) (n p : nat),
 subst_rec (lift p U) V (p + n) = lift p (subst_rec U V n).
Proof.
unfold lift in |- *; intros; rewrite subst_rec_lift_rec1;
 trivial with arith.
Qed.


Lemma subst_rec_lift_rec :
 forall (U V : SF) (p q n : nat),
 q <= p + n ->
 n <= q -> subst_rec (lift_rec U n (S p)) V q = lift_rec U n p.
Proof.
simple induction U; intros; simpl in |- *; split_all. 
unfold relocate. elim(test n0 n); split_all. 
unfold insert_Ref. 
elim(compare q (S(p+n))); split_all; try noway. 
elim a0; split_all; try noway. 
unfold insert_Ref. 
elim(compare q n); split_all; try noway. 
elim a; split_all; try noway. 

(* 1 *) 
rewrite H; split_all. 
rewrite H0; auto.
Qed.

(* subst_rec_subst_rec *)

Lemma subst_rec_subst_rec :
 forall (V U W : SF) (n p : nat),
 subst_rec (subst_rec V U p) W (p + n) =
 subst_rec (subst_rec V W (S (p + n))) (subst_rec U W n) p.
Proof.
simple induction V;  split_all.

unfold insert_Ref in |- *.
elim (compare p n); split_all. 
elim a; split_all. 
elim (compare (S (p + n0)) n); split_all. 
elim a1; split_all; try noway. 
unfold insert_Ref.
elim (compare (p+n0) (pred n)); split_all; try noway. 
elim a3; split_all; try noway.
elim (compare p (pred n)); split_all; try noway. 
elim a5; split_all; try noway.
unfold lift; split_all. 
unfold insert_Ref. 
elim (compare (p+n0) (pred n)); split_all; try noway. 
elim a2; split_all; try noway.
subst. unfold lift. 
rewrite subst_rec_lift_rec; split_all; try omega. 
unfold insert_Ref. 
elim(compare (p+n0) (pred n)); split_all; try noway. 
elim a1; split_all; try noway. 
elim(compare p n); split_all; try noway. 
elim a1; split_all; try noway. 
elim (compare (S (p + n0)) n); split_all; try noway. 
elim a0; split_all; try noway.
unfold insert_Ref. 
elim(compare p n); split_all; try noway. 
elim a0; split_all; try noway. 
unfold lift. 
subst. 
rewrite subst_rec_lift_rec1; split_all.  omega. 

unfold insert_Ref. 
elim(compare (p+n0) n); split_all; try noway. 
elim a; split_all; try noway.
elim(compare (S(p+n0)) n); split_all; try noway. 
elim a; split_all; try noway. 
unfold insert_Ref. 
elim(compare p n); split_all; try noway. 
elim a; split_all; try noway. 
rewrite H; auto. rewrite H0; auto. 
Qed.


Lemma subst_rec_subst_0 :
 forall (U V W : SF) (n : nat),
 subst_rec (subst_rec V U 0) W n =
 subst_rec (subst_rec V W (S n)) (subst_rec U W n) 0.
Proof.
intros; pattern n at 1 3 in |- *.
replace n with (0 + n) by trivial with arith.
rewrite (subst_rec_subst_rec V U W n 0); trivial with arith.
Qed.

(**************************)
(* The Substitution Lemma *)
(**************************)

Lemma substitution :
 forall (U V W : SF) (n : nat),
 subst_rec (subst U V) W n =
 subst (subst_rec U W (S n)) (subst_rec V W n).
Proof.
unfold subst in |- *; intros; apply subst_rec_subst_0; trivial with arith.
Qed.

(* to show (\ t)0 -> t  *) 


Lemma subst_lift_null :
forall (W V : SF)(n : nat), subst_rec (lift_rec W n 1) V n = W.
Proof.
simple induction W; split_all. 
unfold insert_Ref. 
unfold relocate. 
elim(test n0 n); split_all. 
elim(compare n0 (S n)); split_all.
elim a0; split_all; noway. 
noway. 
elim(compare n0 n); split_all.
elim a; split_all. noway. 
noway.
rewrite H; auto; rewrite H0; auto. 
Qed. 


(* more  Properties *) 



Lemma subst_rec_lift2 : 
forall M N n , subst_rec (lift 1 M) N (S n)  = lift 1 (subst_rec M N n).
Proof.
split_all.
unfold lift. 
replace (S n) with (1+n) by omega.
rewrite subst_rec_lift_rec1; auto. 
omega.
Qed.



Lemma insert_Ref_lt : forall M n k, n< k -> insert_Ref M n k = Ref n.
Proof.
induction M; unfold insert_Ref; split_all. 
elim (compare k n0); split_all. 
elim a; split_all; try noway. 
elim (compare k n); split_all. 
elim a; split_all; try noway. 
elim (compare k n); split_all. 
elim a; split_all; try noway. 
Qed. 

Lemma insert_Ref_eq : forall M n k, n= k -> insert_Ref M n k = lift k M.
Proof.
induction M; unfold insert_Ref; split_all. 
elim (compare k n0); split_all. 
elim a; split_all; try noway. 
unfold lift; unfold lift_rec. unfold relocate. elim(test 0 n); split_all; try noway. 
elim (compare k n); split_all. 
elim a; split_all; try noway. 
unfold lift; unfold lift_rec. unfold relocate. elim(test 0 n); split_all; try noway. 
elim (compare k n); split_all. 
elim a; split_all; try noway. 
noway.
Qed. 


Lemma insert_Ref_gt : forall M n k, n> k -> insert_Ref M n k = Ref (pred n).
Proof.
induction M; unfold insert_Ref; split_all. 
elim (compare k n0); split_all. 
elim a; split_all; try noway. 
noway. 
elim (compare k n); split_all. 
elim a; split_all; try noway. 
noway. 
elim (compare k n); split_all. 
elim a; split_all; try noway. 
noway.
Qed. 

Ltac insert_Ref_out := 
try (rewrite insert_Ref_lt; [|unfold relocate; split_all; omega]; insert_Ref_out); 
try (rewrite insert_Ref_eq; [|unfold relocate; split_all; omega]; insert_Ref_out); 
try (rewrite insert_Ref_gt; [|unfold relocate; split_all; omega]; insert_Ref_out). 


Lemma fold_subst :  forall M1 M2 N, App (subst_rec M1 N 0) M2 = subst (App M1 (lift 1 M2)) N.
Proof.
  unfold subst, lift, subst_rec; split_all; fold subst_rec.
  rewrite subst_rec_lift_rec; try omega. rewrite lift_rec_null; auto.  
Qed.



Ltac  subst_tac := 
unfold_op; unfold subst; 
rewrite ? subst_rec_app; rewrite ? subst_rec_op; rewrite ? subst_rec_ref; 
rewrite ? subst_rec_lift_rec; try omega; rewrite ? lift_rec_null; 
unfold subst_rec; fold subst_rec; insert_Ref_out; unfold pred.  



Definition subst_preserves_l (red: termred) := 
forall (M M' N : SF), red M M' -> red  (subst M N) (subst M' N).

Definition subst_preserves_r (red: termred) := 
forall (M N N' : SF), red N N' -> red  (subst M N) (subst M N').

Definition subst_preserves (red: termred) := 
forall (M M' : SF), red M M' -> forall N N', red N N' -> 
red  (subst M N) (subst M' N').

Lemma subst_preserves_l_multi_step : 
forall (red: termred), subst_preserves_l red -> subst_preserves_l (multi_step red). 
Proof. unfold subst_preserves_l. 
 induction 2; split_all.  
apply succ_red with (subst N0 N); auto.
Qed.

Lemma subst_preserves_r_multi_step : 
forall (red: termred), subst_preserves_r red -> subst_preserves_r (multi_step red). 
Proof. unfold subst_preserves_r. 
 induction 2; split_all.  
apply succ_red with (subst M N); auto.
Qed. 

Lemma subst_preserves_multi_step : 
forall (red: termred), subst_preserves_l red -> subst_preserves_r red -> subst_preserves (multi_step red). 
Proof. 
unfold subst_preserves. split_all.
assert(transitive (multi_step red)) by eapply2 transitive_red. 
unfold transitive in *.
apply X with  (subst M' N); auto. 
eapply2 subst_preserves_l_multi_step.
eapply2 subst_preserves_r_multi_step.
Qed.


Lemma subst_preserves_compound: 
forall (M: SF), compound M -> forall N, compound(subst M N).
Proof. intros M c; induction c; unfold subst; split_all. Qed. 
Hint Resolve subst_preserves_compound.

Lemma  subst_rec_preserves_components_l : forall (M : SF) n k, compound M -> 
  subst_rec(left_component M) n k = left_component(subst_rec M n k).
Proof. induction M; split_all; inv1 compound. Qed. 


Lemma  subst_rec_preserves_components_r : 
forall (M : SF),  compound M -> forall n k,   
subst_rec(right_component M) n k = right_component(subst_rec M n k).
Proof. induction M; split_all; inversion H; subst; split_all. Qed. 
Lemma subst_rec_preserves_compounds: 
forall M N k, compound M -> compound (subst_rec M N k). 
Proof. intros; inv1 compound. Qed. 

Lemma subst_rec_preserves_left_component: 
forall M N k, compound M -> 
              subst_rec (left_component M) N k = left_component (subst_rec M N k) . 
Proof. intros; inv1 compound. Qed. 

Lemma subst_rec_preserves_right_component: 
forall M N k, compound M -> 
              subst_rec (right_component M) N k = right_component (subst_rec M N k) . 
Proof. intros; inv1 compound. Qed. 

Lemma subst_preserves_sf_red1 : subst_preserves sf_red1. 
Proof. 
red. 
intros M M' R; induction R; unfold subst; split_all. 
(* 5 *) 
unfold insert_Ref. elim(compare 0 i); split_all. elim a; split_all. 
unfold lift. repeat rewrite lift_rec_null_term; auto. 
(* 4 *) 
eapply2 app_sf_red. 
(* 3 *) 
eapply2 s_red. 
(* 2 *) 
eapply2 k_red. 
(* 1 *) 
eapply2 f_red. 
Qed. 

Lemma subst_preserves_sf_red : subst_preserves sf_red. 
Proof. eapply2 subst_preserves_multi_step. red; split_all. 
eapply2 subst_preserves_sf_red1. red; split_all. 
eapply2 subst_preserves_sf_red1. 
Qed. 

Lemma subst_rec_closed: forall M N k, maxvar M <= k -> subst_rec M N k = M. 
Proof. 
induction M; split_all. 
unfold insert_Ref. elim(compare k n); split_all. elim a; split_all. noway. noway. 
assert (max (maxvar M1) (maxvar M2) >= maxvar M1) by eapply2 max_is_max. 
assert (max (maxvar M1) (maxvar M2) >= maxvar M2) by eapply2 max_is_max. 
rewrite IHM1; try omega;  rewrite IHM2; try omega. auto. 
Qed. 


Lemma subst_decreases_maxvar : 
forall M N,  max (pred (maxvar M)) (maxvar N) >= maxvar(subst M N).
Proof. 
unfold subst; induction M; split_all. 
unfold insert_Ref. 
case n; split_all. unfold lift. rewrite lift_rec_null_term. auto.
case (maxvar N); split_all. 
assert(max n0 n1  >= n0) by eapply2 max_is_max. 
omega. 
omega. 
(* 1 *) 
rewrite max_pred.
assert(max (max (pred (maxvar M1)) (pred (maxvar M2))) (maxvar N) >=
max (pred (maxvar M1)) (maxvar N)).
eapply2 max_monotonic. eapply2 max_is_max. 
assert(max (max (pred (maxvar M1)) (pred (maxvar M2))) (maxvar N) >=
max (pred (maxvar M2)) (maxvar N)).
eapply2 max_monotonic. eapply2 max_is_max. 
assert(max (max (pred (maxvar M1)) (pred (maxvar M2))) (maxvar N) >=
max(max (pred (maxvar M1)) (maxvar N)) (max (pred (maxvar M2)) (maxvar N))).
eapply2 max_max2. 
assert(max (max (pred (maxvar M1)) (maxvar N))
         (max (pred (maxvar M2)) (maxvar N))>= 
max (maxvar (subst_rec M1 N 0)) (maxvar (subst_rec M2 N 0))).
eapply2 max_monotonic. 
omega. 
Qed. 



Lemma subst_closed : forall M, maxvar M = 0 -> forall N, subst M N = M.
Proof.
induction M; split_all; subst. omega. 
max_out. unfold subst in *; simpl. rewrite IHM1; try omega; rewrite IHM2; try omega; split_all. 
Qed. 


Ltac closed_tac M := repeat (rewrite (subst_rec_closed M); [| auto]); 
                     repeat (rewrite (lift_rec_closed M); [| auto]).



Lemma fold_subst_list:
  forall sigma M N,  App (fold_left subst sigma M) N =
                     fold_left subst sigma (App M (lift (length sigma) N)).
Proof.
  induction sigma; split_all.
  (* 2 *)
  unfold lift; rewrite lift_rec_null. auto. 
  (* 1 *) 
  rewrite IHsigma. unfold subst. simpl. unfold lift. rewrite subst_rec_lift_rec; try omega. auto.
Qed.


Lemma list_subst_preserves_op:
  forall sigma o, fold_left subst sigma (Op o) = Op o. 
  Proof. induction sigma; split_all. unfold subst in *. split_all. Qed. 

Lemma list_subst_preserves_app:
  forall sigma M N, fold_left subst sigma (App M N) =
                    App (fold_left subst sigma M) (fold_left subst sigma N).
  Proof. induction sigma; split_all. unfold subst in *. split_all. Qed. 

Lemma list_subst_preserves_sf_red:
  forall sigma M N, sf_red M N -> sf_red (fold_left subst sigma M) (fold_left subst sigma N).
Proof.  induction sigma; split_all. eapply2 IHsigma. eapply2 subst_preserves_sf_red. Qed. 



Lemma list_subst_lift: forall sigma M, fold_left subst sigma (lift (length sigma) M) = M.
Proof.
  induction sigma; split_all. unfold lift; rewrite lift_rec_null. auto. 
unfold lift, subst. rewrite subst_rec_lift_rec; try omega. unfold lift in *. rewrite IHsigma. auto. 
Qed.

