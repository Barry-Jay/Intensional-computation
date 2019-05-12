(**********************************************************************)
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

(**********************************************************************)
(*                       Star.v                                       *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)



Require Import Arith Omega Max Bool List.
Require Import IntensionalLib.SF_calculus.Test.  
Require Import IntensionalLib.SF_calculus.General.  
Require Import IntensionalLib.Tree_calculus.Tree_Terms.  
Require Import IntensionalLib.Tree_calculus.Tree_Tactics.  
Require Import IntensionalLib.Tree_calculus.Tree_reduction.  
Require Import IntensionalLib.Tree_calculus.Tree_Normal.  
Require Import IntensionalLib.Tree_calculus.Tree_Closed.  
Require Import IntensionalLib.Tree_calculus.Substitution.  
Require Import IntensionalLib.Tree_calculus.Tree_Eval.  


(* naive abstraction -- no optimisation *) 

Fixpoint star M := 
match M with 
  | Ref 0 => i_op
| Ref (S n) => App  k_op  (Ref n)
| Op o => App k_op (Op o)
| App M1 M2 => App (App (Op Node) (App (Op Node) (star M2))) (star M1)
end
.

Proposition star_beta: forall M N, sf_red (App (star M) N) (subst M N).
Proof.
induction M; split_all. 
(* 3 *) 
unfold subst; case n; split_all; unfold_op;  eapply2 succ_red.
insert_Ref_out. unfold lift. rewrite lift_rec_null_term. 
eapply2 succ_red.
(* 2 *) 
unfold_op; eval_tac. 
(* 1 *)
unfold subst; simpl. 
eapply succ_red. eapply2 s_red.
eapply2 preserves_app_sf_red. 
Qed.



Proposition star_beta2: forall M N P, sf_red (App (App (star (star M)) N) P) (subst (subst M (lift 1 P)) N).
Proof.
induction M; intros.
(* 3 *) 
case n; split_all. 
(* 4 *) 
unfold subst; simpl. insert_Ref_out. unfold lift; rewrite lift_rec_null. 
rewrite subst_rec_lift_rec; try omega. 
rewrite lift_rec_null; auto.
repeat eval_tac. 
(* 3 *) 
case n0; split_all. 
unfold subst; simpl. insert_Ref_out. unfold lift; rewrite lift_rec_null.
unfold_op; repeat eval_tac.
unfold subst; simpl. insert_Ref_out. simpl. 
unfold_op; repeat eval_tac.
(* 2 *) 
unfold star, subst; simpl. repeat eval_tac. 
(* 1 *) 
unfold star; fold star. 
eapply transitive_red.  eapply preserves_app_sf_red. 
eapply succ_red. eapply2 s_red. 
eapply transitive_red.  eapply preserves_app_sf_red. 
eapply succ_red. eapply2 s_red. eval_tac. auto. auto. auto.   
eapply transitive_red.  eapply preserves_app_sf_red.
eapply preserves_app_sf_red. eapply preserves_app_sf_red.
auto. 
eapply succ_red. eapply2 s_red. eval_tac. auto. auto. 
eapply succ_red. eapply2 s_red.
eapply transitive_red.  eapply preserves_app_sf_red. 
eapply2 IHM1. eapply2 IHM2. 
unfold subst; auto. 
Qed. 
 
Lemma star_normal:  forall M, normal (star M).
Proof. 
induction M; split_all.
case n; unfold_op; auto. 
unfold_op; auto.
Qed.  



Lemma app_mono: forall M N P, App M N = App M P -> N = P. 
Proof.  split_all. inversion H. auto. Qed. 


Lemma star_mono: forall M N, star M = star N -> M = N. 
Proof. 
induction M; split_all. 
gen_case H n; split_all.
gen_case H N. 
gen_case H n0.
inversion H. inversion H. inversion H. 
gen_case H2 t. 
gen_case H2 n0. 
discriminate . discriminate . discriminate.
discriminate.
gen_case H N. 
gen_case H n1. discriminate.
inversion H; subst. auto. discriminate. 
discriminate. 
gen_case H N. 
gen_case H n. discriminate. discriminate.
case o; case o0; auto.  
discriminate. 
gen_case H N. 
gen_case H n. all: try discriminate. inversion H. 
gen_case H1 M2. gen_case H1 n0.  all: try discriminate. 
inversion H; subst. 
rewrite (IHM1 t); auto. rewrite (IHM2 t0); auto. 
Qed. 



(* optimising star *) 

Fixpoint eqnat n k := 
match n with 
| 0 => match k with 0 => 1 | _ => 0 end 
| S n1 => match k with 0 => 0 | S k1 => eqnat n1 k1 end 
end.


Fixpoint occurs k M := 
match M with 
| Ref n => eqnat n k 
| Op _ => 0
| App M1 M2 => occurs k M1 + occurs k M2
end. 



Lemma occurs_op: forall k o, occurs k (Op o) = 0. 
Proof. split_all. Qed. 

Lemma occurs_app: forall k M N, occurs k (App M N) = occurs k M + occurs k N. 
Proof. split_all. Qed. 

Lemma occurs_closed: forall k M, maxvar M = 0 -> occurs k M = 0.
Proof. induction M; split_all. omega. max_out.  Qed. 

Lemma occurs_lift_rec_zero: forall M k, occurs 0 (lift_rec M 0 (S k)) = 0.
Proof. 
induction M; split_all. relocate_lt. 
induction k; intros. unfold plus. auto. 
unfold plus; fold plus; auto.
rewrite IHM1; rewrite IHM2; auto. 
Qed. 


Lemma occurs_lift_rec_succ: forall M n k, occurs 0 (lift_rec M (S n) k) = occurs 0 M. 
Proof. 
induction M; split_all. unfold relocate. 
elim(test (S n0) n); split_all. 
gen_case a n;try noway. replace (k + S n1) with (S (k+n1)) by omega. auto. 
Qed. 


Lemma occurs_subst_rec_succ: forall M N k, occurs 0 (subst_rec M N (S k)) = occurs 0 M.
Proof. 
induction M; split_all. case n; split_all. 
unfold insert_Ref. elim(compare (S k) (S n0)); split_all. elim a; split_all. 
gen_case a0 n0; try omega. 
unfold lift. eapply2 occurs_lift_rec_zero.
Qed. 



Lemma occurs_false_subst_status: 
forall M N, occurs 0 M = 0 -> status (subst_rec M N 0) = status M.
Proof.
cut(forall p M, p>= rank M -> 
 forall N, occurs 0 M = 0 -> status (subst_rec M N 0) = status M). 
split_all. eapply2 H. 
induction p; split_all. 
assert(rank M >0) by eapply2 rank_positive. noway. 
induction M; intros. 
(* 3 *) 
 split_all. simpl in H0.  
generalize H0; clear H0. unfold insert_Ref. case n; split_all. 
(* 2 *) 
split_all. 
(* 1 *) 
unfold subst_rec; fold subst_rec. 
simpl in H0. simpl in H. discriminate. split_all.  simpl in *. 
assert(occurs 0 M1 = 0 /\ occurs 0 M2 = 0) by omega. 
inversion H1. 
generalize IHM1 H H2; clear IHM1 H H2; case M1; intros. 
(* 3 *) 
simpl in H2. unfold subst_rec; fold subst_rec.  unfold insert_Ref. 
gen_case H2 n. discriminate. 
(* 2 *) 
gen_case H o. 
(* 1 *) 
generalize IHM1 H H2; clear IHM1 H H2; case t; intros. 
(* 3 *) 
simpl in H2. unfold subst_rec; fold subst_rec.  unfold insert_Ref. 
gen_case H2 n. discriminate. 

(* 2 *) 
simpl in H2.  unfold subst_rec; fold subst_rec.  
case o; split_all. 
(* 1 *)
unfold subst_rec; fold subst_rec.
generalize IHM1 H H2; clear IHM1 H H2; case t1; intros. 
(* 3 *) 
simpl in H2. unfold subst_rec; fold subst_rec.  unfold insert_Ref. 
gen_case H2 n. 
(* 2 *) 
simpl in H2.  unfold subst_rec; fold subst_rec.  discriminate. 
case o; split_all. 
rewrite ! IHp; auto. simpl in H; omega. simpl in *. 
assert(occurs 0 t2 = 0 /\ occurs 0 t0 = 0) by omega. 
split_all. 
inversion H4; auto. 
(* 1 *) 
unfold subst_rec; fold subst_rec. 
replace (status (App (App (App (App t3 t4) t2) t0) M2)) with (status (App (App (App t3 t4) t2) t0))
by auto. 
replace (status (App
        (App
           (App (App (subst_rec t3 N 0) (subst_rec t4 N 0))
              (subst_rec t2 N 0)) (subst_rec t0 N 0)) 
        (subst_rec M2 N 0))) 
with
(status (App
           (App (App (subst_rec t3 N 0) (subst_rec t4 N 0))
              (subst_rec t2 N 0)) (subst_rec t0 N 0)) 
        )
by auto. 
replace (App
           (App (App (subst_rec t3 N 0) (subst_rec t4 N 0))
              (subst_rec t2 N 0)) (subst_rec t0 N 0)) 
with (subst_rec (App (App (App t3 t4) t2) t0) N 0) by auto. 
rewrite  IHp; auto. simpl in *; omega. 
Qed. 



Lemma occurs_false_subst_normal: 
forall M N, occurs 0 M = 0 -> normal M -> normal (subst_rec M N 0). 
Proof.
induction M; split_all. 
unfold insert_Ref. generalize H; clear H. case n; split_all.  discriminate. 
assert(occurs 0 M1 = 0 /\ occurs 0 M2 = 0) by omega. 
inversion H1. 
inversion H0. eapply2 nf_active. 
replace(App (subst_rec M1 N 0) (subst_rec M2 N 0)) with (subst_rec (App M1 M2) N 0) by auto. 
rewrite occurs_false_subst_status. auto. split_all.
apply nf_compound. eapply2 IHM1. eapply2 IHM2. 
replace(App (subst_rec M1 N 0) (subst_rec M2 N 0)) with (subst_rec (App M1 M2) N 0) by auto. 
eapply2 subst_rec_preserves_compounds. 
Qed.

Lemma no_subst: forall M N P, occurs 0 M = 0 -> subst_rec M N 0 = subst_rec M P 0. 
Proof. 
induction M; split_all. 
gen_case H n. discriminate. 
assert(occurs 0 M1 = 0 /\ occurs 0 M2 = 0). omega.  
split_all. inversion H0. rewrite (IHM1 N P); auto; rewrite (IHM2 N P); auto. 
Qed. 



(* Star abstraction optimised *) 

Fixpoint star_opt M := 
match M with 
| Ref 0 => i_op 
| Ref (S n) => App k_op (Ref n)
| Op o => App k_op (Op o)
| App M1 M2 =>
  match occurs 0 M1 with
    | S _ => App (App (Op Node) (App (Op Node) (star_opt M2))) (star_opt M1)
    | _ => match M2 with 
           | Ref 0 => subst M1 (Op Node)
           | _ => match occurs 0 M2 with
                  | S _ => App (App (Op Node) (App (Op Node) (star_opt M2))) (star_opt M1)
                  | _ => App k_op (subst M (Op Node))
                  end
           end
  end
end.



  (* characterising star_opt  *) 

Lemma star_opt_eta: forall M, occurs 0 M = 0 -> 
 star_opt (App M (Ref 0)) = subst M (Op Node). 
Proof.  intros. unfold star_opt; fold star_opt. rewrite H. auto. Qed. 

Lemma star_opt_occurs_false : 
forall M, occurs 0 M = 0  -> star_opt M = App k_op (subst_rec M (Op Node) 0). 
Proof.
induction M; unfold star_opt; fold star_opt; split_all. gen_case H n; split_all. 
discriminate. 
assert(occurs 0 M1 = 0 /\ occurs 0 M2 = 0) by omega. 
split_all. inversion H0. rewrite H1. rewrite H2. gen_case H2 M2. gen_case H2 n.
discriminate.  
Qed.

Lemma star_opt_occurs_true : 
forall M1 M2, occurs 0 (App M1 M2) >0 -> M2 <> Ref 0 -> 
star_opt (App M1 M2) = 
App (App (Op Node) (App (Op Node) (star_opt M2))) (star_opt M1). 
Proof.
cut(forall M, occurs 0 M >0 -> forall M1 M2, M = App M1 M2  -> M2 <> Ref 0 -> 
star_opt M = App (App (Op Node) (App (Op Node) (star_opt M2)))
 (star_opt M1)). 
intros. eapply2 H. 
(* 1 *)
induction M; intros; subst; inversion H0; subst. 
simpl in H. assert(occurs 0 M0 >0 \/ occurs 0 M3 >0) by omega.
inversion H2. 
(* 2 *) 
split_all. replace (occurs 0 M0) with (S (pred (occurs 0 M0))) by omega. auto. 
(* 1 *) 
split_all. replace (occurs 0 M3) with (S (pred (occurs 0 M3))) by omega.
case (occurs 0 M0). 
gen_case H1 M3. gen_case H1 n.  congruence.
auto. 
Qed. 


Lemma star_opt_lift: forall M, star_opt (lift 1 M) = App k_op M. 
Proof. 
split_all. 
assert(M = subst_rec (lift 1 M) (Op Node) 0). 
unfold lift; rewrite subst_rec_lift_rec; try omega. rewrite lift_rec_null; auto. 
rewrite H at 2. 
eapply2 star_opt_occurs_false.  
unfold lift. apply occurs_lift_rec_zero. 
Qed. 




Lemma star_opt_normal_app: 
forall M N, normal (App M N) -> normal (star_opt M) -> normal (star_opt N)  -> 
normal (star_opt (App M N)).
Proof. 
split_all. 
assert(occurs 0 M = 0 -> normal (subst M (Op Node))). 
intro; eapply2 occurs_false_subst_normal. inversion H; auto. 
assert((occurs 0 M + occurs 0 N) = 0 -> normal (subst (App M N) (Op Node))). 
intro; eapply2 occurs_false_subst_normal. 
gen2_case H2 H3 (occurs 0 M). 
gen3_case H H1 H3 N.
(* 3 *) 
 gen3_case H H1  H3 n.
unfold_op; eapply2 nf_compound.
unfold_op; eapply2 nf_compound.
(* 1 *) 
gen3_case H1 H H3 (occurs 0 t). 
gen3_case H1 H H3 t0. gen3_case H1 H H3 n. 
unfold_op; eapply2 nf_compound.
unfold_op; eapply2 nf_compound.
gen3_case H1 H H3 (occurs 0 t1). 
gen3_case H1 H H3 (occurs 0 t2). 
unfold_op; eapply2 nf_compound.
Qed. 


Lemma star_opt_closed: forall M, maxvar M = 0 -> star_opt M = App k_op M. 
Proof.
intros. 
assert(occurs 0 M = 0). 
induction M; simpl in *; split_all. omega. 
max_out. rewrite IHM1; auto; rewrite IHM2; auto. 
rewrite star_opt_occurs_false. rewrite subst_rec_closed; auto. omega. auto. 
Qed. 



Lemma star_opt_normal: forall M, normal M -> normal (star_opt M).
Proof.
rank_tac. 
  induction M; intros r nf.  
  (* 3 *) 
  case n; split_all; unfold_op; auto. 
  (* 2 *) 
  split_all; unfold_op; auto. 
(* 1 *) 
simpl in *. eapply2 star_opt_normal_app.  eapply2 IHM1. omega. inversion nf; auto. 
eapply2 IHM2. omega. inversion nf; auto. 
Qed. 



Lemma maxvar_lower: forall M, maxvar (subst M (Op Node)) = pred (maxvar M). 
Proof.
induction M; split_all; unfold subst, subst_rec; fold subst_rec. 
case n; split_all. 
rewrite max_pred. auto. 
Qed. 

Lemma max_swap: forall m n, max m n = max n m. 
Proof. 
induction m; split_all.  rewrite max_zero; auto.
case n; split_all.
Qed.  

Lemma maxvar_star: forall M, maxvar (star M) = pred (maxvar M). 
Proof. 
induction M; split_all. 
(* 2 *) 
case n; split_all.
(* 1 *)  
rewrite IHM1; rewrite IHM2.
rewrite max_pred. rewrite max_swap.  omega.
Qed. 


Lemma maxvar_star_opt: forall M, maxvar (star_opt M) = pred (maxvar M). 
Proof. 
induction M; split_all. 
(* 2 *) 
case n; split_all.
(* 1 *)  
rewrite max_pred. 
case (occurs 0 M1); split_all.
(* 2 *)  
all: cycle 1.
rewrite IHM1; rewrite IHM2. 
rewrite max_swap. auto. 
(* 1 *)  
gen_case IHM2 M2. 
gen_case IHM2 n. rewrite max_zero. 
eapply2 maxvar_lower. 
replace (subst_rec M1 (Op Node) 0) with 
(subst M1 (Op Node)) by (unfold subst; auto). 
rewrite maxvar_lower. auto. 
replace (subst_rec M1 (Op Node) 0) with (subst M1 (Op Node
)) by (unfold subst; auto). 
rewrite maxvar_lower. rewrite ! max_zero.  auto.
(* 1 *)  
gen_case IHM2 (occurs 0 t).
(* 2 *)  
all: cycle 1.
rewrite IHM2. rewrite IHM1. rewrite max_swap. auto. 
(* 1 *) 
gen_case IHM2 t0. gen_case IHM2 n. 
rewrite IHM1; rewrite IHM2; auto. 
rewrite max_swap; auto. 
replace (subst_rec M1 (Op Node) 0) with (subst M1 (Op Node)) by (unfold subst; auto). 
rewrite maxvar_lower. 
replace (subst_rec t (Op Node) 0) with (subst t (Op Node)) by (unfold subst; auto). 
rewrite maxvar_lower. rewrite max_pred; auto. 
replace (subst_rec M1 (Op Node) 0) with (subst M1 (Op Node)) by (unfold subst; auto). 
rewrite maxvar_lower. 
replace (subst_rec t (Op Node) 0) with (subst t (Op Node)) by (unfold subst; auto). 
rewrite maxvar_lower. rewrite max_pred; auto. 
(* 1 *) 
gen_case IHM2 (occurs 0 t1).
all: cycle 1.
rewrite IHM2. rewrite IHM1. rewrite max_swap. auto. 
gen_case IHM2 (occurs 0 t2).
all: cycle 1. 
gen_case IHM2 t2. 
(* 4 *) 
gen_case IHM2 n.  
rewrite IHM1. rewrite IHM2.  rewrite max_swap. auto.
rewrite IHM1. rewrite IHM2. rewrite max_swap; auto. 
(* 3 *) 
rewrite IHM1. rewrite IHM2. rewrite max_swap; auto.
(* 2 *) 
rewrite IHM1. rewrite IHM2. rewrite max_swap; auto.
(* 1 *) 
replace (subst_rec M1 (Op Node) 0) with (subst M1 (Op Node)) by (unfold subst; auto). 
rewrite maxvar_lower. 
replace (subst_rec t (Op Node) 0) with (subst t (Op Node)) by (unfold subst; auto). 
rewrite maxvar_lower.
replace (subst_rec t1 (Op Node) 0) with (subst t1 (Op Node)) by (unfold subst; auto). 
rewrite maxvar_lower.
replace (subst_rec t2 (Op Node) 0) with (subst t2 (Op Node)) by (unfold subst; auto). 
rewrite maxvar_lower.
rewrite ! max_pred. simpl. auto.
Qed. 


     
Lemma lift_rec_preserves_star: 
forall M n k, lift_rec (star M) n k = star (lift_rec M (S n) k). 
Proof. 
rank_tac. 
induction p; intros. assert(rank M >0) by eapply2 rank_positive. noway. 
induction M; split_all. 
(* 2 *) 
case n0; split_all. rewrite relocate_succ. auto. 
(* 1 *) 
simpl in *; rewrite IHM1; try omega. rewrite IHM2; try omega. auto. 
Qed. 
      
Lemma lift_rec_preserves_star_opt: 
forall M n k, lift_rec (star_opt M) n k = star_opt (lift_rec M (S n) k). 
Proof. 
rank_tac. 
induction p; intros. assert(rank M >0) by eapply2 rank_positive. noway. 
induction M; split_all. 
(* 2 *) 
case n0; split_all. rewrite relocate_succ. auto. 
(* 1 *) 
rewrite ! occurs_lift_rec_succ. 
case (occurs 0 M1); split_all. 
all: cycle 1.
rewrite IHM1. rewrite IHM2. auto.  simpl in *; omega. simpl in * ; omega. 
(* 1 *) 
rewrite <- IHM1. rewrite <- IHM2. 
unfold subst, subst_rec; fold subst_rec. 
replace n with (0+n) by auto. unfold plus. 
gen2_case H IHM2 M2. 
(* 5 *) 
gen_case IHM2 n0. 
(* 6 *) 
unfold subst.  replace n with (0+n) by omega.
 rewrite lift_rec_subst_rec. auto. 
(* 5 *) 
rewrite relocate_succ. 
unfold subst.  replace n with (0+n) by omega.
 rewrite lift_rec_subst_rec. auto. 
(* 4 *) 
unfold subst.  replace n with (0+n) by omega.
 rewrite lift_rec_subst_rec. auto. 
(* 3 *) 
rewrite ! occurs_lift_rec_succ in *; auto. 
gen_case IHM2 (occurs 0 t0). 
gen_case IHM2 (occurs 0 t). 
all: cycle 1.
replace (occurs 0 t + S n0) with (S (occurs 0 t + n0)) by omega. 
case (occurs 0 t). 
(* 5 *) 
unfold lift_rec; fold lift_rec.  auto. 
unfold lift_rec; fold lift_rec.  auto. 
simpl in *. omega.
simpl in *. omega.
(* 1 *) 
unfold_op; unfold lift_rec; fold lift_rec. 
replace n with (0+n) by auto; 
rewrite ! lift_rec_subst_rec ; try omega. auto. 
Qed. 


Lemma subst_rec_preserves_star_opt: 
forall M N k, subst_rec (star_opt M) N k = star_opt (subst_rec M N (S k)). 
Proof. 
  induction M; split_all.
  (* 2 *)
  case n; split_all.
  unfold insert_Ref. elim(compare k n0); split_all.
elim a; split_all.    elim(compare (S k) (S n0)); split_all; try noway.
elim a1; split_all; try noway.
replace n0 with (S (pred n0)) by omega. auto.
elim(compare (S k) (S n0)); split_all; try noway.
elim a0; split_all; try noway.
unfold lift. 
replace (lift_rec N 0 (S k)) with (lift 1 (lift_rec N 0 k)).
rewrite star_opt_lift. auto. 
unfold lift. rewrite lift_rec_lift_rec; try omega.  auto.
elim(compare (S k) (S n0)); split_all; try noway.
elim a; split_all; try noway.
(* 1 *) 
rewrite <- ! IHM2. 
rewrite ! occurs_subst_rec_succ. 
rewrite <- IHM1. 
case (occurs 0 M1); split_all.
case M2; split_all. case n; split_all. 
(* 4 *) 
unfold subst. replace k with (0+k) by auto.
rewrite subst_rec_subst_rec. auto.
(* 3 *)  
unfold insert_Ref. 
elim(compare k n0); intro. elim a; intro.
elim(compare (S k) (S n0)); split_all; try noway. elim a1; split_all; try noway. 
replace n0 with (S (pred n0)) by omega.  
unfold subst. replace k with (0+k) by auto. rewrite ! subst_rec_subst_rec. simpl. insert_Ref_out. 
auto. 
subst. elim(compare (S n0) (S n0)); intro; try noway. elim a0; intro; try noway. 
case N; unfold lift, lift_rec; fold lift_rec; split_all. relocate_lt. 
replace (S n0 + n1) with (S (n0 + n1)) by omega.  
unfold subst. replace n0 with (0+n0) by auto. rewrite ! subst_rec_subst_rec. simpl. insert_Ref_out. 
auto. 
unfold subst. replace n0 with (0+n0) by auto. rewrite ! subst_rec_subst_rec. simpl. insert_Ref_out. 
auto. 
unfold subst. replace n0 with (0+n0) by auto. rewrite ! subst_rec_subst_rec. simpl. 
rewrite ! subst_rec_lift_rec; try omega. auto. 
elim(compare (S k) (S n0)); split_all; try noway. elim a; split_all; try noway. 
unfold subst. replace k with (0+k) by auto. rewrite ! subst_rec_subst_rec. simpl. insert_Ref_out. 
auto. 
unfold subst. replace k with (0+k) by auto. rewrite ! subst_rec_subst_rec. simpl. insert_Ref_out. 
auto. 
(* 1 *) 
case (occurs 0 t); split_all. 
case (occurs 0 t0); split_all. 
unfold subst. replace k with (0+k) by auto. rewrite ! subst_rec_subst_rec. simpl. auto.  
Qed. 



Proposition star_opt_beta: forall M N, sf_red (App (star_opt M) N) (subst M N).
Proof.
cut(forall p M, p>= rank M -> forall N, sf_red (App (star_opt M) N) (subst M N)). 
split_all. eapply2 H. 
induction p; split_all. 
assert(rank M >0) by eapply2 rank_positive. noway. 
induction M; intros. 
(* 3 *) 
unfold subst; case n; split_all; unfold_op;  eapply2 succ_red.
insert_Ref_out. unfold lift. rewrite lift_rec_null_term. 
eval_tac. eval_tac. 
(* 2 *) 
unfold subst, subst_rec; unfold star_opt; unfold_op;  eapply2 succ_red.
(* 1 *)
simpl in H. 
unfold star_opt; fold star_opt. 
assert(occurs 0 M1 = 0 -> subst_rec M1 N 0 = subst_rec M1 (Op Node) 0) by eapply2 no_subst. 
gen_case H0 (occurs 0 M1).
all: cycle 1. 
eapply succ_red.  eapply2 s_red. 
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply2 IHM1. omega. 
eapply2 IHM2. omega.
unfold subst; auto.  
(* 1 *) 
gen2_case H IHM2 M2. gen2_case H IHM2 n. 
unfold subst, subst_rec; fold subst_rec. insert_Ref_out. unfold lift. rewrite lift_rec_null; auto.
rewrite H0;  auto. 
(* 3 *) 
eval_tac. insert_Ref_out. eapply2 preserves_app_sf_red. rewrite H0; auto. 
(* 2 *) 
eval_tac. eapply2 preserves_app_sf_red. rewrite H0; auto. 
(* 1 *) 
assert(occurs 0 t = 0 -> subst_rec t N 0 = subst_rec t (Op Node) 0) by eapply2 no_subst. 
gen2_case H1 IHM2 (occurs 0 t).
all: cycle 1. 
eapply succ_red. eapply2 s_red. 
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply2 IHM1. omega. 
eapply2 IHM2. omega.
unfold subst; auto.  
(* 1 *) 
assert(occurs 0 t0 = 0 -> subst_rec t0 N 0 = subst_rec t0 (Op Node) 0) by eapply2 no_subst. 
gen3_case H2 H IHM2 t0. gen3_case H H2 IHM2 n. 
(* 4 *)
all: cycle 2.
eval_tac. insert_Ref_out. simpl.  rewrite H1; auto. rewrite H0; auto. 
(* 3 *)
all: cycle 1.
eapply succ_red. eapply2 s_red. 
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply2 IHM1. omega.  
eapply2 IHM2. omega.
unfold subst; auto.  
(* 2 *) 
eval_tac. eapply2 preserves_app_sf_red. rewrite H0; auto. rewrite H1; auto. 
(* 1 *) 
assert(occurs 0 t1 = 0 -> subst_rec t1 N 0 = subst_rec t1 (Op Node) 0) by eapply2 no_subst. 
assert(occurs 0 t2 = 0 -> subst_rec t2 N 0 = subst_rec t2 (Op Node) 0) by eapply2 no_subst. 
gen2_case IHM2 H3 (occurs 0 t1).
all: cycle 1. 
eapply succ_red. eapply2 s_red. 
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply2 IHM1. omega.  
eapply2 IHM2. omega.
unfold subst; auto.  
(* 1 *) 
gen2_case IHM2 H4 (occurs 0 t2).
all: cycle 1.
eapply succ_red. eapply2 s_red. 
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply2 IHM1. omega.  
eapply2 IHM2. omega.
unfold subst; auto.  
(* 1 *) 
eval_tac. rewrite H0; auto. 
rewrite H1; auto. rewrite H3; auto. rewrite H4; auto. 
Qed. 



Lemma star_opt_beta2:
  forall M N1 N2, sf_red (App (App (star_opt (star_opt M)) N1) N2) (subst (subst M (lift 1 N2)) N1).
Proof.
  intros.
eapply transitive_red. eapply preserves_app_sf_red. 
eapply2 star_opt_beta. auto. 
match goal with
    |- multi_step sf_red1 (App (subst ?P ?Q) N2) _  =>
    replace(App (subst P Q) N2) with (subst (App P (lift 1 N2)) Q)
end
.
eapply2 subst_preserves_sf_red.
eapply transitive_red. eapply2 star_opt_beta. auto. 
unfold subst, lift; split_all. repeat rewrite subst_rec_lift_rec; try omega.
rewrite lift_rec_null. auto.
Qed.


Lemma star_opt_beta3:
  forall M N1 N2 N3, sf_red (App (App (App (star_opt (star_opt (star_opt M))) N1) N2) N3)
                           (subst (subst (subst M (lift 2 N3)) (lift 1 N2)) N1).
Proof.
  intros.
eapply transitive_red. eapply preserves_app_sf_red. 
eapply2 star_opt_beta2. auto. 
match goal with
    |- multi_step sf_red1 (App (subst (subst ?P ?Q) ?R) N3) _  =>
    replace(App (subst (subst P Q) R) N3) with (subst (subst (App P (lift 2 N3)) Q) R)
end
.
eapply2 subst_preserves_sf_red.
eapply2 subst_preserves_sf_red.
eapply transitive_red. eapply2 star_opt_beta. auto. 
unfold subst, lift; split_all. repeat rewrite subst_rec_lift_rec; try omega.
rewrite lift_rec_null. auto.
Qed.

Lemma star_opt_beta4:
  forall M N1 N2 N3 N4, 
sf_red (App (App (App (App (star_opt (star_opt (star_opt (star_opt M)))) N1) N2) N3) N4)
                           (subst (subst (subst (subst M (lift 3 N4))(lift 2 N3)) (lift 1 N2)) N1).
Proof.
  intros.
eapply transitive_red. eapply preserves_app_sf_red. eapply2 star_opt_beta3. auto. 
match goal with
    |- multi_step sf_red1 (App (subst (subst (subst ?P ?Q) ?R) ?T) N4) _  =>
    replace(App (subst(subst (subst P Q) R) T) N4) 
    with (subst (subst (subst (App P (lift 3 N4)) Q) R) T)
end
.
eapply2 subst_preserves_sf_red.
eapply2 subst_preserves_sf_red.
eapply2 subst_preserves_sf_red.
eapply transitive_red. eapply2 star_opt_beta. auto. 
unfold subst, lift; split_all. repeat rewrite subst_rec_lift_rec; try omega.
rewrite lift_rec_null. auto.
Qed.



Lemma app_preserves_active: forall M N, status M = Active -> status (App M N) = Active.
Proof.
induction M; intros. auto. auto. 
gen2_case IHM1 H M1.
gen2_case IHM1 H t. 
discriminate. 
Qed. 
 
 

Inductive bind_normal : Tree -> Prop := 
| bn_normal : forall M, normal M -> bind_normal M
| bn_app : forall M N, bind_normal M -> bind_normal N ->  maxvar (App M N) > 0 -> bind_normal (App M N)
.

Hint Constructors bind_normal. 

Lemma bind_normal_stem: forall M, bind_normal M -> bind_normal (App (Op Node) M). 
Proof. 
intros. inversion H; subst. 
(* 2 *) 
eapply2 bn_normal. 
(* 1 *) 
eapply2 bn_app. 
Qed. 

Lemma bind_normal_fork: forall M N, bind_normal M -> bind_normal N -> bind_normal (App (App (Op Node) M) N). 
Proof. 
intros. inversion H; subst. inversion H0; subst. 
(* 3 *) 
eapply2 bn_normal.
(* 2 *) 
eapply2 bn_app. rewrite maxvar_app. 
match goal with 
| |- ?m >0 => assert (m >= maxvar (App M0 N0)) by eapply2 max_is_max 
end. 
omega. 
(* 1 *)   
eapply2 bn_app.
rewrite maxvar_app. 
match goal with 
| |- ?m >0 => assert (m >= maxvar (App (Op Node) (App M0 N0))) by eapply2 max_is_max 
end.
rewrite ! maxvar_app in *. 
simpl. 
match goal with 
| |- ?m >0 => assert (m >= (Nat.max (maxvar M0) (maxvar N0)) ) by eapply2 max_is_max 
end.
omega. 

Qed. 

Fixpoint size P := 
match P with 
| App M N => size M + size N 
| _ => 1
end.

Lemma size_positive: forall M, size M >0.
Proof. induction M; split_all. omega. Qed. 



Lemma aux: forall m M, m > size M -> occurs 0 M = 0 -> status (subst M (Op Node)) = status M. 
Proof.
induction m ; split_all. omega.  
(* 1 *) 
gen2_case H H0 M. 
gen2_case H H0 n. discriminate. 
assert(occurs 0 t = 0 /\ occurs 0 t0 = 0). omega. 
inversion H1.
unfold subst in *. rewrite IHm; auto.
all: cycle 1.
assert (size t0 >0) by eapply2 size_positive.  
omega.
(* 1 *)  
gen2_case H H2 t. 
gen2_case H H2 n. 
gen2_case H H2 t1. 
gen2_case H H2 n. 
gen2_case H H2 t3. 
gen2_case H H2 n. discriminate.  
case o; auto.
eapply2 IHm. omega.
gen_case H2 (occurs 0 t4).
discriminate. 
Qed. 
    

(* 
Lemma aux2: forall M, occurs 0 M = 0 -> normal M -> normal (subst M (Op Node)).
Proof.
induction M ; split_all. 
(* 2 *) 
gen_case H n. discriminate. 
unfold subst, subst_rec; insert_Ref_out. auto.   
(* 1 *) 
assert(status (subst (App M1 M2) (Op Node)) = status (App M1 M2)).
eapply2 aux. 
assert(occurs 0 M1 = false /\ occurs 0 M2 = false). 
gen_case H (occurs 0 M1). discriminate. 
inversion H2. 
inversion H0; subst.
apply nf_active.
eapply2 IHM1. eapply2 IHM2. 
unfold subst, subst_rec in *; 
rewrite H1. auto. 
eapply2 nf_compound. 
assert(compound (subst_rec (App M1 M2) (Op Node) 0)) by eapply2 subst_rec_preserves_compounds.
simpl in *; auto. 
Qed. 
 *)


Lemma aux4: forall M, occurs 0 M = 0 -> maxvar M > 0 -> maxvar (subst_rec M (Op Node) 0) >0.
Proof. 
induction M; split_all. 
gen_case H n. discriminate. omega. 
assert(occurs 0 M1 = 0 /\ occurs 0 M2 = 0). 
gen_case H (occurs 0 M1). 
discriminate. 
inversion H1. 
assert(maxvar M1 >0 \/ maxvar M2 >0).
gen_case H0 (maxvar M1). 
left; omega. 
inversion H4.
assert(Nat.max (maxvar (subst_rec M1 (Op Node) 0))
  (maxvar (subst_rec M2 (Op Node) 0))  >= 
maxvar (subst_rec M1 (Op Node) 0) )
by eapply2 max_is_max.
assert(maxvar (subst_rec M1 (Op Node) 0) >0). 
eapply2 IHM1.   omega.
assert(Nat.max (maxvar (subst_rec M1 (Op Node) 0))
  (maxvar (subst_rec M2 (Op Node) 0))  >= 
maxvar (subst_rec M2 (Op Node) 0) )
by eapply2 max_is_max.
assert(maxvar (subst_rec M2 (Op Node) 0) >0). 
eapply2 IHM2.   omega.
Qed. 

 
Lemma aux3: forall m M, m > size M -> occurs 0 M = 0 -> bind_normal M -> bind_normal (subst M (Op Node)).
Proof.
induction m; intros. 
omega. 
gen3_case H H0 H1 M. 
(* 2 *) 
gen3_case H H0 H1 n. discriminate. cbv. eapply2 bn_normal. 
(* 1 *) 
assert(occurs 0 t = 0 /\ occurs 0 t0 = 0). 
gen_case H0 (occurs 0 t). discriminate. 
inversion H2. 
inversion H1; subst.
(* 2 *) 
eapply2 bn_normal. eapply2 occurs_false_subst_normal. 
(* 1 *) 
unfold subst, subst_rec; fold subst_rec. 
eapply2 bn_app.
eapply2 IHm. 
assert(size t0>0) by eapply2 size_positive. omega.  
eapply2 IHm. 
assert(size t>0) by eapply2 size_positive. omega.
(* 1 *) 
assert(maxvar (subst_rec (App t t0) (Op Node) 0) >0).
eapply2 aux4.
simpl in *; auto. 
Qed. 
 
 



Lemma star_opt_preserves_bind_normal: forall M, bind_normal M -> bind_normal (star_opt M). 
Proof. 
induction M; intros.
(* 3 *) 
cbv; auto. case n; auto. 
(* 2 *) 
cbv; auto. 
(* 1 *) 
assert(bind_normal (star_opt M1)). 
inversion H; subst; auto. 
inversion H0; eapply2 bn_normal; eapply2 star_opt_normal. 
(* 1 *) 
assert(bind_normal (star_opt M2)). 
inversion H; subst; auto. 
inversion H1; eapply2 bn_normal; eapply2 star_opt_normal.
(* 1 *) 
inversion H; subst. 
eapply2 bn_normal. 
eapply2 star_opt_normal.
(* 1 *)   
unfold star_opt; fold star_opt. 
assert(occurs 0 M1 >0 \/ occurs 0 M1 = 0) by omega .
inversion H2.
replace (occurs 0 M1) with (S (pred (occurs 0 M1))) by omega.
(* 2 *) 
eapply2 bind_normal_fork.
eapply2 bind_normal_stem.
(* 1 *) 
rewrite H3.
generalize IHM2 H H5 H6; clear IHM2 H H5 H6; case M2; intros.
(* 3 *) 
case n; split_all.
unfold subst. eapply2 aux3. 
unfold_op. eapply2 bind_normal_fork.
eapply2 aux3.  simpl; rewrite H3; auto.
eapply2 bn_app. simpl. 
assert(Nat.max (maxvar M1) (S (S n0)) >= S (S n0)) by eapply2 max_is_max. omega.
(* 2 *) 
simpl.
unfold_op. eapply2 bind_normal_fork.
eapply2 aux3.  simpl; rewrite H3; auto.
(* 1 *) 
assert(occurs 0 (App t t0) >0 \/ occurs 0 (App t t0) =0) by omega. 
inversion H7. 
(* 2 *) 
replace (occurs 0 (App t t0)) with (S (pred (occurs 0 (App t t0)))) by omega.
eapply2 bind_normal_fork.
eapply2 bind_normal_stem.  
(* 1 *) 
rewrite H8.  
unfold_op. 
eapply2 bind_normal_fork.
eapply2 aux3. 
simpl in *. rewrite H8. rewrite H3; auto. 
Qed. 
 


Fixpoint multi_star n M := 
match n with 
| 0 => M 
| S k => multi_star k (star_opt M)
end .

Lemma multi_star_plus: forall m n M, multi_star (m+n) M = multi_star m (multi_star n M).
Proof.
induction m; split_all. 
rewrite IHm. 
cut(multi_star n (star_opt M) = star_opt (multi_star n M)); auto. congruence . 
generalize M; clear.  induction n; split_all.
Qed. 
 


Lemma bind_normal_to_normal: forall M, bind_normal M -> normal (multi_star (maxvar M) M). 
Proof.
cut (forall m M, m>= maxvar M -> bind_normal M -> normal (multi_star m M)). 
intros. eapply2 H.
induction m; split_all.
inversion H0; subst. auto. omega. 
(* 1 *) 
eapply2 IHm. rewrite maxvar_star_opt. omega. 
eapply2 star_opt_preserves_bind_normal. 
Qed. 
 
 

Lemma lift_rec_preserves_bind_normal: forall M n k, bind_normal M -> bind_normal (lift_rec M n k).
Proof.
induction M; split_all.
inversion H; subst. 
eapply2 bn_normal.  
assert(normal(lift_rec (App M1 M2) n k)) by eapply2 lift_rec_preserves_normal. 
simpl in *; auto. 
eapply2 bn_app. 
simpl. 
assert(maxvar(lift_rec (App M1 M2) n k) >0) by eapply2 lift_rec_preserves_variables. 
simpl in *; auto. 
Qed.
