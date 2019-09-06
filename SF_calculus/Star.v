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
Require Import IntensionalLib.SF_calculus.SF_Terms.  
Require Import IntensionalLib.SF_calculus.SF_Tactics.  
Require Import IntensionalLib.SF_calculus.SF_reduction.  
Require Import IntensionalLib.SF_calculus.SF_Normal.  
Require Import IntensionalLib.SF_calculus.SF_Closed.  
Require Import IntensionalLib.SF_calculus.Substitution.  
Require Import IntensionalLib.SF_calculus.SF_Eval.  


(* naive abstraction -- no optimisation *) 

Fixpoint star M := 
match M with 
  | Ref 0 => i_op
| Ref (S n) => App  k_op  (Ref n)
| Op o => App k_op (Op o)
| App M1 M2 => App (App (Op Sop) (star M1)) (star M2)
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


(* optimising star *) 

Fixpoint occurs0 M := 
match M with 
| Ref 0 => true 
| Ref (S _) => false 
| Op _ => false
| App M1 M2 => (occurs0 M1) || (occurs0 M2)
end. 



Lemma occurs_op: forall o, occurs0 (Op o) = false. 
Proof. split_all. Qed. 

Lemma occurs_app: forall M N, occurs0 (App M N) = occurs0 M || occurs0 N. 
Proof. split_all. Qed. 

Lemma occurs_closed: forall M, maxvar M = 0 -> occurs0 M = false.
Proof.
induction M; split_all. omega. 
max_out. rewrite IHM1; auto; rewrite IHM2; auto. 
Qed. 

Lemma occurs_lift_rec_zero: forall M k, occurs0 (lift_rec M 0 (S k)) = false.
Proof. 
induction M; split_all. relocate_lt. 
replace (S k + n) with (S (k+n)) by omega. auto. 
rewrite IHM1; rewrite IHM2; auto. 
Qed. 

Lemma occurs_lift_rec_succ: forall M n k, occurs0 (lift_rec M (S n) k) = occurs0 M. 
Proof. 
induction M; split_all. unfold relocate. 
elim(test (S n0) n); split_all. 
gen_case a n;try noway. replace (k + S n1) with (S (k+n1)) by omega. auto. 
rewrite IHM1; rewrite IHM2; auto. 
Qed. 


Lemma occurs_subst_rec_succ: forall M N k, occurs0 (subst_rec M N (S k)) = occurs0 M.
Proof. 
induction M; split_all. case n; split_all. 
unfold insert_Ref. elim(compare (S k) (S n0)); split_all. elim a; split_all. 
gen_case a0 n0; try omega. 
unfold lift; eapply2 occurs_lift_rec_zero.
rewrite IHM1; rewrite IHM2; auto. 
Qed. 


Lemma occurs_false_subst_status: 
forall M N, occurs0 M = false -> status (subst_rec M N 0) = status M.
Proof.
cut(forall p M, p>= rank M -> 
 forall N, occurs0 M = false -> status (subst_rec M N 0) = status M). 
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
simpl in H0. simpl in H. discriminate. split_all.  
assert(occurs0 M1 = false /\ occurs0 M2 = false) by eapply2 orb_false_iff. 
inversion H1. 
generalize IHM1 H H2; clear IHM1 H H2; case M1; intros. 
(* 3 *) 
simpl in H2. unfold subst_rec; fold subst_rec.  unfold insert_Ref. 
gen_case H2 n. discriminate. 
(* 2 *) 
gen_case H o. 
(* 1 *) 
generalize IHM1 H H2; clear IHM1 H H2; case s; intros. 
(* 3 *) 
simpl in H2. unfold subst_rec; fold subst_rec.  unfold insert_Ref. 
gen_case H2 n. discriminate. 

(* 2 *) 
simpl in H2.  unfold subst_rec; fold subst_rec.  
case o; split_all. 
(* 1 *)
unfold subst_rec; fold subst_rec.
generalize IHM1 H H2; clear IHM1 H H2; case s1; intros. 
(* 3 *) 
simpl in H2. unfold subst_rec; fold subst_rec.  unfold insert_Ref. 
gen_case H2 n. 
(* 2 *) 
simpl in H2.  unfold subst_rec; fold subst_rec.  discriminate. 
case o; split_all. 
rewrite ! IHp; auto. simpl in H; omega. 
assert(occurs0 s2 = false /\ occurs0 s0 = false) by eapply2 orb_false_iff. 
split_all. 
inversion H4; auto. 
(* 1 *) 
unfold subst_rec; fold subst_rec. 
replace (status (App (App (App (App s3 s4) s2) s0) M2)) with (status (App (App (App s3 s4) s2) s0))
by auto. 
replace (status (App
        (App
           (App (App (subst_rec s3 N 0) (subst_rec s4 N 0))
              (subst_rec s2 N 0)) (subst_rec s0 N 0)) 
        (subst_rec M2 N 0))) 
with
(status (App
           (App (App (subst_rec s3 N 0) (subst_rec s4 N 0))
              (subst_rec s2 N 0)) (subst_rec s0 N 0)) 
        )
by auto. 
replace (App
           (App (App (subst_rec s3 N 0) (subst_rec s4 N 0))
              (subst_rec s2 N 0)) (subst_rec s0 N 0)) 
with (subst_rec (App (App (App s3 s4) s2) s0) N 0) by auto. 
rewrite  IHp; auto. simpl in *; omega. 
Qed. 



Lemma occurs_false_subst_normal: 
forall M N, occurs0 M = false -> normal M -> normal (subst_rec M N 0). 
Proof.
induction M; split_all. 
unfold insert_Ref. generalize H; clear H. case n; split_all.  discriminate. 
assert(occurs0 M1 = false /\ occurs0 M2 = false) by eapply2 orb_false_iff. 
inversion H1. 
inversion H0. eapply2 nf_active. 
replace(App (subst_rec M1 N 0) (subst_rec M2 N 0)) with (subst_rec (App M1 M2) N 0) by auto. 
rewrite occurs_false_subst_status. auto. split_all.
apply nf_compound. eapply2 IHM1. eapply2 IHM2. 
replace(App (subst_rec M1 N 0) (subst_rec M2 N 0)) with (subst_rec (App M1 M2) N 0) by auto. 
eapply2 subst_rec_preserves_compounds. 
Qed.

Lemma no_subst: forall M N P, occurs0 M = false -> subst_rec M N 0 = subst_rec M P 0. 
Proof. 
induction M; split_all. 
gen_case H n. discriminate. 
assert(occurs0 M1 = false /\ occurs0 M2 = false). rewrite <- orb_false_iff. auto. 
split_all. inversion H0. rewrite (IHM1 N P); auto; rewrite (IHM2 N P); auto. 
Qed. 

(* Star abstraction optimised *) 

Fixpoint star_opt M := 
match M with 
| Ref 0 => i_op 
| Ref (S n) => App k_op (Ref n)
| Op o => App k_op (Op o)
| App M1 M2 =>
  if occurs0 M1 
  then App (App (Op Sop) (star_opt M1)) (star_opt M2)
  else match M2 with 
         | Ref 0 => subst M1 (Op Sop)
         | _ => if occurs0 M2 
                then App (App (Op Sop)  (star_opt M1))  (star_opt M2) 
                else App k_op (subst M (Op Sop)) 
       end
end. 


  (* characterising star_opt  *) 

Lemma star_opt_eta: forall M, occurs0 M = false -> star_opt (App M (Ref 0)) = subst M (Op Sop). 
Proof. intros. unfold star_opt; fold star_opt. rewrite H. split_all. Qed. 

Lemma star_opt_occurs_false : 
forall M, occurs0 M = false  -> star_opt M = App k_op (subst_rec M (Op Sop) 0). 
Proof.
induction M; unfold star_opt; fold star_opt; split_all. gen_case H n; split_all. 
discriminate. 
assert(occurs0 M1 = false /\ occurs0 M2 = false) by eapply2 orb_false_iff. 
split_all. inversion H0. rewrite H1. rewrite H2. gen_case H2 M2. gen_case H2 n.
discriminate.  
Qed.

Lemma star_opt_occurs_true : 
forall M1 M2, occurs0 (App M1 M2) = true -> M2 <> Ref 0 -> 
star_opt (App M1 M2) = App (App (Op Sop) (star_opt M1)) (star_opt M2). 
Proof.
cut(forall M, occurs0 M = true -> forall M1 M2, M = App M1 M2  -> M2 <> Ref 0 -> 
star_opt M = App (App (Op Sop) (star_opt M1)) (star_opt M2)). 
intros. eapply2 H. 
(* 1 *)
induction M; intros; subst; inversion H0; subst. 
simpl in H. assert(occurs0 M0 = true \/ occurs0 M3 = true) by eapply2 orb_true_iff. 
inversion H2. 
(* 2 *) 
split_all. rewrite H3. auto. 
(* 1 *) 
split_all. 
assert(occurs0 M0 = true \/ occurs0 M0 <> true) by decide equality.
assert(occurs0 M0 = false -> star_opt M0 = App k_op (subst M0 (Op Sop)))
by eapply2 star_opt_occurs_false. 
inversion H4. rewrite H6. auto. 
gen2_case H5 H6 (occurs0 M0). rewrite H3. 
gen_case H1 M3. gen_case H1 n; rewrite H5; auto. 
assert False by eapply2 H1. noway. 
Qed. 


Lemma star_opt_lift: forall M, star_opt (lift 1 M) = App k_op M. 
Proof. 
split_all. 
assert(M = subst_rec (lift 1 M) (Op Sop) 0). 
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
assert(occurs0 M = false -> normal (subst M (Op Sop))). 
intro; eapply2 occurs_false_subst_normal. inversion H; auto. 
assert(occurs0 M || occurs0 N = false -> normal (subst (App M N) (Op Sop))). 
intro; eapply2 occurs_false_subst_normal. 
gen2_case H2 H3 (occurs0 M). 
gen3_case H H1 H3 N.
(* 3 *) 
 gen3_case H H1  H3 n.
unfold_op; eapply2 nf_compound.
unfold_op; eapply2 nf_compound.
(* 1 *) 
gen3_case H1 H H3 (occurs0 s). 
gen3_case H1 H H3 s0. gen3_case H1 H H3 n. 
unfold_op; eapply2 nf_compound.
unfold_op; eapply2 nf_compound.
gen3_case H1 H H3 (occurs0 s1). 
gen3_case H1 H H3 (occurs0 s2). 
unfold_op; eapply2 nf_compound.
Qed. 

Lemma star_opt_closed: forall M, maxvar M = 0 -> star_opt M = App k_op M. 
Proof.
intros. 
assert(occurs0 M = false). 
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



Lemma maxvar_lower: forall M, maxvar (subst M (Op Sop)) = pred (maxvar M). 
Proof.
induction M; split_all; unfold subst, subst_rec; fold subst_rec. 
case n; split_all. 
rewrite max_pred. auto. 
Qed. 

Lemma maxvar_star_opt: forall M, maxvar (star_opt M) = pred (maxvar M). 
Proof. 
induction M; split_all. 
case n; split_all. 
rewrite max_pred. 
case (occurs0 M1); split_all. 
gen_case IHM2 M2. 
gen_case IHM2 n. rewrite max_zero. apply maxvar_lower. 
replace (subst_rec M1 (Op Sop) 0) with (subst M1 (Op Sop)) by (unfold subst; auto). 
rewrite maxvar_lower. auto. 
replace (subst_rec M1 (Op Sop) 0) with (subst M1 (Op Sop)) by (unfold subst; auto). 
rewrite maxvar_lower. auto. 
gen_case IHM2 (occurs0 s). 
gen_case IHM2 s0. gen_case IHM2 n. 
replace (subst_rec M1 (Op Sop) 0) with (subst M1 (Op Sop)) by (unfold subst; auto). 
rewrite maxvar_lower. 
replace (subst_rec s (Op Sop) 0) with (subst s (Op Sop)) by (unfold subst; auto). 
rewrite maxvar_lower. rewrite max_pred; auto. 
replace (subst_rec M1 (Op Sop) 0) with (subst M1 (Op Sop)) by (unfold subst; auto). 
rewrite maxvar_lower. 
replace (subst_rec s (Op Sop) 0) with (subst s (Op Sop)) by (unfold subst; auto). 
rewrite maxvar_lower. rewrite max_pred; auto. 
(* 1 *) 
gen_case IHM2 (occurs0 s1). 
gen_case IHM2 (occurs0 s2). 
replace (subst_rec M1 (Op Sop) 0) with (subst M1 (Op Sop)) by (unfold subst; auto). 
rewrite maxvar_lower. 
replace (subst_rec s1 (Op Sop) 0) with (subst s1 (Op Sop)) by (unfold subst; auto). 
rewrite maxvar_lower. rewrite max_pred; auto. 
replace (subst_rec s2 (Op Sop) 0) with (subst s2 (Op Sop)) by (unfold subst; auto). 
rewrite maxvar_lower. 
replace (subst_rec s (Op Sop) 0) with (subst s (Op Sop)) by (unfold subst; auto). 
rewrite maxvar_lower. rewrite max_pred; auto. 
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
case (occurs0 M1); split_all. 
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
gen_case IHM2 (occurs0 s0). 
gen_case IHM2 (occurs0 s). 
rewrite orb_false_r. 
case (occurs0 s). 
3: simpl in *; omega. 3: simpl in *; omega. 
(* 2 *) 
unfold lift_rec; fold lift_rec. 
 auto. 
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
case (occurs0 M1); split_all.
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
case (occurs0 s); split_all. 
case (occurs0 s0); split_all. 
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
assert(occurs0 M1 = false -> subst_rec M1 N 0 = subst_rec M1 (Op Sop) 0) by eapply2 no_subst. 
gen_case H0 (occurs0 M1). 
eval_tac. 
eapply2 preserves_app_sf_red. 
eapply2 IHM1. omega. 
eapply2 IHM2. omega. 
(* 1 *) 
gen2_case H IHM2 M2. gen2_case H IHM2 n. 
unfold subst, subst_rec; fold subst_rec. insert_Ref_out. unfold lift. rewrite lift_rec_null; auto.
rewrite H0;  auto. 
(* 3 *) 
eval_tac. subst_tac. eapply2 preserves_app_sf_red. rewrite H0; auto. 
(* 2 *) 
eval_tac. subst_tac. eapply2 preserves_app_sf_red. rewrite H0; auto. 
(* 1 *) 
assert(occurs0 s = false -> subst_rec s N 0 = subst_rec s (Op Sop) 0) by eapply2 no_subst. 
gen2_case H1 IHM2 (occurs0 s). eval_tac. 
eapply transitive_red. eapply preserves_app_sf_red. eapply2 IHM1. omega. 
 eval_tac. 
unfold subst. eapply2 preserves_app_sf_red. 
eapply transitive_red. eapply preserves_app_sf_red. eapply2 IHp. omega. eapply2 IHp. omega. 
auto. 
(* 1 *) 
assert(occurs0 s0 = false -> subst_rec s0 N 0 = subst_rec s0 (Op Sop) 0) by eapply2 no_subst. 
gen3_case H2 H IHM2 s0. gen3_case H H2 IHM2 n. 
(* 4 *) 
 eval_tac. insert_Ref_out. unfold lift. rewrite lift_rec_null. eapply2 preserves_app_sf_red. 
unfold subst in *. eapply2 IHM1. omega. rewrite H1; auto. 
(* 3 *) 
eval_tac. subst_tac.  rewrite H1; auto. rewrite H0; auto. 
(* 2 *) 
eval_tac. subst_tac. eapply2 preserves_app_sf_red. rewrite H0; auto. rewrite H1; auto. 
(* 1 *) 
assert(occurs0 s1 = false -> subst_rec s1 N 0 = subst_rec s1 (Op Sop) 0) by eapply2 no_subst. 
assert(occurs0 s2 = false -> subst_rec s2 N 0 = subst_rec s2 (Op Sop) 0) by eapply2 no_subst. 
gen2_case IHM2 H3 (occurs0 s1).  eval_tac. eapply2 preserves_app_sf_red. 
unfold subst in *; eapply2 IHM1. omega. 
eval_tac. eapply2 preserves_app_sf_red. unfold subst in *; eapply2 IHp. omega. 
eval_tac. eapply2 preserves_app_sf_red. unfold subst in *; eapply2 IHp. omega. 
unfold subst in *; eapply2 IHp. omega. 
(* 1 *) 
gen2_case IHM2 H4 (occurs0 s2).  eval_tac. eapply2 preserves_app_sf_red. 
unfold subst in *; eapply2 IHM1. omega.
unfold subst in *. eapply2 IHM2. omega. 
eval_tac. subst_tac.   eapply2 preserves_app_sf_red. rewrite H0; auto. 
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




