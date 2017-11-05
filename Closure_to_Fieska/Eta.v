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
(*                            Eta                                     *)
(*                                                                    *)
(*                          Barry Jay                                 *)
(*                                                                    *)
(**********************************************************************)


(* 
Add LoadPath ".." as IntensionalLib.
*) 

Require Import Arith Omega Max Bool List.

Require Import IntensionalLib.Closure_calculus.Closure_calculus.

Require Import IntensionalLib.Fieska_calculus.Test.
Require Import IntensionalLib.Fieska_calculus.General.
Require Import IntensionalLib.Fieska_calculus.Fieska_Terms.
Require Import IntensionalLib.Fieska_calculus.Fieska_Tactics.
Require Import IntensionalLib.Fieska_calculus.Fieska_reduction.
Require Import IntensionalLib.Fieska_calculus.Fieska_Normal.
Require Import IntensionalLib.Fieska_calculus.Fieska_Closed.
Require Import IntensionalLib.Fieska_calculus.Substitution.
Require Import IntensionalLib.Fieska_calculus.Fieska_Eval.
Require Import IntensionalLib.Fieska_calculus.Star.
Require Import IntensionalLib.Fieska_calculus.Fixpoints.
Require Import IntensionalLib.Fieska_calculus.Extensions.
Require Import IntensionalLib.Fieska_calculus.Tagging.
Require Import IntensionalLib.Fieska_calculus.Adding.
Require Import IntensionalLib.Closure_to_Fieska.Abstraction_to_Combination.


Hypothesis optimise_star2:
  forall M N, sf_red (App (lift 1 M) (Ref 0)) N -> sf_red M (star_opt N). 



Lemma optimise_eta :
  forall M N, sf_red (App (lift 1 M) (Ref 0)) (App (lift 1 N) (Ref 0))  -> sf_red M N.
Proof.
  intros. replace N with (star_opt (App (lift 1 N) (Ref 0))). 
  eapply2 optimise_star2.
  rewrite star_opt_eta. unfold lift;   subst_tac. auto. 
unfold lift. eapply2 occurs_lift_rec_zero. 
Qed.  

Lemma optimise_A: forall M N,  sf_red (App (App (Op Aop) M) N) (App M N). 
Proof. intros. eapply2 optimise_eta. unfold lift, lift_rec; fold lift_rec.  red; one_step. Qed. 


Lemma optimise_star: forall M N, sf_red M N -> sf_red (star_opt M) (star_opt N). 
Proof. 
intros. eapply2 optimise_star2. 
unfold lift. rewrite lift_rec_preserves_star_opt. 
eapply transitive_red. eapply2 star_opt_beta. 
unfold subst. apply transitive_red with M. 2: auto. 
clear. induction M; split_all. 
case n; split_all. relocate_lt. insert_Ref_out. auto. 
eapply2 preserves_app_sf_red. 
Qed. 


Lemma optimise_eta2: forall M, sf_red M (star_opt (App (lift 1 M) (Ref 0))). 
Proof. intros. eapply2 optimise_star2. Qed. 


Lemma lift_rec_preserves_var : forall M n k, lift_rec(var M) n k = var (lift_rec M n k).
Proof. 
intros; unfold var; unfold_op. unfold lift_rec; fold lift_rec. 
rewrite lift_rec_closed. auto. apply var_fix_closed. 
Qed. 

Theorem identity_abstraction_optimised: 
sf_red (lambda_to_fieska (Abs 0 nil Closure_calculus.Iop (Closure_calculus.Ref 0))) i_op. 
Proof. 
unfold lambda_to_fieska. unfold refs, abs; unfold_op. 
eapply transitive_red. eapply2 optimise_A.  eval_tac. eval_tac. eval_tac. 
eapply transitive_red. eapply2 (Y4_fix).  
unfold abs_fn. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. eapply star_opt_beta. auto. auto. auto. 
unfold subst. rewrite subst_rec_preserves_extension. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply2 extensions_by_matchfail. auto. auto. 
unfold_op; rewrite subst_rec_app. rewrite subst_rec_op.  
rewrite ! subst_rec_preserves_star_opt. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply succ_red. eapply2 k_red. auto. auto. auto. 
eapply transitive_red. eapply2 star_opt_beta2.  
unfold_op; unfold subst. rewrite ! subst_rec_preserves_star_opt. 
subst_tac. rewrite ! (subst_rec_closed add). 
2: cbv; auto. 
unfold subst_rec; fold subst_rec. insert_Ref_out. 
unfold subst_rec; fold subst_rec. insert_Ref_out. unfold lift. 
rewrite lift_rec_lift_rec; try omega. unfold plus.   
rewrite ! subst_rec_lift_rec; try omega.
rewrite lift_rec_preserves_var. 
unfold lift_rec; fold lift_rec. 
(* 1 *)
replace (Op Iop) with (star_opt (Ref 0)) by auto. 
eapply2 optimise_star2.
unfold lift. rewrite lift_rec_preserves_star_opt.
unfold lift_rec; fold lift_rec.
rewrite !  lift_rec_closed. 2: split_all. 2: split_all. 2: cbv; auto. 
relocate_lt. 
eapply transitive_red. eapply2 star_opt_beta.
unfold star_opt, subst, subst_rec; fold subst_rec.
insert_Ref_out. unfold lift; rewrite lift_rec_null.
rewrite ! subst_rec_closed.  2:split_all. 2: cbv; omega. 
eval_tac. eapply transitive_red. eapply2 add_red_var_equal. unfold program, var; split_all.
 auto. 
Qed.

(* restore 

Theorem first_projection_abstraction_optimised: 
sf_red (lambda_to_fieska (Abs 1 (0::nil) Closure_calculus.Iop (Closure_calculus.Ref 1))) k_op. 
Proof. 
unfold lambda_to_fieska. unfold abs, refs; unfold_op. 
eapply transitive_red. eapply2 optimise_A.  eval_tac.  eval_tac.   eval_tac. 
eapply transitive_red. eapply2 (Y4_fix).  
unfold abs_fn at 1. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. eapply star_opt_beta. auto. auto. auto. 
unfold subst. rewrite subst_rec_preserves_extension. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply2 extensions_by_matching. unfold_op; auto. auto. auto. 
unfold map, app, length, fold_left,  subst.  
repeat (rewrite subst_rec_preserves_star_opt at 1). 
unfold_op; unfold pattern_size; fold pattern_size. 
unfold plus; fold plus. 
unfold lift; repeat (unfold subst_rec; fold subst_rec;  insert_Ref_out). 
unfold lift. rewrite ? lift_rec_lift_rec; try omega. unfold plus; fold plus. 
rewrite ? subst_rec_lift_rec; try omega.
rewrite ? lift_rec_preserves_var; try omega.
lift_tac. repeat (rewrite lift_rec_closed; [| auto]).
eapply transitive_red. eapply2 star_opt_beta2.  
unfold_op; unfold subst. rewrite ! subst_rec_preserves_star_opt. 


--------------
unfold subst_rec; fold subst_rec. 

rewrite ! abs_preserves_subst_rec. unfold subst_rec; fold subst_rec. insert_Ref_out. 
unfold subst_rec; fold subst_rec. insert_Ref_out. unfold lift. 
rewrite lift_rec_lift_rec; try omega. rewrite ! subst_rec_lift_rec; try omega. 
rewrite ! subst_rec_closed. 2: split_all. 2: split_all. 
unfold lift_rec; fold lift_rec. rewrite ! lift_rec_preserves_var. 
unfold lift_rec; fold lift_rec. 

replace (Op Kop) with (star_opt (star_opt (Ref 1))) by auto. 
eapply2 optimise_star. 
eapply2 optimise_star2. 
unfold lift. 

rewrite abs_preserves_lift_rec. unfold lift_rec; fold lift_rec. relocate_lt. 
rewrite ! lift_rec_preserves_var. unfold plus, lift_rec; fold lift_rec. 
eapply transitive_red. eapply2 abs_red. 
eapply transitive_red. eapply2 act_red_var. 
eapply transitive_red. eapply preserves_app_sf_red. eapply2 applysub_to_var_red. auto. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red.
eapply preserves_app_sf_red.
eapply2 unequal_programs. 
unfold program; split_all. eapply2 var_normal. 
unfold program; split_all. eapply2 var_normal. 
discriminate. 
auto.  auto. auto. unfold_op; eval_tac. eval_tac. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eval_tac. eval_tac. eval_tac. 
eapply transitive_red. eapply2 act_red_var. 
eapply transitive_red. eapply preserves_app_sf_red. eapply2 applysub_to_var_red. auto. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red.
eapply preserves_app_sf_red. eapply2 equal_programs. 
unfold program; split_all. eapply2 var_normal. auto.  auto. auto. 
unfold_op; eval_tac. 
Qed. 




Theorem second_projection_abstraction_optimised: 
forall M, sf_red (lambda_to_fieska (Closure_calculus.App (Abs 1 (0::nil) Closure_calculus.Iop (Closure_calculus.Ref 0)) M)) i_op. 
Proof. 
intro. unfold lambda_to_fieska; fold lambda_to_fieska. unfold abs, refs; unfold_op. 
eval_tac. eval_tac. eval_tac. eval_tac. 
eapply transitive_red. eapply preserves_app_sf_red. eapply2 (Y4_fix).  auto. 
unfold abs_fn at 1. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. eapply preserves_app_sf_red. eapply star_opt_beta. auto. auto. auto. 
auto. unfold subst. rewrite subst_rec_preserves_extension. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply2 extensions_by_matching. unfold_op; auto. auto. auto. auto. 
unfold map, app, length, fold_left, subst, subst_rec; fold subst_rec. 
repeat (rewrite subst_rec_preserves_star_opt at 1). 
unfold_op; unfold pattern_size; fold pattern_size. 
unfold plus; fold plus. 
repeat (unfold subst_rec; fold subst_rec;  insert_Ref_out). unfold lift. 
rewrite ? lift_rec_lift_rec; try omega. unfold plus; fold plus. 
rewrite ? subst_rec_lift_rec; try omega.
rewrite ? lift_rec_preserves_var; try omega.
lift_tac. repeat (rewrite lift_rec_closed; [| auto]).

replace (App
                       (App (Op Aop)
                          (App
                             (App (Op Aop)
                                (App
                                   (App (Op Aop)
                                      (App (App (Op Aop) (Y_k 4)) abs_fn))
                                   (Op Sop)))
                             (App
                                (App (Op Sop)
                                   (App (App (Op Sop) (Ref 2)) (Ref 0)))
                                (var (Op Sop))))) (Ref 1))
with (abs (Op Sop)
                             (App
                                (App (Op Sop)
                                   (App (App (Op Sop) (Ref 2)) (Ref 0)))
                                (var (Op Sop))) (Ref 1))
by auto. 

eapply transitive_red. eapply2 star_opt_beta3.  
unfold_op; unfold subst. rewrite ! abs_preserves_subst_rec. 
unfold subst_rec; fold subst_rec. insert_Ref_out. 
unfold subst_rec; fold subst_rec. insert_Ref_out. unfold lift. 
rewrite lift_rec_lift_rec; try omega.  unfold plus; fold plus. 
rewrite ! subst_rec_lift_rec; try omega. 
unfold subst_rec; fold subst_rec. insert_Ref_out.
rewrite ! subst_rec_closed. 2: split_all. 2: split_all.  2: split_all.  2: split_all. 
unfold lift_rec; fold lift_rec. rewrite ! lift_rec_preserves_var. 
unfold lift_rec; fold lift_rec. 
rewrite lift_rec_null. 
(* 1 *) 
replace (Op Iop) with (star_opt (Ref 0)) by auto.  unfold star_opt at 1. 
eapply2 optimise_star2.
unfold lift. rewrite abs_preserves_lift_rec.
unfold lift_rec; fold lift_rec.
eapply transitive_red. eapply2 abs_red. 
rewrite lift_rec_closed. 2: split_all. 
eapply transitive_red. eapply2 act_red_var. 
eapply transitive_red. eapply preserves_app_sf_red.  eapply2 applysub_to_var_red. auto. 
eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red.  
eapply preserves_app_sf_red. 
eapply2 equal_programs. unfold program, var; split_all. auto. auto. auto. 
unfold_op; eval_tac. 
Qed.


*) 

