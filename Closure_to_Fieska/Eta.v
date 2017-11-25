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



Add LoadPath ".." as IntensionalLib.


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
Require Import IntensionalLib.Closure_to_Fieska.Tagging.
Require Import IntensionalLib.Closure_to_Fieska.Adding.
Require Import IntensionalLib.Closure_to_Fieska.Abstraction_to_Combination.



Lemma lift_rec_preserves_components_l: 
forall M n k, lift_rec (left_component M) n k = left_component (lift_rec M n k).
Proof. induction M; split_all. Qed. 


Lemma lift_rec_preserves_components_r: 
forall M n k, lift_rec (right_component M) n k = right_component (lift_rec M n k).
Proof. induction M; split_all. Qed. 

Lemma lift_rec_preserves_sf_red1: 
forall M N, sf_red1 M N -> forall n k, sf_red1 (lift_rec M n k) (lift_rec N n k).
Proof. 
intros M N r; induction r; split_all. 
rewrite lift_rec_preserves_components_l.
rewrite lift_rec_preserves_components_r. 
eapply2 f_compound_red.  
rewrite ! lift_rec_preserves_components_l.
rewrite ! lift_rec_preserves_components_r. 
eapply2 e_compound_compound_red. Qed. 

Lemma lift_rec_multi_step: 
forall (red: Fieska -> Fieska -> Prop), 
(forall M N, red M N -> forall n k, red (lift_rec M n k) (lift_rec N n k)) -> 
(forall M N, multi_step red M N -> forall n k, multi_step red (lift_rec M n k) (lift_rec N n k)).
Proof. 
intros red H M N r; induction r; split_all.
eapply succ_red. eapply2 H. eapply2 IHr. 
Qed. 

Lemma lift_rec_preserves_sf_red: 
forall M N, sf_red M N -> forall n k, sf_red (lift_rec M n k) (lift_rec N n k).
Proof. eapply2 lift_rec_multi_step. eapply2 lift_rec_preserves_sf_red1. Qed. 
 

Lemma subst_rec_preserves_sf_red1: 
forall M N, sf_red1 M N -> forall n k, sf_red1 (subst_rec M n k) (subst_rec N n k).
Proof. 
intros M N r; induction r; split_all. 
rewrite subst_rec_preserves_components_l.
rewrite subst_rec_preserves_components_r. 
eapply2 f_compound_red.
eapply2 subst_rec_preserves_compounds.  eapply2 preserves_compound_sf_red1.   
eapply2 preserves_compound_sf_red1. 
eapply2 e_op_compound_red.  eapply2 subst_rec_preserves_compounds. 
eapply2 e_compound_op_red.  eapply2 subst_rec_preserves_compounds. 
rewrite ! subst_rec_preserves_components_l. 
rewrite ! subst_rec_preserves_components_r.
apply e_compound_compound_red.
  eapply2 subst_rec_preserves_compounds. 
  eapply2 subst_rec_preserves_compounds. 
eapply2 IHr1. eapply2 IHr2. 
eapply2 preserves_compound_sf_red1. 
eapply2 (preserves_compound_sf_red1 M). 
eapply2 preserves_compound_sf_red1. 
eapply2 (preserves_compound_sf_red1 M). 
Qed. 

Lemma subst_rec_multi_step: 
forall (red: Fieska -> Fieska -> Prop), 
(forall M N, red M N -> forall n k, red (subst_rec M n k) (subst_rec N n k)) -> 
(forall M N, multi_step red M N -> forall n k, multi_step red (subst_rec M n k) (subst_rec N n k)).
Proof. 
intros red H M N r; induction r; split_all.
eapply succ_red. eapply2 H. eapply2 IHr. 
Qed. 

Lemma subst_rec_preserves_sf_red: 
forall M N, sf_red M N -> forall n k, sf_red (subst_rec M n k) (subst_rec N n k).
Proof. eapply2 subst_rec_multi_step. eapply2 subst_rec_preserves_sf_red1. Qed. 
 



Inductive ext_equiv : Fieska -> Fieska -> Prop := 
| ext_red : forall M N, (exists P, sf_red M P /\ sf_red N P) -> ext_equiv M N 
| ext_eta : forall M N, ext_equiv (App (lift 1 M) (Ref 0)) (App (lift 1 N) (Ref 0)) -> ext_equiv M N
.

Hint Constructors ext_equiv. 

Lemma ext_equiv_reflexive: forall M, ext_equiv M M.
Proof. intro; eauto. Qed. 

Lemma ext_equiv_symmetric : forall M N, ext_equiv M N -> ext_equiv N M. 
Proof. 
intros M N e; induction e.  
inversion H. inversion H0. eapply2 ext_red.
eapply2 ext_eta.  
Qed. 

Lemma ext_equiv_transitive: forall M N, ext_equiv M N -> forall P, ext_equiv N P -> ext_equiv M P.
Proof.
intros M N e1; induction e1. 
(* 2 *) 
inversion H. inversion H0. clear H H0.  
intros P e2. generalize H1 H2; clear H1 H2. generalize x M.  clear - e2.
 induction e2; intros.   
(* 3 *) 
inversion H. inversion H0.
assert(exists Q, sf_red x Q /\ sf_red x0 Q) by eapply2 confluence_sf_red. 
inversion H5. inversion H6. 
eapply2 ext_red. exist x1; split; auto. eapply2 transitive_red. eapply2 transitive_red. 
(* 2 *) 
eapply2 ext_eta. eapply2 (IHe2 (App (lift 1 x) (Ref 0))). 
eapply2 preserves_app_sf_red. unfold lift; eapply2 lift_rec_preserves_sf_red.   
eapply2 preserves_app_sf_red. unfold lift; eapply2 lift_rec_preserves_sf_red.   
(* 1 *) 
intros P e2; induction e2.
(* 2 *) 
inversion H. inversion H0. 
eapply2 ext_eta. eapply2 IHe1. 
eapply2 ext_red. exist (App (lift 1 x) (Ref 0)). split. 
eapply2 preserves_app_sf_red. unfold lift; eapply2 lift_rec_preserves_sf_red.   
eapply2 preserves_app_sf_red. unfold lift; eapply2 lift_rec_preserves_sf_red.   
(* 1 *) 
eapply2 ext_eta.  
Qed. 


Lemma sf_red_implies_ext_equiv: forall M N, sf_red M N -> ext_equiv M N.
Proof. intros. eapply2 ext_red. Qed. 


Lemma optimise_A: forall M N,  ext_equiv (App (App (Op Aop) M) N) (App M N). 
Proof. 
intros. eapply2 ext_eta. eapply2 ext_red. exist (App (lift 1 (App M N)) (Ref 0)). 
unfold lift, lift_rec; fold lift_rec. split.  eval_tac. auto.
Qed.   

Lemma optimise_star: forall M N, sf_red M N -> ext_equiv (star_opt M) (star_opt N). 
Proof. 
intros. eapply2 ext_eta. eapply2 ext_red. 
 exist (subst (lift_rec N 1 1) (Ref 0)). split. 
unfold lift; rewrite lift_rec_preserves_star_opt. 
eapply transitive_red. eapply2 star_opt_beta. 
unfold subst; apply subst_rec_preserves_sf_red. 
eapply2 lift_rec_preserves_sf_red. 
unfold lift; rewrite lift_rec_preserves_star_opt. 
eapply2 star_opt_beta. 
Qed. 


Lemma optimise_eta2: forall M, ext_equiv M (star_opt (App (lift 1 M) (Ref 0))). 
Proof. 
intros. eapply2 ext_eta. eapply2 ext_red. 
exists (App (lift 1 M) (Ref 0)). split. auto.
unfold lift; rewrite lift_rec_preserves_star_opt. 
eapply transitive_red. eapply2 star_opt_beta. 
unfold subst, lift_rec; fold lift_rec. unfold subst_rec; fold subst_rec. 
insert_Ref_out; relocate_lt. 
rewrite lift_rec_lift_rec; try omega. unfold plus.  
rewrite subst_rec_lift_rec; try omega. 
unfold lift; rewrite lift_rec_null; auto.  
Qed. 


Lemma lift_rec_preserves_var : forall M n k, lift_rec(var M) n k = var (lift_rec M n k).
Proof. 
intros; unfold var, app_comb; unfold_op. unfold lift_rec; fold lift_rec. 
rewrite lift_rec_closed. auto. 
Qed. 

Theorem identity_abstraction_optimised: 
ext_equiv (closure_to_fieska (Abs Closure_calculus.Iop 0 (Closure_calculus.Ref 0))) i_op. 
Proof. 
unfold closure_to_fieska. 
replace i_op with (star_opt ( Ref 0)) at 2 by auto. 
eapply2 ext_eta. eapply2 ext_red. 
exist (Ref 0). split. 
unfold lift; rewrite lift_rec_closed. 2: cbv; auto. 
eapply transitive_red. eapply2 abs_red. eapply2 add_red_var_equal.
unfold_op; split; auto.   unfold app_comb. eapply2 matchfail_compound_op.
unfold_op; eapply2 matchfail_compound_op.
unfold lift, lift_rec; eval_tac. 
Qed.

(* restore 

Define polyvariate binding in closure calculus as syntactic sugar then use this here. 

To do. 

1) revise paper according to my lights
2) upload to GitHub
3) address referees comments (minor)
4) address minor comments. 

*) 

Lemma lift_rec_preserves_abs: 
forall sigma i t n k, 
lift_rec (abs sigma i t) n k = abs (lift_rec sigma n k) (lift_rec i n k) (lift_rec t n k). 
Proof. intros; cbv; auto. Qed. 


Lemma lift_rec_preserves_add: 
forall sigma n k, 
lift_rec (add sigma) n k = add (lift_rec sigma n k). 
Proof. intros; cbv; auto. Qed. 

Theorem first_projection_abstraction_optimised: 
ext_equiv (closure_to_fieska (Abs Closure_calculus.Iop 1 
 (Abs (Add Closure_calculus.Iop  1 (Closure_calculus.Ref 1)) 0 (Closure_calculus.Ref 1)))) k_op. 
Proof. 
unfold closure_to_fieska. 
eapply2 ext_eta. eapply2 ext_eta. eapply2 ext_red. 
exist (Ref 1). split. 
2: cbv; eval_tac.
unfold lift; rewrite ! lift_rec_preserves_abs.
unfold_op; rewrite ! lift_rec_app. 
rewrite ! lift_rec_preserves_abs. 
unfold lift_rec; fold lift_rec.  
rewrite ! lift_rec_preserves_add. 
rewrite ! lift_rec_preserves_var.
unfold lift_rec; fold lift_rec; relocate_lt.  
rewrite ! lift_rec_preserves_var.
unfold lift_rec; fold lift_rec; relocate_lt.  unfold plus. 
eapply transitive_red. eapply preserves_app_sf_red. 
eapply2 abs_red. auto. 
eapply transitive_red. eapply preserves_app_sf_red.
 eapply2 add_red_abs. auto. 
eapply transitive_red. eapply2 abs_red. 
eapply transitive_red. eapply2 add_red_var_unequal. 
unfold program; auto. unfold program; auto. discriminate. 
unfold app_comb. eapply2 matchfail_compound_l. 
eapply transitive_red. eapply preserves_app_sf_red.
eapply2 add_red_add. auto. 
eapply transitive_red. eapply2 add_red_var_equal.
unfold program; auto. 
unfold app_comb. eapply2 matchfail_compound_l. 
eapply2 add_red_var_equal. unfold program; auto.
unfold app_comb. eapply2 matchfail_compound_l. 
Qed. 



Theorem closure_optimized: 
forall M, 
ext_equiv (closure_to_fieska (Abs (Add Closure_calculus.Iop 1 M) 0 (Closure_calculus.Ref 0))) i_op. 
Proof. 
intro. unfold closure_to_fieska; fold closure_to_fieska.
eapply2 ext_eta. 
unfold_op; unfold lift; rewrite lift_rec_preserves_abs.  
rewrite lift_rec_preserves_add; rewrite lift_rec_preserves_var. 
unfold lift_rec; fold lift_rec. rewrite ! (lift_rec_closed (ref _)). 
2: cbv; auto. 2: cbv; auto. 
eapply2 ext_red. exist (Ref 0). split. 2: eval_tac. 
eapply transitive_red. eapply2 abs_red. unfold_op. 
eapply transitive_red. eapply2 add_red_var_equal; unfold program; auto. 
unfold app_comb; auto. auto. 
Qed. 

Theorem three_optimizations: 
ext_equiv (closure_to_fieska (Abs Closure_calculus.Iop 0 (Closure_calculus.Ref 0))) i_op /\ 
ext_equiv (closure_to_fieska (Abs Closure_calculus.Iop 1 
 (Abs (Add Closure_calculus.Iop  1 (Closure_calculus.Ref 1)) 0 (Closure_calculus.Ref 1)))) k_op /\ 
forall M, 
ext_equiv (closure_to_fieska (Abs (Add Closure_calculus.Iop 1 M) 0 (Closure_calculus.Ref 0))) i_op.
Proof. 
repeat split. eapply2 identity_abstraction_optimised. 
eapply2 first_projection_abstraction_optimised.
eapply2 closure_optimized. 
Qed. 


