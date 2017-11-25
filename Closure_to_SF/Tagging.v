(**********************************************************************)
(* This Program is free software; you can redistribute it and/or      *)
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
(*                      Tagging.v                                     *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)



Require Import Arith Omega Max Bool List.
Require Import IntensionalLib.SF_calculus.General.  
Require Import IntensionalLib.SF_calculus.SF_Terms.  
Require Import IntensionalLib.SF_calculus.SF_Tactics.  
Require Import IntensionalLib.SF_calculus.SF_reduction.  
Require Import IntensionalLib.SF_calculus.SF_Normal.  
Require Import IntensionalLib.SF_calculus.SF_Closed.  
Require Import IntensionalLib.SF_calculus.Substitution.  
Require Import IntensionalLib.SF_calculus.SF_Eval.  
Require Import IntensionalLib.SF_calculus.Star.  
Require Import IntensionalLib.SF_calculus.Fixpoints.  
Require Import IntensionalLib.SF_calculus.Extensions. 



(* tagging and variables  *) 



Ltac pattern_size_out := 
unfold a_op; unfold_op; 
(* rewrite ? pattern_size_star_opt; *) 
repeat try (rewrite pattern_size_closed; [| rewrite Y_k_closed; omega]); 
unfold pattern_size; fold pattern_size;
repeat try (rewrite pattern_size_closed; [| rewrite Y_k_closed; omega]); 
 unfold plus; fold plus. 

Definition pair M N := App (App (Op Fop) M) N.

Lemma subst_rec_preserves_pair: 
forall M N P k, subst_rec (pair M N) P k = pair (subst_rec M P k) (subst_rec N P k).
Proof. unfold pair; split_all. Qed. 

Definition var_fn := 
  star_opt (star_opt (star_opt (App (Ref 2) (app_comb (App (Ref 2) (Ref 1)) (Ref 0))))).
Definition var M := app_comb (app_comb (app_comb omega3 omega3) var_fn) M. 
Definition tag M N := var (app_comb M N). 



Lemma var_red: forall M N, sf_red (App (var M) N) (tag (var M) N). 
Proof.
intros; unfold var, var_fn. 
eapply transitive_red. eapply2 app_comb_red. 
eapply transitive_red. eapply preserves_app_sf_red. eapply2 app_comb_red.  auto. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply2 app_comb_red. auto. auto. 
eapply transitive_red. eapply preserves_app_sf_red. eapply2 omega3_omega3. auto.   
eapply transitive_red. eapply2 star_opt_beta3. 
unfold subst; rewrite ! subst_rec_app. 
repeat (rewrite ! subst_rec_ref; insert_Ref_out). 
unfold lift; rewrite !lift_rec_null.
rewrite ! subst_rec_preserves_app_comb.
repeat (rewrite  subst_rec_ref; insert_Ref_out).  
unfold lift; rewrite ! lift_rec_lift_rec; try omega. unfold plus.
 rewrite ! subst_rec_lift_rec; try omega. rewrite ! lift_rec_null.
unfold Y3. eapply transitive_red. eapply2 star_opt_beta. 
unfold subst; rewrite ! subst_rec_preserves_app_comb. 
unfold lift; rewrite ! subst_rec_lift_rec; try omega. 
rewrite ! lift_rec_null. 
rewrite ! (subst_rec_closed omega3). 2: unfold omega3; cbv; auto. 
rewrite ! subst_rec_app. 
repeat (rewrite subst_rec_ref; insert_Ref_out). 
unfold lift; rewrite ! lift_rec_null. 
rewrite ! lift_rec_preserves_star_opt. 
unfold lift_rec; fold lift_rec. relocate_lt. 
rewrite ! lift_rec_preserves_app_comb. 
unfold lift_rec; fold lift_rec. relocate_lt.
rewrite subst_rec_lift_rec; try omega.
rewrite ! lift_rec_null.
 unfold tag, var, var_fn.  
eapply2 app_comb_preserves_sf_red. 
eapply2 app_comb_preserves_sf_red. 
eapply transitive_red. eapply2 star_opt_beta. 
unfold subst; rewrite ! subst_rec_preserves_app_comb.
rewrite ! (subst_rec_closed omega3). 2: cbv; auto. 
rewrite ! subst_rec_preserves_star_opt.  
unfold subst_rec; fold subst_rec.  insert_Ref_out. 
unfold lift; rewrite ! lift_rec_null. auto. 
Qed. 
 

Lemma tag_red: forall M N P, sf_red (App (tag M N) P) (tag (tag M N) P). 
Proof. intros; unfold tag. eapply transitive_red. eapply2 var_red. unfold tag; auto. Qed. 
 

Lemma pattern_size_var : forall M, pattern_size (var M) = pattern_size M. 
Proof. intros; unfold var, var_fn; unfold_op.  pattern_size_out. 
rewrite pattern_size_closed. simpl.  omega. cbv. auto.  
Qed. 

Lemma subst_rec_preserves_Y3: forall f N k, subst_rec (Y3 f) N k = Y3 (subst_rec f N k). 
Proof.
unfold Y3; intros. rewrite subst_rec_preserves_star_opt. 
rewrite ! subst_rec_preserves_app_comb. rewrite  subst_rec_ref. insert_Ref_out. 
rewrite ! (subst_rec_closed omega3). 
2: unfold omega3; cbv; omega. 
unfold lift. rewrite subst_rec_lift_rec1; try omega. auto. 
Qed. 

Lemma var_fn_program: program var_fn.
Proof.  
unfold var_fn, pair, program; intros; split. repeat eapply2 star_opt_normal.
eapply2 nf_active. nf_out. 
repeat rewrite maxvar_star_opt. cbv. auto. 
Qed.

Lemma var_normal: forall M, normal M -> normal (var M).
Proof.  
intros. unfold var. repeat apply app_comb_normal; try eapply2 omega3_program; auto. 
eapply2 var_fn_program. 
Qed.


Lemma var_maxvar: forall M, maxvar (var M) = maxvar M.
Proof.
  intros. unfold var.  
rewrite ! maxvar_app_comb. 
replace (maxvar omega3) with 0 by eapply2 omega3_program.
replace (maxvar var_fn) with 0 by eapply2 var_fn_program. auto.  
 Qed.

Hint Resolve var_fn_program. 



Lemma var_fn_pattern_normal: pattern_normal 0 var_fn. 
Proof.
unfold var_fn.  replace 0 with (pred (pred (pred 3))) by omega. 
repeat eapply2 pattern_normal_star_opt.  simpl.
repeat eapply2 pattern_normal_app_comb; eapply2 pnf_normal. 
eapply2 nf_active. nf_out; auto.  
Qed. 
