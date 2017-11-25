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
intros; unfold var, var_fn, app_comb. eval_tac. eval_tac. eval_tac. 
eapply transitive_red. eapply preserves_app_sf_red. eapply2 omega3_omega3. auto.  
eval_tac. eval_tac. eval_tac. eval_tac. eval_tac. eval_tac. eval_tac. eval_tac.  
unfold Y3, app_comb. eapply transitive_red. eapply2 star_opt_beta. 
unfold subst, subst_rec; fold subst_rec.  
rewrite ! (subst_rec_closed omega3). 2: unfold omega3; cbv; auto.
unfold lift; rewrite ! subst_rec_lift_rec; try omega. 
rewrite ! lift_rec_null.  insert_Ref_out. 
unfold lift, lift_rec; fold lift_rec. 
unfold lift; rewrite ! lift_rec_null. 
 unfold tag, var, var_fn, app_comb.  
eapply2 preserves_app_sf_red. eval_tac. eval_tac.  
Qed. 
 

Lemma tag_red: forall M N P, sf_red (App (tag M N) P) (tag (tag M N) P). 
Proof. intros; unfold tag. eapply transitive_red. eapply2 var_red. unfold tag; auto. Qed. 
 

Lemma pattern_size_var : forall M, pattern_size (var M) = pattern_size M. 
Proof. intros; unfold var, var_fn, app_comb; unfold_op.  pattern_size_out. 
rewrite pattern_size_closed. simpl.  omega. cbv. auto.  
Qed. 

Lemma subst_rec_preserves_Y3: forall f N k, subst_rec (Y3 f) N k = Y3 (subst_rec f N k). 
Proof.
unfold Y3, app_comb; intros. rewrite subst_rec_preserves_star_opt. 
unfold subst_rec; fold subst_rec. rewrite ! (subst_rec_closed omega3). 
2: unfold omega3; cbv; omega. insert_Ref_out. 
unfold lift. rewrite subst_rec_lift_rec1; try omega. auto. 
Qed. 

Lemma var_fn_program: program var_fn.
Proof.  
unfold var_fn, pair, program, app_comb; intros; split. repeat eapply2 star_opt_normal.
repeat rewrite maxvar_star_opt. cbv. auto. 
Qed.

Lemma var_normal: forall M, normal M -> normal (var M).
Proof.  
intros. unfold var, app_comb. nf_out; try eapply2 omega3_program; auto. 
eapply2 var_fn_program. 
Qed.


Lemma var_maxvar: forall M, maxvar (var M) = maxvar M.
Proof.
  intros. unfold var, app_comb.  simpl. auto.  
 Qed.

Hint Resolve var_fn_program. 


(* delete ? 
Lemma var_fn_pattern_normal: pattern_normal 0 var_fn. 
Proof.
unfold var_fn.  replace 0 with (pred (pred (pred 3))) by omega. 
repeat eapply2 pattern_normal_star_opt.  simpl.
repeat eapply2 pattern_normal_app_comb; eapply2 pnf_normal. 
eapply2 nf_active. nf_out; auto.  
Qed. 

*) 