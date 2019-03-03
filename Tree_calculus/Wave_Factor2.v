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
(*                        Wave_Factor2.v                              *)
(*                                                                    *)
(*                          Barry Jay                                 *)
(*                                                                    *)
(**********************************************************************)

Require Import Arith Omega List Max.
Require Import IntensionalLib.SF_calculus.Test.  
Require Import IntensionalLib.SF_calculus.General.  
Require Import IntensionalLib.Tree_calculus.Tree_Terms.  
Require Import IntensionalLib.Tree_calculus.Tree_Tactics.  
Require Import IntensionalLib.Tree_calculus.Tree_reduction.  
Require Import IntensionalLib.Tree_calculus.Tree_Normal.  
Require Import IntensionalLib.Tree_calculus.Tree_Closed.  
Require Import IntensionalLib.Tree_calculus.Substitution.  
Require Import IntensionalLib.Tree_calculus.Tree_Eval.  
Require Import IntensionalLib.Tree_calculus.Star.  
Require Import IntensionalLib.Tree_calculus.Wave_Factor.  



 
Lemma factor_fork:
forall p q u t, 
sf_red(App (App (App Fop (App (App (Op Node) p) q)) u) t) 
    (App (App t (App (Op Node) p)) q).
Proof.
intros; unfold Fop.
eapply transitive_red.
eapply2 star_opt_beta3.  
unfold subst, subst_rec; fold subst_rec. 
rewrite ! (subst_rec_closed is_leaf). 
2: simpl; auto. 
insert_Ref_out. simpl. 
insert_Ref_out.  
unfold lift; rewrite ! lift_rec_null.
rewrite ! subst_rec_lift_rec; try omega.
rewrite ! lift_rec_null.  
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red.
eapply2 fork_test. auto. 
eval_tac. eval_tac. eval_tac. eval_tac. 
eval_tac. eval_tac. eval_tac. eval_tac. 
eapply succ_red. eapply2 f_red. 
eval_tac. eval_tac. eval_tac. eval_tac. 
eval_tac. eval_tac. eval_tac. eval_tac.
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eval_tac. all: auto.
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eval_tac. all: auto.
Qed. 


Lemma Fop_closed: maxvar Fop = 0.
Proof. 
unfold Fop.   unfold is_leaf, is_stem, is_fork, swap. 
unfold tree_test; unfold_op. 
rewrite ! maxvar_star_opt.
rewrite ! maxvar_app.
rewrite ! maxvar_star_opt.
rewrite ! maxvar_app.
cbv. auto. 
Qed. 


