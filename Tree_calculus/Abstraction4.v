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
(* 021101301 USA                                                     *)
(**********************************************************************)

(**********************************************************************)
(*                 Abstraction_to_Tree.v                              *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)


Require Import Omega Max Bool List.
Require Import IntensionalLib.SF_calculus.Test.  
Require Import IntensionalLib.SF_calculus.General.  
Require Import IntensionalLib.Tree_calculus.Abstraction_Terms.  
Require Import IntensionalLib.Tree_calculus.Abstraction_Reduction.  
Require Import IntensionalLib.Tree_calculus.Tree_Terms.  
Require Import IntensionalLib.Tree_calculus.Tree_Tactics.  
Require Import IntensionalLib.Tree_calculus.Tree_reduction.  
Require Import IntensionalLib.Tree_calculus.Tree_Normal.  
Require Import IntensionalLib.Tree_calculus.Tree_Closed.  
Require Import IntensionalLib.Tree_calculus.Substitution.  
Require Import IntensionalLib.Tree_calculus.Tree_Eval.  
Require Import IntensionalLib.Tree_calculus.Star.  
Require Import IntensionalLib.Tree_calculus.Wait.  
Require Import IntensionalLib.Tree_calculus.Fixpoints.  
Require Import IntensionalLib.Tree_calculus.Wave_Factor.  
Require Import IntensionalLib.Tree_calculus.Wave_Factor2.  
Require Import IntensionalLib.Tree_calculus.Equal.  
Require Import IntensionalLib.Tree_calculus.Case.  
Require Import IntensionalLib.Tree_calculus.Extensions.  
Require Import IntensionalLib.Tree_calculus.Wait2.  
Require Import IntensionalLib.Tree_calculus.Abstraction.  
Require Import IntensionalLib.Tree_calculus.Abstraction2.  
Require Import IntensionalLib.Tree_calculus.Abstraction3. 

 
Lemma b_r_op_red: forall M N, sf_red (App (App (App b_op M) N) r_op) r_op.
Proof.
intros; unfold b_op. 
eapply transitive_red. 
eapply preserves_app_sf_red.
eapply preserves_app_sf_red.
eapply2 app_comb_red. all: auto. 
eapply transitive_red.    
eapply2 Y2_fix.
unfold b_fn at 1. 
eapply transitive_red.
eapply preserves_app_sf_red. 
eapply2 star_opt_beta3. auto. 
unfold subst.
rewrite ! subst_rec_preserves_extension.
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_r.
eapply2 matchfail_program. 
eapply2 h_fn_program.
split. eapply2 omega_k_normal. eapply2 omega_k_closed. 
eapply2 h_fn_not_omega.
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
eapply matchfail_program. 
split. apply app_comb_normal.
apply omega_k_normal. 
apply omega_k_normal. 
rewrite maxvar_app_comb. rewrite ! omega_k_closed. auto.
split. apply A_k_normal. apply A_k_closed.
discriminate. 
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
unfold r_op, Y_k. 
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
eapply2 program_matching.
split. eapply2 omega_k_normal. eapply2 omega_k_closed.
eapply2 matchfail_program. 
split. eapply2 omega_k_normal. eapply2 omega_k_closed.
split. eapply2 A_k_normal. eapply2 A_k_closed.
discriminate.
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
unfold r_op, Y_k. 
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_r.
eapply2 matchfail_program. 
split. eapply2 omega_k_normal. eapply2 omega_k_closed.
split. eapply2 omega_k_normal. eapply2 omega_k_closed.
replace 1 with (S (0+0)) by omega.
apply omega_k_mono. 
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail. 
unfold r_op, Y_k. 
eapply2 matchfail_app_comb_r.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_compound_l. 
simpl. 
unfold_op; eapply2 matchfail_compound_r. 
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail. 
unfold r_op, ab1. 
eapply2 matchfail_compound_l.
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_l.
unfold_op. 
eapply2 matchfail_compound_r.
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail. 
unfold r_op. 
eapply2 matchfail_app_comb_r.
eapply2 matchfail_app_comb_l.
unfold compose, star_opt, occurs, eqnat. 
unfold_op. 
eapply2 matchfail_compound_l.
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
simpl. 
eapply2 matchfail_compound_l.
(* 1 *) 
unfold_op; simpl. repeat eval_tac. 
Qed. 

