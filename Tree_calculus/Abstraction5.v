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
Require Import IntensionalLib.Tree_calculus.occurs. 



Lemma b_h_op_red: forall M N, sf_red (App (App (App b_op M) N) h_op) h_op.
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
eapply2 matchfail_program.
split. apply app_comb_normal. eapply2 omega_k_normal. eapply2 omega_k_normal.
rewrite maxvar_app_comb. rewrite ! omega_k_closed. auto.
split. eapply2 A_k_normal. eapply2 A_k_closed.
discriminate. 
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_r.
eapply2 matchfail_program.
split. eapply2 omega_k_normal. eapply2 omega_k_closed.
split. eapply2 omega_k_normal. eapply2 omega_k_closed.
replace 4 with (S (3 +0)) by auto. 
replace 2 with (S (0+1)) by omega.
eapply2 omega_k_mono. 
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_r.
eapply2 matchfail_program. 
split. eapply2 omega_k_normal. eapply2 omega_k_closed.
split. eapply2 omega_k_normal. eapply2 omega_k_closed.
replace 2 with (S(1+0)) by auto.
eapply2 omega_k_mono.  
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
eapply2 matchfail_app_comb_r.
unfold h_fn.
rewrite star_opt_eta. 
2: simpl; auto.
unfold subst, subst_rec. insert_Ref_out. unfold pred.   
rewrite star_opt_occurs_true. 
2: simpl; auto. 2: discriminate. 
rewrite star_opt_eta.  2: auto. 
rewrite star_opt_occurs_true. 
2: simpl; auto. 2: discriminate.
unfold subst, subst_rec; insert_Ref_out. unfold pred.
rewrite star_opt_occurs_true. 
2: simpl; auto. 2: discriminate. 
eapply2 matchfail_compound_l.
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
apply matchfail_program. 
unfold_op; split; auto.
cbv; split; auto.
repeat eapply2 nf_compound.
discriminate.
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail. 
unfold h_op, ab1. 
eapply2 matchfail_compound_l.
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_l.
unfold_op. 
eapply2 matchfail_compound_r.
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail. 
unfold h_op. 
eapply2 matchfail_app_comb_r.
unfold h_fn. 
rewrite star_opt_eta. 2: cbv; auto. repeat subst_tac.
eapply2 matchfail_compound_l. simpl. unfold_op. subst_tac. 
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_l.
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_op. 
right; auto. 
discriminate . 
(* 1 *) 
unfold_op; simpl. eval_tac. eval_tac.   
Qed. 



Lemma app_comb_vs_abs_op: forall M N, 
matchfail
  (app_comb M N) abs_op.
Proof. 
intros.
unfold abs_op, ab_op, app_comb2.
unfold app_comb at 2.
rewrite star_opt_occurs_true. 
all: cycle 1. 
unfold flip, app_comb; unfold_op. 
rewrite ! occurs_app.
replace (occurs 0 (Ref 0)) with 1 by auto. omega. 
discriminate. 
(* 1 *) 
rewrite star_opt_occurs_true.
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. 
unfold_op; auto. eapply2 matchfail_compound_r. 
unfold_op; auto. 
unfold_op; auto. 
unfold flip; rewrite ! occurs_app. 
assert(occurs 0
     (star_opt
        (App
           (App (Op Node)
              (App (Op Node)
                 (App k_op (app_comb (app_comb (A_k 1) (ab_fn b_op)) (Ref 1)))))
           (App k_op (App (App node (App node (App k_op (Ref 0)))) i_op)))) =1).
all: cycle 1. rewrite H; omega. 
discriminate.
(* 1 *) 
rewrite (star_opt_occurs_true) at 1.
all: cycle 1. 
rewrite ! occurs_app.
replace (occurs 0 (Ref 0)) with 1 by auto. omega. 
discriminate.
rewrite ! occurs_app. 
assert(occurs 0
    (star_opt
       (App (Op Node)
            (App (Op Node) (App k_op (app_comb (app_comb (A_k 1) (ab_fn b_op)) (Ref 1)))))) = 1).
2: rewrite H; cbv; omega. 
rewrite (star_opt_occurs_false).
all: cycle 1. 
unfold app_comb; unfold_op. rewrite ! occurs_app.
rewrite (occurs_closed 0 (A_k 1)). 
2: apply A_k_closed.
rewrite (occurs_closed 0 (ab_fn b_op)).
cbv; auto. apply ab_fn_program. apply b_op_program.
subst_tac. rewrite ! subst_rec_preserves_app_comb.
rewrite subst_rec_closed. 2: rewrite A_k_closed; omega.
rewrite subst_rec_closed.
rewrite occurs_app. subst_tac. 
unfold app_comb. rewrite ! occurs_app. 
replace (occurs 0 (Ref 0)) with 1 by auto.
rewrite (occurs_closed 0 (ab_fn b_op)).
cbv; auto. apply ab_fn_program. apply b_op_program.
cut(maxvar (ab_fn b_op) = 0). intros; omega. 
apply ab_fn_program. apply b_op_program.
Qed.

Lemma b_abs_op_red: forall M N, sf_red (App (App (App b_op M) N) abs_op) abs_op.
Proof.
intros; unfold b_op. 
eapply transitive_red. 
eapply preserves_app_sf_red.
eapply preserves_app_sf_red.
eapply2 app_comb_red. auto. auto.  
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
eapply2 app_comb_vs_abs_op. 
(* 1 *) 
eapply transitive_red. 
apply extensions_by_matchfail.  
eapply2 app_comb_vs_abs_op.
(* 1 *)  
eapply transitive_red. 
apply extensions_by_matchfail.  
eapply2 app_comb_vs_abs_op.
(* 1 *)  
eapply transitive_red. 
apply extensions_by_matchfail.  
eapply2 app_comb_vs_abs_op.
eapply transitive_red. 
apply extensions_by_matchfail.  
eapply2 app_comb_vs_abs_op.
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail. 
unfold abs_op, ab_op. 
unfold app_comb2, flip.
unfold app_comb at 1. 
(* 2 *) 
rewrite star_opt_occurs_true.
all: cycle 1. 
unfold_op. 
rewrite ! occurs_app.
replace (occurs 0 (Ref 0)) with 1 by auto. omega. 
discriminate. 
(* 2 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail. 
unfold abs_op, ab_op. 
unfold app_comb2, flip.
unfold app_comb at 5. 
(* 3 *) 
rewrite star_opt_occurs_true.
all: cycle 1. 
unfold_op. 
rewrite ! occurs_app.
replace (occurs 0 (Ref 0)) with 1 by auto; omega. 
discriminate. 
(* 1 *) 
all: cycle -1. 
rewrite star_opt_occurs_true. 
all: cycle 1. 
unfold_op. 
rewrite ! occurs_app.
rewrite occurs_star_opt.
rewrite ! occurs_app. 
replace (occurs 1 (Ref 1)) with 1 by auto. omega. 
discriminate.
(* 1 *) 
all: cycle -1. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l.
unfold_op; auto.
unfold_op; auto.   
eapply2 matchfail_compound_r.
(* 2 *) 
all: cycle -1. 
rewrite (star_opt_occurs_true (App (Op Node)
                       (App (Op Node)
                          (App k_op
                             (app_comb (app_comb (A_k 1) (ab_fn b_op))
                                (Ref 1)))))) at 1.
all: cycle 1. 
unfold_op. 
rewrite ! occurs_app.
replace (occurs 0 (Ref 0)) with 1 by auto. omega. 
discriminate. 
(* 2 *) 
all: cycle -1.
unfold_op.
rewrite star_opt_occurs_true. 
all: cycle 1. 
unfold_op. 
rewrite ! occurs_app.
rewrite ! occurs_star_opt. 
rewrite ! occurs_app.
replace (occurs 1 (Ref 1)) with 1  by auto. omega. 
discriminate. 
all: cycle -1 . 
(* 2 *)  
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l.
unfold_op; auto.
eapply2 matchfail_compound_r.
unfold_op; auto. 
unfold_op. 
eapply2 matchfail_compound_op.
(* 1 *)  
unfold_op; simpl. 
eapply succ_red. eapply2 s_red. 
eapply succ_red. eapply k_red.
auto. 
auto.
Qed. 

Lemma b_i_op_red: forall M N, sf_red (App (App (App b_op M) N) i_op) i_op.
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
eapply2 app_comb_vs_I. 
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
eapply2 app_comb_vs_I. 
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
eapply2 app_comb_vs_I. 
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
eapply2 app_comb_vs_I. 
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
eapply2 app_comb_vs_I. 
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
unfold ab1.  unfold_op. 
eapply2 matchfail_compound_l. 
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
unfold_op; eapply2 matchfail_compound_l. 
(* 1 *) 
unfold_op; simpl. repeat eval_tac. 
Qed. 

Lemma occur_ref: forall n k, occurs k (Ref n) = eqnat n k. 
Proof. auto. Qed.  

Lemma b_b_op_red: forall M N, sf_red (App (App (App b_op M) N) b_op) b_op.
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
apply matchfail_program.
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
eapply2 app_comb_program. 
split. eapply2 omega_k_normal. eapply2 omega_k_closed. 
split. eapply2 omega_k_normal. eapply2 omega_k_closed. 
split. eapply2 A_k_normal. eapply2 A_k_closed.
discriminate.   
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_r.
eapply matchfail_program. 
split. eapply2 omega_k_normal. eapply2 omega_k_closed. 
split. eapply2 omega_k_normal. eapply2 omega_k_closed. 
replace 2 with (S (0+1)) by auto. 
apply omega_k_mono.
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_r.
eapply matchfail_program. 
split. eapply2 omega_k_normal. eapply2 omega_k_closed. 
split. eapply2 omega_k_normal. eapply2 omega_k_closed. 
replace 2 with (S (1+0)) by auto. 
apply omega_k_mono.
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
eapply2 matchfail_app_comb_r.
(* 2 *) 
unfold b_fn.
unfold extension at 1. 
rewrite star_opt_occurs_true.
all: cycle 1.
unfold_op. 
rewrite ! occurs_app.
rewrite ! occurs_extension.  
rewrite ! occurs_app.
rewrite ! occurs_op.
rewrite pattern_size_ab1. 
rewrite pattern_size_app_comb2.
rewrite ! pattern_size_app. 
rewrite ! pattern_size_op. 
rewrite ! pattern_size_ref.
rewrite ! pattern_size_closed.
all: cycle 1. 
rewrite omega_k_closed. auto. 
rewrite Y_k_closed. omega.  
rewrite A_k_closed. omega.
cbv; auto. 
eapply2 omega_k_closed.
discriminate. 
all: cycle -1.
unfold plus.
rewrite ! occur_ref; unfold eqnat.
omega.
(* 2 *)
eapply transitive_red. 
eapply2 extensions_by_matchfail.
(* 3 *) 
unfold ab1. unfold_op. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
(* 2 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
eapply2 matchfail_app_comb_r.
unfold b_fn.
(* 3 *) 
unfold extension at 1. 
rewrite star_opt_occurs_true. 
rewrite star_opt_occurs_true. 
rewrite star_opt_occurs_true.
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r.
rewrite star_opt_occurs_true. 
rewrite star_opt_occurs_true.
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
unfold_op; auto. 
eapply2 matchfail_compound_r.
unfold_op; auto. 
eapply2 matchfail_op.
right; auto. simpl; auto. 
unfold_op; auto. 
discriminate. 
(* 12 *) 
rewrite ! occurs_app. 
rewrite occurs_star_opt.
rewrite ! occurs_app. 
rewrite occurs_star_opt. 
rewrite occurs_case. 
rewrite ! pattern_size_app_comb.
rewrite ! pattern_size_ref.
rewrite ! pattern_size_closed. 
cbv; auto. 
eapply2 omega_k_closed.
cbv; auto. 
discriminate. 
(* 10 *) 
rewrite ! occurs_app. 
rewrite occurs_star_opt.
rewrite occurs_case. 
rewrite ! pattern_size_app_comb.
rewrite ! pattern_size_ref.
rewrite ! pattern_size_closed. 
cbv; auto. 
eapply2 omega_k_closed.
cbv; auto. 
discriminate.
(* 8 *) 
rewrite ! occurs_app. 
rewrite ! occurs_star_opt.
rewrite ! occurs_app.
rewrite ! occurs_extension.  
rewrite occurs_star_opt. 
rewrite pattern_size_ab1. 
rewrite pattern_size_app_comb2. 
rewrite ! pattern_size_app_comb.
rewrite ! pattern_size_ref.
rewrite ! pattern_size_closed.
unfold app_comb; unfold_op. 
rewrite ! occurs_app.
rewrite ! occurs_op.
rewrite ! occur_ref.
unfold plus, eqnat.
omega. 
eapply2 omega_k_closed. 
eapply2 Y_k_closed. 
eapply2 A_k_closed. 
cbv; auto.
eapply2 omega_k_closed. 
(* 7 *) 
rewrite star_opt_occurs_true. 
discriminate. 
rewrite ! occurs_app.
rewrite occurs_star_opt. 
rewrite occurs_case. 
rewrite ! pattern_size_app_comb. 
rewrite ! pattern_size_ref.
rewrite ! pattern_size_closed.
cbv. auto. 
eapply2 omega_k_closed.
cbv; auto. 
discriminate.
(* 6 *) 
rewrite ! occurs_app. 
rewrite occurs_star_opt. 
rewrite occurs_case.
rewrite ! pattern_size_app_comb. 
rewrite ! pattern_size_ref.
rewrite ! pattern_size_closed.
rewrite ! occurs_app.
unfold occurs at 4. unfold eqnat, plus; fold plus.  omega. 
eapply2 omega_k_closed.
cbv; auto.
(* 5 *) 
rewrite star_opt_occurs_true. 
discriminate. 
rewrite ! occurs_app.
rewrite ! occurs_extension.
rewrite ! pattern_size_ab1. 
rewrite ! pattern_size_app_comb2.  
rewrite ! pattern_size_app_comb. 
rewrite ! pattern_size_ref.
rewrite ! pattern_size_closed.
rewrite ! occurs_app.
unfold plus; fold plus.
replace (occurs 2 (Ref 2)) with 1 by auto.
unfold_op; unfold occurs; fold occurs. 
unfold eqnat, plus; fold plus. omega.
eapply2 omega_k_closed. 
eapply2 Y_k_closed.
eapply2 A_k_closed. 
cbv; auto. 
eapply2 omega_k_closed. 
discriminate . 
(* 4 *) 
rewrite ! occurs_app.
rewrite ! occurs_extension.
rewrite ! pattern_size_ab1. 
rewrite ! pattern_size_app_comb2.  
rewrite ! pattern_size_app_comb. 
rewrite ! pattern_size_ref.
rewrite ! pattern_size_closed.
unfold plus; fold plus. 
rewrite ! occurs_app.
replace (occurs 2 (Ref 2)) with 1 by auto.
rewrite ! occur_ref.
unfold eqnat. 
unfold plus; fold plus.
omega.
eapply2 omega_k_closed. 
eapply2 Y_k_closed.
eapply2 A_k_closed. 
cbv; auto. 
eapply2 omega_k_closed. 
discriminate . 
(* 2 *)
subst_tac. eval_tac. eval_tac. 
(* 1 *) 
rewrite star_opt_occurs_true. 
rewrite star_opt_occurs_true. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r.
unfold_op. 
rewrite star_opt_occurs_true. 
rewrite star_opt_occurs_true. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r.
eapply2 matchfail_op. 
right; cbv; auto. 
cbv; discriminate. 
(* 9 *) 
rewrite ! occurs_app.
rewrite ! occurs_star_opt.
rewrite ! occurs_app. 
rewrite ! occurs_star_opt. 
rewrite ! occurs_case. 
rewrite ! pattern_size_app. 
rewrite ! pattern_size_ref.
rewrite ! pattern_size_op. 
rewrite ! pattern_size_closed.
cbv. auto. 
eapply2 omega_k_closed.
cbv; auto.
cbv; discriminate . 
(* 7 *)   
rewrite ! occurs_app.
rewrite ! occurs_star_opt.
rewrite ! occurs_case. 
rewrite ! pattern_size_app. 
rewrite ! pattern_size_ref.
rewrite ! pattern_size_op. 
rewrite ! pattern_size_closed.
cbv. auto. 
eapply2 omega_k_closed.
cbv; auto.
discriminate .
(* 5 *) 
rewrite ! occurs_app.
rewrite ! occurs_star_opt.
rewrite ! occurs_app. 
rewrite ! occurs_extension. 
rewrite ! pattern_size_ab1. 
rewrite ! pattern_size_app_comb2. 
rewrite ! pattern_size_app_comb. 
rewrite ! pattern_size_ref.
rewrite ! pattern_size_closed.
unfold app_comb; unfold_op. 
rewrite ! occurs_app.
unfold plus.
rewrite ! occurs_op.
rewrite ! occur_ref; unfold eqnat. omega. 
eapply2 omega_k_closed. 
eapply2 Y_k_closed.
eapply2 A_k_closed. 
cbv; auto. 
eapply2 omega_k_closed.
(* 4 *) 
rewrite star_opt_occurs_true .
discriminate. 
rewrite ! occurs_app.
rewrite ! occurs_star_opt.
rewrite ! occurs_case. 
rewrite ! pattern_size_app_comb. 
rewrite ! pattern_size_ref.
rewrite ! pattern_size_closed.
cbv; auto. 
eapply2 omega_k_closed. 
cbv; auto. 
discriminate.
(* 3 *) 
rewrite ! occurs_app.
rewrite ! occurs_star_opt.
rewrite ! occurs_case. 
rewrite ! pattern_size_app_comb. 
rewrite ! pattern_size_ref.
rewrite ! pattern_size_closed.
unfold plus. fold plus.
rewrite ! occurs_app.
rewrite! occur_ref. unfold eqnat.
rewrite ! occurs_op. unfold plus. 
omega. 
eapply2 omega_k_closed. 
cbv; auto.
(* 2 *)  
rewrite star_opt_occurs_true .
discriminate. 
rewrite ! occurs_app.
rewrite ! occurs_extension.
rewrite ! pattern_size_ab1. 
rewrite ! pattern_size_app_comb2. 
rewrite ! pattern_size_app_comb. 
rewrite ! pattern_size_ref.
rewrite ! pattern_size_closed.
unfold app_comb; unfold_op. 
rewrite ! occurs_app.
rewrite ! occurs_op.
rewrite ! occur_ref. unfold eqnat, plus . omega.
eapply2 omega_k_closed. 
eapply2 Y_k_closed.
eapply2 A_k_closed. 
cbv; auto. 
eapply2 omega_k_closed.
discriminate . 
Qed. 


Lemma subst_rec_preserves_sf_red1:
forall M N P k, sf_red1 M N -> sf_red1 (subst_rec M P k) (subst_rec N P k).
Proof. intros.  induction H; simpl; auto. Qed. 

Lemma  subst_rec_preserves_multi_step: 
forall (red: Tree -> Tree -> Prop), 
(forall  M N P k, red M N -> red (subst_rec M P k) (subst_rec N P k)) -> 
forall M N P k, multi_step red M N -> multi_step red  (subst_rec M P k) (subst_rec N P k).
Proof.
intros.  induction H0; auto.
eapply succ_red. eapply2 H. eapply2 IHmulti_step. 
Qed. 
   

Lemma  subst_rec_preserves_sf_red:
forall M N, sf_red M N -> forall P k, sf_red (subst_rec M P k) (subst_rec N P k).
Proof. intros. eapply2 subst_rec_preserves_multi_step. eapply2 subst_rec_preserves_sf_red1. Qed.
 

Lemma subst_rec_preserves_ab_op: 
forall M N k, subst_rec (ab_op M) N k = ab_op (subst_rec M N (S (S k))).
Proof.
intros. unfold ab_op. 
rewrite ! subst_rec_preserves_star_opt.
rewrite ! subst_rec_preserves_app_comb2.
rewrite ! subst_rec_preserves_app_comb.
rewrite subst_rec_closed. 
2: rewrite A_k_closed; omega. 
rewrite ! subst_rec_ref. insert_Ref_out.
auto. 
Qed. 
 

Lemma b_a1_red: 
forall M N P, sf_red (App (App (App b_op M) N) (App abs_op P)) 
                     (App (App (App (App b_op M) N) abs_op) (App (App (App b_op M) N) P)).
Proof.
intros; unfold b_op. 
eapply transitive_red. 
eapply preserves_app_sf_red.
eapply preserves_app_sf_red.
eapply2 app_comb_red. auto.
unfold abs_op. apply a1_aux.
rewrite maxvar_ab_fn. rewrite b_op_closed. auto.  
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
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r.
unfold_op. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
eapply2 matchfail_op.
right. auto. discriminate .
(* 1 *) 
eapply transitive_red.
eapply2 extensions_by_matchfail.
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r.
unfold_op. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
eapply2 matchfail_op.
right. auto. discriminate .
(* 1 *) 
eapply transitive_red.
eapply2 extensions_by_matchfail.
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r.
unfold_op. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
eapply2 matchfail_op.
right. auto. discriminate .
(* 1 *) 
eapply transitive_red.
eapply2 extensions_by_matchfail.
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r.
unfold_op. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
eapply2 matchfail_op.
right. auto. discriminate .
(* 1 *) 
eapply transitive_red.
eapply2 extensions_by_matchfail.
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r.
unfold_op. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
eapply2 matchfail_op.
right. auto. discriminate .
(* 1 *) 
eapply transitive_red.
eapply2 extensions_by_matching.
unfold ab1. unfold_op. 
eapply2 match_app.  
eapply2 match_app.  
eapply2 match_app.  
eapply2 match_app.  
eapply2 match_app.  
eapply2 match_app.  
eapply2 match_app.
eapply2 program_matching.
split; auto.
repeat eapply2 nf_compound. 
repeat eapply2 match_app.
(* 3 *)   
eapply2 match_app.  
eapply2 match_app.  
eapply2 match_app.  
eapply2 match_app.  
eapply2 match_app.  
repeat eapply2 match_app.  
eapply2 match_app.
repeat eapply2 match_app. 
eapply2 match_app.  
eapply2 match_app.  
repeat eapply2 match_app.  
eapply2 match_app.  
eapply2 match_app.  
eapply2 match_app.
eapply2 program_matching. 
split; auto. 
eapply2 program_matching. 
split; auto. 
eapply2 star_opt_normal.
repeat eapply2 nf_compound. 
(* 1 *) 
unfold length; fold length. 
rewrite ! map_lift0.
rewrite ! app_nil_r. 
unfold map. rewrite ! app_nil_l. 
rewrite ! subst_rec_app.
rewrite ! subst_rec_preserves_ab_op.
rewrite ! pattern_size_ab1. 
rewrite ! pattern_size_ref.
rewrite ! subst_rec_ref. insert_Ref_out. 
rewrite ! subst_rec_ref. insert_Ref_out. 
rewrite ! subst_rec_ref. insert_Ref_out. 
unfold plus, lift.
rewrite ! lift_rec_lift_rec; try omega. unfold plus.   
rewrite ! subst_rec_lift_rec; try omega.
unfold app, fold_left.
unfold subst. 
rewrite ! subst_rec_app.
rewrite ! subst_rec_preserves_ab_op. 
rewrite ! subst_rec_ref. insert_Ref_out. 
rewrite ! subst_rec_ref. insert_Ref_out. 
rewrite ! subst_rec_lift_rec; try omega.
unfold lift; rewrite ! lift_rec_null.
rewrite lift_rec_lift_rec; try omega. unfold plus.  
rewrite ! subst_rec_lift_rec; try omega.
rewrite lift_rec_closed. 
unfold abs_op. auto.
rewrite maxvar_ab_fn. rewrite b_op_closed; auto. 
Qed.


Lemma b_b1_red: 
forall M N P, sf_red (App (App (App b_op M) N) (App b_op P)) 
     (App (App (App (App b_op M) N) b_op) (App (App (App b_op M) N) P)).
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
eapply preserves_app_sf_red. auto.  
unfold h_op. 
eapply transitive_red. 
eapply transitive_red. 
eapply app_comb_red.
eapply preserves_app_sf_red. 
eapply app_comb_red.  auto.
eapply transitive_red.
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply app_comb_red.  auto. auto. 
eapply transitive_red.
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
unfold A_k.
eapply2 star_opt_beta2. auto. auto. 
unfold subst. 
rewrite ! subst_rec_preserves_app_comb. 
rewrite ! subst_rec_ref. insert_Ref_out.  
rewrite ! subst_rec_ref. insert_Ref_out.  
unfold lift; rewrite ! lift_rec_null.
rewrite ! lift_rec_closed. 
2: eapply2 omega_k_closed. 
eapply transitive_red. 
eapply preserves_app_sf_red.
eapply2 app_comb_red. auto. 
rewrite (subst_rec_closed (omega_k 2)) at 1.
2: rewrite omega_k_closed; omega.
match goal with 
| |- multi_step sf_red1 (App (App (App (subst_rec (subst_rec ?M ?N1 0) ?N2 0) ?P1) ?P2) ?P3) _ => 
replace (App (App (subst_rec (subst_rec M N1 0) N2 0) P1) P2) with 
(subst_rec (subst_rec (App (App M P1) P2) N1 0) N2 0) 
end.
eapply preserves_app_sf_red. 
eapply subst_rec_preserves_sf_red.
eapply subst_rec_preserves_sf_red.
eapply2 star_opt_beta2.  auto. 
rewrite ! subst_rec_app. 
rewrite (subst_rec_closed b_fn) at 1.
rewrite (subst_rec_closed b_fn) at 1.
rewrite (subst_rec_closed (app_comb (omega_k 2) (omega_k 2))) at 1. 
rewrite (subst_rec_closed (app_comb (omega_k 2) (omega_k 2))) at 1.
auto. 
3, 4: rewrite b_fn_closed; auto. 
1,2: unfold app_comb; unfold_op;  rewrite ! maxvar_app; rewrite ! omega_k_closed; cbv; auto.
(* 1 *)      
eapply transitive_red.
eapply preserves_app_sf_red.
auto. 
unfold subst; rewrite ! subst_rec_preserves_app_comb.
rewrite (subst_rec_closed (star_opt _)) at 1. 2: cbv; auto. 
rewrite (subst_rec_closed (star_opt _)) at 1. 2: cbv; auto. 
rewrite (subst_rec_closed (star_opt _)) at 1. 2: cbv; auto. 
rewrite (subst_rec_closed (star_opt _)) at 1. 2: cbv; auto. 
rewrite subst_rec_ref at 1. insert_Ref_out. 
rewrite subst_rec_ref at 1. insert_Ref_out. 
rewrite subst_rec_ref at 1. insert_Ref_out. 
unfold lift; rewrite ! lift_rec_null. 
rewrite subst_rec_lift_rec; try omega. 
rewrite lift_rec_null. 
rewrite ! subst_rec_closed. 
2: rewrite b_fn_closed; auto. 
2: rewrite subst_rec_closed. 
2: rewrite b_fn_closed; auto. 
2: rewrite b_fn_closed; auto. 
2: rewrite maxvar_app_comb; rewrite ! omega_k_closed; auto. 
2: rewrite subst_rec_closed.  2, 3: rewrite maxvar_app_comb.
2,3: rewrite omega_k_closed; auto.
eapply transitive_red. eapply2 app_comb_red. 
eapply2 star_opt_beta2.
(* 1 *)  
eapply transitive_red. 
eapply extensions_by_matchfail.
unfold subst; rewrite ! subst_rec_preserves_app_comb.
rewrite ! subst_rec_ref. insert_Ref_out. 
rewrite ! subst_rec_ref. insert_Ref_out. 
unfold lift; rewrite ! lift_rec_null. 
rewrite subst_rec_lift_rec; try omega. 
rewrite lift_rec_null.
rewrite ! (subst_rec_closed a_op).
2: cbv; auto. 
eapply2 matchfail_app_comb_l.
eapply2 matchfail_compound_l. 
fold star_opt. 
eapply2 matchfail_compound_r.  
eapply2 matchfail_compound_r.  
unfold_op; unfold occurs. unfold plus. 
eapply2 matchfail_compound_l. 
unfold_op; auto.
unfold_op; eapply2 matchfail_compound_r.
(* 1 *)  
eapply transitive_red. 
eapply preserves_app_sf_red. auto. 
unfold subst; rewrite ! subst_rec_preserves_app_comb.
rewrite ! subst_rec_ref. insert_Ref_out. 
rewrite ! subst_rec_ref. insert_Ref_out. 
unfold lift; rewrite ! lift_rec_null. 
rewrite subst_rec_lift_rec; try omega. 
rewrite lift_rec_null.
rewrite ! (subst_rec_closed a_op).
2: cbv; auto. auto. 
(* 1 *)  
eapply transitive_red. 
eapply extensions_by_matchfail.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_compound_l. 
fold star_opt. 
eapply2 matchfail_compound_r.  
eapply2 matchfail_compound_r.  
unfold_op; unfold occurs. 
unfold plus. 
cbv. 
eapply2 matchfail_compound_l. 
(* 1 *)  
eapply transitive_red. 
eapply extensions_by_matchfail.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_compound_l. 
fold star_opt. 
eapply2 matchfail_compound_r.  
eapply2 matchfail_compound_r.  
unfold_op; unfold occurs. 
unfold plus. cbv. 
eapply2 matchfail_compound_l.
(* 1 *)  
eapply transitive_red. 
eapply extensions_by_matchfail.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_compound_l. 
fold star_opt. 
eapply2 matchfail_compound_r.  
eapply2 matchfail_compound_r.  
unfold_op; unfold occurs. 
unfold plus. 
cbv. 
eapply2 matchfail_compound_l. 
(* 1 *)  
eapply transitive_red. 
eapply extensions_by_matchfail.
eapply2 matchfail_app_comb_r.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
unfold A_k. 
unfold app_comb. unfold_op.
rewrite star_opt_occurs_true.
rewrite star_opt_occurs_true.
eapply2 matchfail_compound_l.  
eapply2 matchfail_compound_r.  
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_l.  
unfold_op; auto.
eapply2 matchfail_compound_r.  
unfold_op; auto.
unfold_op; eapply2 matchfail_op. 
right; auto.
discriminate.
rewrite! occurs_app. 
rewrite ! occurs_star_opt.
rewrite! occurs_app. 
rewrite ! occur_ref.
rewrite ! occurs_op; unfold eqnat. unfold plus; fold plus. 
omega. 
discriminate.
rewrite! occurs_app. 
rewrite ! occur_ref.
rewrite ! occurs_op; unfold eqnat. unfold plus; fold plus. 
omega. 
discriminate.
(* 1 *) 
eapply transitive_red. 
eapply extensions_by_matchfail.
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. 
unfold_op. 
eapply2 matchfail_compound_r.
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matching.
unfold app_comb; unfold_op. 
eapply2 match_app.
repeat eapply2 match_app. 
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 program_matching.
split.  eapply2 omega_k_normal. eapply2 omega_k_closed.  
eapply2 match_app.
eapply2 program_matching.
split.  eapply2 omega_k_normal. eapply2 omega_k_closed.  
eapply2 program_matching.
split.  eapply2 nf_compound.
repeat eapply2 star_opt_normal. 
repeat eapply2 nf_compound. 
cbv. auto. 
(* 1 *) 
unfold length; fold length. 
rewrite ! map_lift0.
rewrite ! app_nil_r. 
unfold map. rewrite ! app_nil_l. 
rewrite ! subst_rec_app.
rewrite ! subst_rec_preserves_app_comb.
rewrite (subst_rec_closed (A_k _)) at 1. 
rewrite (subst_rec_closed (A_k _)) at 1. 
rewrite (subst_rec_closed (A_k _)) at 1. 
rewrite (subst_rec_closed (omega_k _)) at 1. 
rewrite (subst_rec_closed (omega_k _)) at 1. 
rewrite (subst_rec_closed (omega_k _)) at 1. 
rewrite (subst_rec_closed (omega_k _)) at 1. 
rewrite (subst_rec_closed (omega_k _)) at 1. 
rewrite (subst_rec_closed (omega_k _)) at 1. 
rewrite ! pattern_size_app_comb. 
rewrite ! pattern_size_ref.
rewrite ! pattern_size_closed.
2: cbv; auto. 2: eapply2 omega_k_closed. 
all: try (rewrite omega_k_closed; omega). 
all: try (rewrite A_k_closed; omega).
(* 1 *)  
rewrite ! subst_rec_ref. insert_Ref_out. 
rewrite ! subst_rec_ref. insert_Ref_out. 
rewrite ! subst_rec_ref. insert_Ref_out. 
unfold plus, lift.
unfold app, fold_left.
unfold subst. 
rewrite ! subst_rec_app.
rewrite ! subst_rec_preserves_app_comb. 
rewrite (subst_rec_closed (A_k _)). 
rewrite (subst_rec_closed (A_k _)). 
rewrite (subst_rec_closed (omega_k _)) at 1. 
rewrite (subst_rec_closed (omega_k _)) at 1. 
rewrite (subst_rec_closed (omega_k _)) at 1. 
rewrite (subst_rec_closed (omega_k _)) at 1. 
all: try (rewrite omega_k_closed; omega).
all: try (rewrite A_k_closed; omega).
rewrite ! subst_rec_ref. insert_Ref_out. 
rewrite ! subst_rec_ref. insert_Ref_out. 
unfold lift; rewrite ! lift_rec_null.
rewrite ! lift_rec_lift_rec; try omega. unfold plus. 
rewrite ! subst_rec_lift_rec; try omega.
rewrite ! lift_rec_null. 
auto.
Qed. 



Lemma b_h1_red: 
forall M N P, sf_red (App (App (App b_op M) N) (App h_op P)) 
(App (App (App (App b_op M) N) h_op) (App (App (App b_op M) N) P)).
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
eapply preserves_app_sf_red. auto.  
unfold h_op. 
eapply transitive_red. 
eapply transitive_red. 
eapply app_comb_red.
eapply preserves_app_sf_red. 
eapply app_comb_red.  auto.
eapply transitive_red.
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply app_comb_red.  auto. auto. 
eapply transitive_red.
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
unfold A_k.
eapply2 star_opt_beta2. auto. auto. 
unfold subst. 
rewrite ! subst_rec_preserves_app_comb. 
rewrite ! subst_rec_ref. insert_Ref_out.  
rewrite ! subst_rec_ref. insert_Ref_out.  
unfold lift; rewrite ! lift_rec_null.
rewrite ! lift_rec_closed. 
2: eapply2 omega_k_closed. 
eapply transitive_red. 
eapply preserves_app_sf_red.
eapply2 app_comb_red. auto. 
rewrite (subst_rec_closed (omega_k 2)) at 1.
2: rewrite omega_k_closed; omega.
match goal with 
| |- multi_step sf_red1 (App (App (App (subst_rec (subst_rec ?M ?N1 0) ?N2 0) ?P1) ?P2) ?P3) _ => 
replace (App (App (subst_rec (subst_rec M N1 0) N2 0) P1) P2) with 
(subst_rec (subst_rec (App (App M P1) P2) N1 0) N2 0) 
end.
eapply preserves_app_sf_red. 
eapply subst_rec_preserves_sf_red.
eapply subst_rec_preserves_sf_red.
eapply2 star_opt_beta2.  auto. 
rewrite ! subst_rec_app.
rewrite (subst_rec_closed h_fn) at 1.
rewrite (subst_rec_closed h_fn) at 1.
rewrite (subst_rec_closed (app_comb (omega_k 2) (omega_k 2))) at 1. 
rewrite (subst_rec_closed (app_comb (omega_k 2) (omega_k 2))) at 1.
auto. 
3, 4: cbv; auto. 
1,2: unfold app_comb; unfold_op;  rewrite ! maxvar_app; rewrite ! omega_k_closed; cbv; auto.
(* 1 *)      
eapply transitive_red.
eapply preserves_app_sf_red.
auto. 
unfold subst; rewrite ! subst_rec_preserves_app_comb.
rewrite (subst_rec_closed (star_opt _)) at 1. 2: cbv; auto. 
rewrite (subst_rec_closed (star_opt _)) at 1. 2: cbv; auto. 
rewrite (subst_rec_closed (star_opt _)) at 1. 2: cbv; auto. 
rewrite (subst_rec_closed (star_opt _)) at 1. 2: cbv; auto. 
rewrite subst_rec_ref at 1. insert_Ref_out. 
rewrite subst_rec_ref at 1. insert_Ref_out. 
rewrite subst_rec_ref at 1. insert_Ref_out. 
unfold lift; rewrite ! lift_rec_null. 
rewrite subst_rec_lift_rec; try omega. 
rewrite lift_rec_null. 
rewrite ! subst_rec_closed. 
2: cbv; auto. 
2: rewrite subst_rec_closed. 
2: cbv; auto. 
2: cbv; auto. 
2: rewrite maxvar_app_comb; rewrite ! omega_k_closed; auto. 
2: rewrite subst_rec_closed.  2, 3: rewrite maxvar_app_comb.
2,3: rewrite omega_k_closed; auto.
eapply transitive_red. eapply2 app_comb_red. 
eapply2 star_opt_beta2.
(* 1 *)  
eapply transitive_red. 
eapply extensions_by_matchfail.
unfold subst; rewrite ! subst_rec_preserves_app_comb.
rewrite ! subst_rec_ref. insert_Ref_out. 
rewrite ! subst_rec_ref. insert_Ref_out. 
unfold lift; rewrite ! lift_rec_null. 
rewrite subst_rec_lift_rec; try omega. 
rewrite lift_rec_null.
rewrite ! (subst_rec_closed a_op).
2: cbv; auto. 
eapply2 matchfail_app_comb_l.
eapply2 matchfail_compound_l. 
fold star_opt. 
eapply2 matchfail_compound_r.  
eapply2 matchfail_compound_r.  
unfold_op; unfold occurs. 
unfold plus. cbv. 
eapply2 matchfail_compound_l. 
(* 1 *)  
eapply transitive_red. 
eapply preserves_app_sf_red. auto. 
unfold subst; rewrite ! subst_rec_preserves_app_comb.
rewrite ! subst_rec_ref. insert_Ref_out. 
rewrite ! subst_rec_ref. insert_Ref_out. 
unfold lift; rewrite ! lift_rec_null. 
rewrite subst_rec_lift_rec; try omega. 
rewrite lift_rec_null.
rewrite ! (subst_rec_closed a_op).
2: cbv; auto. auto. 
(* 1 *)  
eapply transitive_red. 
eapply extensions_by_matchfail.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_compound_l. 
fold star_opt. 
eapply2 matchfail_compound_r.  
eapply2 matchfail_compound_r.  
unfold_op; unfold occurs. 
unfold plus. 
cbv. 
eapply2 matchfail_compound_l. 
(* 1 *)  
eapply transitive_red. 
eapply extensions_by_matchfail.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_compound_l. 
fold star_opt. 
eapply2 matchfail_compound_r.  
eapply2 matchfail_compound_r.  
unfold_op; unfold occurs. 
unfold plus. cbv. 
eapply2 matchfail_compound_l.
(* 1 *)  
eapply transitive_red. 
eapply extensions_by_matchfail.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_compound_l. 
fold star_opt. 
eapply2 matchfail_compound_r.  
eapply2 matchfail_compound_r.  
unfold_op; unfold occurs. 
unfold plus.
cbv. 
eapply2 matchfail_compound_l. 
(* 1 *)  
eapply transitive_red. 
eapply extensions_by_matchfail.
eapply2 matchfail_app_comb_r.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
unfold A_k. 
unfold app_comb. unfold_op.
rewrite star_opt_occurs_true.
rewrite star_opt_occurs_true.
eapply2 matchfail_compound_l.  
eapply2 matchfail_compound_r.  
eapply2 matchfail_compound_r.
cbv.
eapply2 matchfail_compound_l.  
eapply2 matchfail_compound_r.  
eapply2 matchfail_op.
right; auto. discriminate.
rewrite ! occurs_app.
rewrite occurs_star_opt.
rewrite ! occurs_app.
rewrite ! occur_ref.
unfold eqnat.
omega.
discriminate.
rewrite ! occurs_app.
rewrite ! occur_ref.
unfold eqnat.
omega.
discriminate.
(* 1 *) 
eapply transitive_red. 
eapply extensions_by_matchfail.
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. 
unfold_op. 
eapply2 matchfail_compound_r.
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matching.
unfold app_comb; unfold_op. 
eapply2 match_app.
repeat eapply2 match_app. 
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 program_matching.
split.  eapply2 omega_k_normal. eapply2 omega_k_closed.  
eapply2 match_app.
eapply2 program_matching.
split.  eapply2 omega_k_normal. eapply2 omega_k_closed.  
eapply2 program_matching.
split.  eapply2 nf_compound.
repeat eapply2 star_opt_normal. 
repeat eapply2 nf_compound. 
cbv. auto. 
(* 1 *) 
unfold length; fold length. 
rewrite ! map_lift0.
rewrite ! app_nil_r. 
unfold map. rewrite ! app_nil_l. 
rewrite ! subst_rec_app.
rewrite ! subst_rec_preserves_app_comb.
rewrite (subst_rec_closed (A_k _)) at 1. 
rewrite (subst_rec_closed (A_k _)) at 1. 
rewrite (subst_rec_closed (A_k _)) at 1. 
rewrite (subst_rec_closed (omega_k _)) at 1. 
rewrite (subst_rec_closed (omega_k _)) at 1. 
rewrite (subst_rec_closed (omega_k _)) at 1. 
rewrite (subst_rec_closed (omega_k _)) at 1. 
rewrite (subst_rec_closed (omega_k _)) at 1. 
rewrite (subst_rec_closed (omega_k _)) at 1. 
rewrite ! pattern_size_app_comb. 
rewrite ! pattern_size_ref.
rewrite ! pattern_size_closed.
2: cbv; auto. 2: eapply2 omega_k_closed. 
all: try (rewrite omega_k_closed; omega). 
all: try (rewrite A_k_closed; omega).
(* 1 *)  
rewrite ! subst_rec_ref. insert_Ref_out. 
rewrite ! subst_rec_ref. insert_Ref_out. 
rewrite ! subst_rec_ref. insert_Ref_out. 
unfold plus, lift.
unfold app, fold_left.
unfold subst. 
rewrite ! subst_rec_app.
rewrite ! subst_rec_preserves_app_comb. 
rewrite (subst_rec_closed (A_k _)). 
rewrite (subst_rec_closed (A_k _)). 
rewrite (subst_rec_closed (omega_k _)) at 1. 
rewrite (subst_rec_closed (omega_k _)) at 1. 
rewrite (subst_rec_closed (omega_k _)) at 1. 
rewrite (subst_rec_closed (omega_k _)) at 1. 
all: try (rewrite omega_k_closed; omega).
all: try (rewrite A_k_closed; omega).
rewrite ! subst_rec_ref. insert_Ref_out. 
rewrite ! subst_rec_ref. insert_Ref_out. 
unfold lift; rewrite ! lift_rec_null.
rewrite ! lift_rec_lift_rec; try omega. unfold plus. 
rewrite ! subst_rec_lift_rec; try omega.
rewrite ! lift_rec_null.
auto.
Qed. 
