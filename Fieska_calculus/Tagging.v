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

Definition tag_fn := 
  star_opt (star_opt (star_opt (star_opt 
      (App (App (Op Aop)  (App (App (Op Aop) (Ref 3)) (App (App (Op Aop) 
      (App (App (Op Aop) (Ref 3)) (Ref 2)))(Ref 1)))) (Ref 0)))))
. 
Definition tag_fix := App (App (Op Aop) (Y_k 3)) tag_fn. 
Definition tag M N := App (App (Op Aop) (App (App (Op Aop) tag_fix) M)) N. 

Lemma tag_red: forall M N P, sf_red (App (tag M N) P) (tag (tag M N) P).
Proof.
intros; unfold tag at 1. unfold tag_fix; unfold_op. 
eval_tac. eval_tac. eval_tac. 
eapply transitive_red. eapply preserves_app_sf_red. eapply Y3_fix. auto. 
unfold tag_fn at 1. 
eapply transitive_red. eapply2 star_opt_beta4. 
unfold subst; unfold_op; unfold subst, subst_rec; fold subst_rec. insert_Ref_out.
unfold lift.  
 repeat (unfold subst_rec; fold subst_rec; insert_Ref_out); unfold lift. 
repeat rewrite lift_rec_lift_rec; try omega.  unfold plus. 
repeat rewrite subst_rec_lift_rec; try omega. repeat rewrite lift_rec_null. 
auto. 
Qed. 

Lemma pattern_size_tag : forall M N, pattern_size (tag M N) = pattern_size M + pattern_size N. 
Proof. intros; unfold tag, tag_fix, tag_fn; unfold_op.  pattern_size_out. split_all.  Qed. 

Lemma subst_rec_preserves_tag: 
forall M N U k, subst_rec (tag M N) U k = tag (subst_rec M U k) (subst_rec N U k). 
Proof.
intros. unfold tag, tag_fix, tag_fn. 
unfold subst_rec; fold subst_rec. 
rewrite subst_rec_closed. 2: cbv; omega. 
repeat rewrite (subst_rec_preserves_star_opt).
unfold subst_rec; fold subst_rec. insert_Ref_out. 
auto. 
Qed. 

Lemma tag_fn_program: program tag_fn.
Proof. 
unfold tag_fn, program; intros; split. repeat eapply2 star_opt_normal.
nf_out. 
       repeat rewrite maxvar_star_opt. cbv. auto. 
Qed.

Lemma tag_fix_program: program tag_fix.
Proof.
  unfold tag_fix; split_all. split.  nf_out. eapply2 Y_k_program. eapply2 tag_fn_program. auto.  
Qed.

Lemma tag_fn_normal: normal tag_fn. Proof. eapply2 tag_fn_program. Qed. 
Lemma tag_fix_normal: normal tag_fix. Proof. eapply2 tag_fix_program. Qed. 


Lemma tag_normal: forall M N, normal M -> normal N -> normal (tag M N).
Proof.  intros. unfold tag, tag_fix, Y_k, a_op; unfold_op. nf_out.  
unfold_op; nf_out. eapply2 tag_fn_normal. Qed.


Lemma tag_maxvar: forall M N, maxvar (tag M N) = max (maxvar M) (maxvar N).
Proof.
  intros. unfold tag, tag_fix, Y_k, A_k, a_op; unfold_op. cbv. auto. 
 Qed.

Hint Resolve 
 Y_k_program tag_fn_program tag_fix_program Y_k_normal Y_k_closed tag_fn_normal
     tag_fix_normal. 

Definition var_fn := star_opt (star_opt (star_opt (tag (App (App (Op Aop) (Ref 2)) (Ref 1)) (Ref 0)))).
Definition var_fix := App (App (Op Aop) (Y_k 3)) var_fn.  
Definition var M := App (App (Op Aop) var_fix) M.

Lemma pattern_size_var : forall M, pattern_size (var M) = pattern_size M. 
Proof. intro; unfold var, var_fix, var_fn; unfold_op; pattern_size_out. split_all. Qed. 

Lemma subst_rec_preserves_var: 
forall M U k, subst_rec (var M) U k = var (subst_rec M U k). 
Proof.
intros. unfold var, var_fix, var_fn. 
rewrite ! subst_rec_app; rewrite ! subst_rec_op. 
rewrite subst_rec_closed; auto. rewrite Y_k_closed. omega. 
Qed. 

Lemma var_fn_program: program var_fn.
Proof. unfold var_fn, tag, program; intros. split. repeat eapply2 star_opt_normal.
nf_out. 
       repeat rewrite maxvar_star_opt. cbv; auto. 
Qed. 

Lemma var_fix_program: program var_fix.
Proof.  unfold var_fix; split. nf_out. eapply2 var_fn_program. auto.  Qed.

Lemma var_fn_normal: normal (var_fn). Proof. eapply2 var_fn_program. Qed. 
Lemma var_fn_closed: maxvar (var_fn) = 0. Proof. eapply2 var_fn_program. Qed. 
Lemma var_fix_normal: normal (var_fix). Proof. eapply2 var_fix_program. Qed. 
Lemma var_fix_closed: maxvar (var_fix) = 0. Proof. eapply2 var_fix_program. Qed. 

Hint Resolve var_fn_normal var_fn_closed var_fix_normal var_fix_closed. 

Lemma var_red:  forall M N, sf_red (App (var M) N) (tag (var M) N).
Proof.
unfold var, var_fix; unfold_op; split_all. eval_tac. eval_tac. 
eapply transitive_red. eapply Y3_fix. 
replace (App (App (Op Aop) (Y_k 3)) var_fn) with var_fix by auto. 
unfold var_fn. 
eapply transitive_red. eapply2 star_opt_beta3. 
unfold_op; unfold subst, subst_rec; fold subst_rec. 
rewrite ! subst_rec_preserves_tag. 
 unfold subst_rec; fold subst_rec. insert_Ref_out. 
 unfold subst_rec; fold subst_rec. insert_Ref_out.
 unfold subst_rec; fold subst_rec. insert_Ref_out. unfold lift.  
repeat rewrite lift_rec_lift_rec; try omega.  unfold plus. 
repeat rewrite subst_rec_lift_rec; try omega. 
rewrite ! lift_rec_null. 
auto. 
Qed. 


Lemma var_normal: forall M, normal M -> normal (var M). 
  intros. unfold var, var_fix, Y_k, a_op; unfold_op. nf_out. unfold_op. nf_out. Qed.

Lemma var_maxvar: forall M, maxvar (var M) = maxvar M.
Proof. intros. unfold var, var_fix, Y_k, A_k, a_op; unfold_op. cbv; auto. Qed.




Ltac maxvar_out1 :=
unfold a_op; unfold_op; 
try rewrite var_maxvar at 1; 
try rewrite maxvar_star_opt at 1; 
try rewrite  maxvar_extension at 1; 
try rewrite maxvar_case at 1 ; 
rewrite ? A_k_closed at 1;
 rewrite ? maxvar_app; 
pattern_size_out. 
