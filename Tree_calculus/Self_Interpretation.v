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
(*                Self_Interpretation.v                               *)
(*                                                                b    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)


Require Import Omega Max Bool List.
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
Require Import IntensionalLib.Tree_calculus.Wait.  
Require Import IntensionalLib.Tree_calculus.Fixpoints.  
Require Import IntensionalLib.Tree_calculus.Wave_Factor.  
Require Import IntensionalLib.Tree_calculus.Wave_Factor2.  
Require Import IntensionalLib.Tree_calculus.Equal.  
Require Import IntensionalLib.Tree_calculus.Case.  
Require Import IntensionalLib.Tree_calculus.Extensions.  
Require Import IntensionalLib.Tree_calculus.Wait2.  

(* 

*) 
 
Definition eval_fn := 
star_opt (star_opt (
extension (App (App (Op Node) (Op Node)) (Ref 0)) (Ref 0) (
extension (App (App (Op Node) (App (Op Node) (Ref 1))) (Ref 0)) 
             (App (App (Ref 3) (App (App (Ref 3) (Ref 2)) (Ref 1))) (App (App (Ref 3) (Ref 2)) (Ref 0))) (
extension (App (App (Op Node) (App (App (Op Node) (Ref 2)) (Ref 1))) (Ref 0)) 
           (App (App (Ref 4) (Ref 1)) (App (App (Ref 4) (Ref 2)) (Ref 3))) (
star_opt (App (Ref 0) (Ref 1))
))))).


Lemma eval_fn_closed: maxvar eval_fn = 0.
Proof.
unfold eval_fn.
rewrite ! maxvar_star_opt.
rewrite ! maxvar_extension. simpl. auto. 
Qed. 

Lemma Y3_eval_fn_closed:  maxvar (Y3 eval_fn) = 0 . 
Proof.
unfold Y3. 
rewrite maxvar_star_opt. 
rewrite ! maxvar_app_comb. 
assert(maxvar omega3 = 0) by eapply2 omega3_program.
rewrite H. 
unfold lift. rewrite ! lift_rec_closed.
rewrite eval_fn_closed. auto. 
rewrite eval_fn_closed. auto.
Qed. 



Definition eager_app p a:= App (App (Y3 eval_fn) a) p.
(* the argument have been swapped *) 

Lemma eager_kernel : forall x y, sf_red (eager_app (App k_op x) y) x.
Proof. 
intros. unfold eager_app. 
eapply transitive_red. eapply2 Y3_fix_f.
unfold eval_fn at 1. 
eapply transitive_red. eapply preserves_app_sf_red. 
eapply star_opt_beta2. auto. 
unfold subst. rewrite ! subst_rec_preserves_extension.
eapply transitive_red. unfold_op.
eapply2 extensions_by_matching.
simpl. 
unfold subst. simpl. 
insert_Ref_out. 
unfold lift; rewrite ! lift_rec_null. 
auto.
Qed. 

Lemma eager_stem: forall x y z, sf_red (eager_app (App (App (Op Node) (App (Op Node) x)) y) z) 
(eager_app (eager_app y z) (eager_app x z)).
Proof.
intros. unfold eager_app. 
eapply transitive_red. eapply2 Y3_fix_f.
unfold eval_fn at 1. 
eapply transitive_red. eapply preserves_app_sf_red. 
eapply star_opt_beta2. auto. 
unfold subst. rewrite ! subst_rec_preserves_extension.
eapply transitive_red. 
eapply2 extensions_by_matchfail.
eapply2 matchfail_compound_l.
eapply2 matchfail_compound_r.
eapply2 matchfail_op.
unfold factorable. right. auto. congruence. 
(* 1 *)  
eapply transitive_red. 
eapply2 extensions_by_matching.
eapply2 match_app.  
subst_tac.
rewrite ! app_nil_r.
unfold pattern_size.  
repeat (replace (length nil) with 0 at 1 by auto).
unfold map; fold map. 
unfold lift; rewrite ! lift_rec_null.
rewrite lift_rec_lift_rec; try omega. 
unfold app, length, plus, fold_left.
unfold lift. subst_tac.  unfold lift; subst_tac. subst_tac. 
unfold lift; rewrite ! lift_rec_null. subst_tac. 
auto.
Qed. 
 



Lemma eager_fork: forall w x y z, sf_red (eager_app (App (App (Op Node) (App (App (Op Node) w) x)) y) z) 
(eager_app (eager_app z w) x).
Proof.
intros. unfold eager_app. 
eapply transitive_red. eapply2 Y3_fix_f.
unfold eval_fn at 1. 
eapply transitive_red. eapply preserves_app_sf_red. 
eapply star_opt_beta2. auto. 
unfold subst. rewrite ! subst_rec_preserves_extension.
eapply transitive_red. 
eapply2 extensions_by_matchfail.
eapply2 matchfail_compound_l.
eapply2 matchfail_compound_r.
eapply2 matchfail_op.
unfold factorable. right. auto. congruence. 
(* 1 *)  
eapply transitive_red. 
eapply2 extensions_by_matchfail.
eapply2 matchfail_compound_l.
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_l.
eapply2 matchfail_op.
unfold factorable. right. auto. congruence. 
(* 1 *)  
eapply transitive_red. 
eapply2 extensions_by_matching.
eapply2 match_app.
eapply2 match_app.   
(* 1 *) 
repeat (replace (length nil) with 0 by auto).
rewrite ! app_nil_r.  
unfold pattern_size.  
rewrite ! subst_rec_app.
rewrite ! subst_rec_ref.
insert_Ref_out. 
rewrite ! subst_rec_ref.
insert_Ref_out. 
repeat (replace (length nil) with 0 at 1 by auto).
rewrite ! plus_0_l. 
unfold map; fold map.
unfold length; fold length. 
simpl.  
unfold subst, subst_rec; fold subst_rec. 
unfold lift; rewrite ! lift_rec_null.
rewrite lift_rec_lift_rec; try omega. 
rewrite ! subst_rec_lift_rec; try omega. 
rewrite ! lift_rec_null.
simpl. 
rewrite ! subst_rec_lift_rec; try omega. 
insert_Ref_out. 
unfold lift; rewrite ! lift_rec_null.  
rewrite ! subst_rec_lift_rec; try omega.
rewrite ! lift_rec_null. 
auto.
Qed. 



Lemma eager_dud1: forall x, sf_red (eager_app (Op Node) x) (App (Op Node) x) .
Proof.
intros. unfold eager_app. 
eapply transitive_red. eapply2 Y3_fix_f.
unfold eval_fn at 1. 
eapply transitive_red. eapply preserves_app_sf_red. 
eapply star_opt_beta2. auto. 
unfold subst. rewrite ! subst_rec_preserves_extension.
eapply transitive_red. 
eapply2 extensions_by_matchfail.
(* 1 *)  
eapply transitive_red. 
eapply2 extensions_by_matchfail.
(* 1 *)  
eapply transitive_red. 
eapply2 extensions_by_matchfail.
(* 1 *) 
rewrite ! subst_rec_preserves_star_opt. 
eapply transitive_red.
eapply2 star_opt_beta.
unfold subst_rec; fold subst_rec. 
insert_Ref_out. 
unfold subst_rec, lift; fold subst_rec. 
insert_Ref_out. 
unfold subst; simpl. insert_Ref_out.
rewrite lift_rec_lift_rec; try omega. 
rewrite ! subst_rec_lift_rec; try omega.
unfold lift; rewrite ! lift_rec_null. auto. 
Qed. 
 
 


Lemma eager_dud2: forall x y, sf_red (eager_app (App (Op Node) x) y) (App (App (Op Node) x) y).
Proof.
intros. unfold eager_app. 
eapply transitive_red. eapply2 Y3_fix_f.
unfold eval_fn at 1. 
eapply transitive_red. eapply preserves_app_sf_red. 
eapply star_opt_beta2. auto. 
unfold subst. rewrite ! subst_rec_preserves_extension.
eapply transitive_red. 
eapply2 extensions_by_matchfail.
(* 1 *)  
eapply transitive_red. 
eapply2 extensions_by_matchfail.
(* 1 *)  
eapply transitive_red. 
eapply2 extensions_by_matchfail.
(* 1 *) 
rewrite ! subst_rec_preserves_star_opt. 
eapply transitive_red.
eapply2 star_opt_beta.
unfold subst_rec; fold subst_rec. 
insert_Ref_out. 
unfold subst, subst_rec, lift; fold subst_rec. 
insert_Ref_out. 
unfold subst; simpl. insert_Ref_out.
rewrite lift_rec_lift_rec; try omega. 
rewrite ! subst_rec_lift_rec; try omega.
unfold lift; rewrite ! lift_rec_null. auto. 
Qed. 
 
 
   

Lemma eager_app_preserves_sf_red: 
forall M M' N N', sf_red M M' -> sf_red N N' -> sf_red (eager_app M N) (eager_app M' N')  .
Proof. 
intros. unfold eager_app. 
auto. 
Qed.


(* stick with small step semantics *) 


Inductive eager : Tree -> Tree -> Tree -> Prop := 
| eag_kernel : forall M, eager (Op Node) M (App (Op Node) M)
| eag_stem : forall M N, eager (App (Op Node) M) N (App (App (Op Node) M) N) 
| eag_fork_kernel : forall M N, eager (App (App (Op Node) (Op Node)) M) N M
| eag_fork_stem : forall M N P v1 v2 v, eager N P v1 -> eager M P v2 -> eager v1 v2 v -> 
                    eager (App (App (Op Node) (App (Op Node) M)) N) P v
| eag_fork_fork : forall M N P Q v1 v, eager Q M v1 -> eager v1 N v -> eager (App (App (App (Op Node) M) N) P) Q v 
.

Lemma program_components:
  forall M, program M -> program (left_component M) /\ program (right_component M).
intros. 
inversion H; subst. 
inversion H0; subst. 
simpl; split; auto. unfold_op; auto. 
split; auto.
simpl; split; auto. unfold_op; auto. 
split; auto.
simpl; split; auto.  
split; auto. simpl in *; max_out. 
split; auto. simpl in *; max_out. 
simpl; split; auto. split; auto. simpl in *; max_out. 
split; auto. simpl in *; max_out.
Qed.


Lemma eager_preserves_programs:
  forall M N v, eager M N v -> program M -> program N -> program v.
Proof.
  intros M N v e; induction e; split_all.
  (* 5 *)
  split; auto. 
  eapply2 nf_compound. inversion H0; auto. simpl; inversion H0; auto. 
  split; auto.
  repeat eapply2 nf_compound. inversion H0; auto. simpl; inversion H; auto. 
  inversion H3; auto. inversion H0; auto. simpl. 
  inversion H0. inversion H. simpl in *; auto. rewrite H2; rewrite H4; auto. 
  replace M with (right_component (App (App (Op Node) (Op Node)) M)) by auto.
  eapply2 program_components. 
  (* 2 *)
  eapply2 IHe3. eapply2 IHe1.
  elim(program_components _ H); intros. simpl in *. auto.
  eapply2 IHe2. 
  elim(program_components _ H); intros. simpl in *.
  elim(program_components _ H1); intros. simpl in *.
  elim(program_components _ H4); intros. simpl in *. auto.
  (* 1 *)
  elim(program_components _ H); intros. simpl in *.
  elim(program_components _ H1); intros. simpl in *.
  elim(program_components _ H3); intros. simpl in *. 
  eapply2 IHe2.
Qed.



  Theorem eager_is_definable:
forall M N v, eager M N v -> program M -> program N -> sf_red (eager_app M N) v.
Proof.
  intros M N v e; induction e; split_all.
  (* 5 *)
  eapply2 eager_dud1.
  (* 4 *)
  eapply2 eager_dud2.
  (* 3 *)
  eapply2 eager_kernel. 
  (* 2 *)
  elim(program_components _ H); intros. simpl in *. 
  elim(program_components _ H1); intros; simpl in *.
  elim(program_components _ H4); intros; simpl in *.
  eapply transitive_red. eapply2 eager_stem.
  eapply transitive_red. eapply eager_app_preserves_sf_red.
  eapply2 IHe1. eapply2 IHe2. eapply2 IHe3.
  eapply2 eager_preserves_programs. 
  eapply2 eager_preserves_programs. 
  (* 1 *)
  inversion H. inversion H1. subst; simpl.
  inversion H7.
  assert(maxvar M = 0 -> False) by eapply2 active_not_closed.
  simpl in *. assert False. apply H3. max_out. max_out. omega. 
  inversion H7. 
Qed.
