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
(*                      Wait2.v                                       *)
(*                                                                    *)
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
Require Import IntensionalLib.Tree_calculus.Case.  
Require Import IntensionalLib.Tree_calculus.Extensions.  


Lemma app_comb_matching: forall P Q M N sigma1 sigma2, 
matching P M sigma2 -> matching Q N sigma1 -> 
matching (app_comb P Q) (app_comb M N) (map (lift (length sigma1)) sigma2 ++ sigma1).
Proof. 
intros. unfold app_comb.
replace (map (lift (length sigma1)) sigma2 ++ sigma1) with 
(map (lift (length (nil : list Tree))) (map (lift (length sigma1)) sigma2 ++ sigma1) ++ nil).
2: simpl; split_all. 2: rewrite map_lift0; rewrite app_nil_r; auto .
eapply2 match_app. 
eapply2 program_matching. 
unfold_op; unfold program; split_all. split; auto. 
unfold_op; repeat eapply2 nf_compound.
(* 1 *) 
eapply2 match_app. 
replace sigma1
with (((map (lift (length (nil: list Tree))) sigma1) ++ nil)). 
2: simpl; split_all. 2: rewrite map_lift0; eapply2 app_nil_r. 
eapply2 match_app. 
(* 1 *) 
replace sigma1
with (((map (lift (length (nil: list Tree))) sigma1) ++ nil)). 
2: simpl; split_all. 2: rewrite map_lift0; eapply2 app_nil_r. 
eapply2 match_app. 
(* 1 *) 
replace sigma1
with (((map (lift (length (nil: list Tree))) sigma1) ++ nil)). 
2: simpl; split_all. 2: rewrite map_lift0; eapply2 app_nil_r. 
unfold_op; eapply2 match_app. 
(* 1 *) 
eapply2 program_matching. 
unfold_op; unfold program; split_all. 
(* 1 *) 
replace sigma2
with (((map (lift (length (nil: list Tree))) sigma2) ++ nil)). 
2: simpl; split_all. 2: rewrite map_lift0; eapply2 app_nil_r. 
unfold_op; eapply2 match_app. 
(* 1 *) 
eapply2 program_matching. 
unfold_op; unfold program; split_all. 
Qed. 



Definition flip N :=  App (App node (App node (App k_op N))) i_op.

Lemma flip_flips: forall M N, sf_red (App (flip N) M) (App M N).
Proof. 
intros; unfold flip; unfold_op. eval_tac.  eval_tac.
eapply transitive_red. eapply preserves_app_sf_red.
eapply succ_red. eapply2 k_red. 
 auto.  eval_tac. auto. 
Qed. 

Lemma maxvar_flip: forall N, maxvar (flip N) = maxvar N.
Proof. intros; unfold flip. unfold_op; simpl.  rewrite max_zero; auto.  Qed.

Lemma flip_normal: forall N, normal N -> normal (flip N). 
Proof.  intros; unfold flip. unfold_op; simpl. repeat eapply2 nf_compound.  Qed.

Lemma subst_rec_preserves_flip: forall N P k, subst_rec (flip N) P k = flip (subst_rec N P k). 
Proof. intros; unfold flip; unfold_op.  simpl; auto. Qed. 
  

Definition app_comb2 M N := app_comb (flip N) M. 

Lemma app_comb2_red : forall M N P, sf_red (App (app_comb2 M N) P) (App (App M N) P).
Proof.
intros; unfold app_comb2. eapply transitive_red. eapply2 app_comb_red.
eapply transitive_red. eapply preserves_app_sf_red.
eapply2 flip_flips. auto. auto. 
Qed.

Lemma maxvar_app_comb2: forall M N, maxvar (app_comb2 M N) = max (maxvar M) (maxvar N). 
Proof. intros; unfold app_comb2. rewrite maxvar_app_comb. rewrite maxvar_flip.  eapply2 max_swap. 
Qed.      

Lemma app_comb2_normal: forall M N, normal M -> normal N -> normal (app_comb2 M N).
Proof. intros; unfold app_comb2. eapply2 app_comb_normal.  eapply2 flip_normal. Qed.

Lemma subst_rec_preserves_app_comb2: 
forall M N P k, subst_rec (app_comb2 M N) P k = app_comb2 (subst_rec M P k) (subst_rec N P k).
Proof. 
intros; unfold app_comb2.  rewrite subst_rec_preserves_app_comb.  rewrite subst_rec_preserves_flip. auto. 
Qed.  
  
 


(* delete ? 
ace sigma
with (((map (lift (length (nil: list Tree))) sigma) ++ nil)). 
2: simpl; split_all. 2: rewrite map_lift0; eapply2 app_nil_r. 
eapply2 match_app. 
(* 1 *) 
replace sigma
with (((map (lift (length sigma)) nil) ++ sigma)). 
2: simpl; split_all. 
eapply2 match_app. 
all: cycle 1. 
eapply2 program_matching. 
unfold_op; unfold program; split_all. split; auto. 
unfold_op; repeat eapply2 nf_compound.
(* 1 *) 
replace sigma
with (((map (lift (length (nil: list Tree))) sigma) ++ nil)). 
2: simpl; split_all. 2: rewrite map_lift0; eapply2 app_nil_r. 
eapply2 match_app. 
(* 1 *) 
replace sigma
with (((map (lift (length (nil: list Tree))) sigma) ++ nil)). 
2: simpl; split_all. 2: rewrite map_lift0; eapply2 app_nil_r. 
eapply2 match_app. 
(* 1 *) 
replace sigma
with (((map (lift (length (nil: list Tree))) sigma) ++ nil)). 
2: simpl; split_all. 2: rewrite map_lift0; eapply2 app_nil_r. 
unfold_op; eapply2 match_app.
eapply2 program_matching. 
unfold program; split_all.
(* 1 *) 
replace sigma
with (((map (lift (length (nil: list Tree))) sigma) ++ nil)). 
2: simpl; split_all. 2: rewrite map_lift0; eapply2 app_nil_r. 
eapply2 match_app. 
(* 1 *) 
eapply2 program_matching. 
unfold program; split_all.
Qed. 


Lemma A32_matching: forall P Q M N sigma, 
matching (App (App (Op Node) Q) P) (App (App (Op Node) N) M) sigma -> 
matching (A32 P Q) (A32 M N) sigma.
Proof. 
intros. unfold A32. 
replace sigma 
with (((map (lift (length sigma))) nil) ++ sigma). 
2: simpl; split_all. 
eapply2 match_app. 
all: cycle 1. 
eapply2 program_matching. 
unfold program; split_all. split; auto. 
repeat eapply2 nf_compound.
(* 1 *) 
replace sigma with 
((map (lift (length (nil: (list Tree)))) sigma) ++ nil) .
all: cycle 1. simpl. 
unfold lift; rewrite map_lift0; eapply2 app_nil_r. 
eapply2 match_app. 
(* 1 *) 
replace sigma with 
((map (lift (length (nil: (list Tree)))) sigma) ++ nil) .
all: cycle 1. simpl. 
unfold lift; rewrite map_lift0; eapply2 app_nil_r. 
eapply2 match_app. 
(* 1 *) 
replace sigma with 
((map (lift (length sigma)) nil) ++ sigma) .
all: cycle 1. simpl. auto. 
eapply2 match_app. 
all: cycle 1. 
eapply2 program_matching. 
unfold program; split_all. split; auto. 
repeat eapply2 nf_compound.
(* 1 *) 
replace sigma with 
((map (lift (length (nil: (list Tree)))) sigma) ++ nil) .
all: cycle 1. simpl. 
unfold lift; rewrite map_lift0; eapply2 app_nil_r. 
eapply2 match_app. 
(* 1 *) 
replace sigma with 
((map (lift (length (nil: (list Tree)))) sigma) ++ nil) .
all: cycle 1. simpl. 
unfold lift; rewrite map_lift0; eapply2 app_nil_r. 
eapply2 match_app. 
(* 1 *) 
replace sigma with 
((map (lift (length (nil: (list Tree)))) sigma) ++ nil) .
all: cycle 1. simpl. 
unfold lift; rewrite map_lift0; eapply2 app_nil_r. 
eapply2 match_app. 
eapply2 program_matching. 
unfold program; split_all. 
(* 1 *) 
replace sigma with 
((map (lift (length (nil: (list Tree)))) sigma) ++ nil) .
all: cycle 1. simpl. 
unfold lift; rewrite map_lift0; eapply2 app_nil_r. 
eapply2 match_app. 
eapply2 program_matching. 
unfold program; split_all. 
(* 1 *) 
replace sigma with 
((map (lift (length (nil: (list Tree)))) sigma) ++ nil) .
all: cycle 1. simpl. 
unfold lift; rewrite map_lift0; eapply2 app_nil_r. 
eapply2 match_app. 
eapply2 program_matching. 
unfold program; split_all.
split; auto; repeat eapply2 nf_compound. 
(* 1 *) 
inversion H; subst. 
inversion H7; subst. 
inversion H11; subst. 
simpl. rewrite ! map_lift0.
rewrite ! app_nil_r.  
eapply2 match_app. 
replace sigma3 with 
((map (lift (length (nil: (list Tree)))) sigma3) ++ nil) .
all: cycle 1. simpl. 
unfold lift; rewrite map_lift0; eapply2 app_nil_r. 
(* 2 *) 
replace sigma2 with 
((map (lift (length (nil: (list Tree)))) sigma2) ++ nil) .
all: cycle 1. simpl. 
unfold lift; rewrite map_lift0; eapply2 app_nil_r. 
eapply2 match_app. 
all: cycle 1. 
eapply2 match_app.
eapply2 program_matching. 
unfold program; split_all.
replace sigma3 with 
((map (lift (length (nil: (list Tree)))) sigma3) ++ nil) .
all: cycle 1. simpl. 
unfold lift; rewrite map_lift0; eapply2 app_nil_r. 
(* 1 *) 
replace sigma2 with 
((map (lift (length (nil: (list Tree)))) sigma2) ++ nil) .
all: cycle 1. simpl. 
unfold lift; rewrite map_lift0; eapply2 app_nil_r. 
eapply2 match_app.
replace sigma3 with 
((map (lift (length (nil: (list Tree)))) sigma3) ++ nil) .
all: cycle 1. simpl. 
unfold lift; rewrite map_lift0; eapply2 app_nil_r. 
eapply2 match_app.
eapply2 program_matching. 
unfold program; split_all.
Qed. 

Lemma A33_matching: forall P Q R M N T sigma, 
matching (App (App (Op Node) R) (App (App (Op Node) Q) P)) (App (App (Op Node) T) (App (App (Op Node) N) M)) sigma -> 
matching (A33 P Q R) (A33 M N T) sigma.
Proof. 
intros. unfold A33. 
unfold app_comb. 
replace sigma
with (((map (lift (length (nil: list Tree))) sigma)) ++ nil).
2: simpl; split_all.  2: rewrite map_lift0; eapply2 app_nil_r. 
eapply2 match_app. 
eapply2 program_matching. 
unfold program; split_all. split; auto. unfold_op; 
repeat eapply2 nf_compound.
(* 1 *) 
inversion H; subst. 
inversion H7; subst. 
inversion H11; subst. 
inversion H8; subst. 
inversion H15; subst. 
inversion H19; subst. 
simpl. clear - H12 H16 H20.
rewrite ! map_lift0. rewrite ! app_nil_r. 
eapply2 match_app. 
replace sigma3
with (map (lift (length (nil: list Tree))) sigma3 ++ nil).
2: simpl; rewrite map_lift0; eapply2 app_nil_r. 
eapply2 match_app. 
(* 2 *) 
replace sigma3
with (map (lift (length (nil: list Tree))) sigma3 ++ nil).
2: simpl; rewrite map_lift0; eapply2 app_nil_r. 
eapply2 match_app. 
(* 2 *) 
replace sigma3
with (map (lift (length (nil: list Tree))) sigma3 ++ nil).
2: simpl; rewrite map_lift0; eapply2 app_nil_r. 
unfold_op; eapply2 match_app. 
(* 2 *) 
eapply2 program_matching. 
unfold program; split_all.
(* 1 *)  
replace (map (lift (length sigma4)) sigma0 ++ sigma4)
with (map (lift (length (nil: list Tree))) (map (lift (length sigma4)) sigma0 ++ sigma4) ++ nil).
2: simpl; rewrite map_lift0; eapply2 app_nil_r. 
unfold_op; eapply2 match_app. 
eapply2 program_matching. 
unfold program; split_all.
(* 1 *)  
replace (map (lift (length sigma4)) sigma0 ++ sigma4)
with (map (lift (length (nil: list Tree))) (map (lift (length sigma4)) sigma0 ++ sigma4) ++ nil).
2: simpl; rewrite map_lift0; eapply2 app_nil_r. 
unfold_op; eapply2 match_app. 
eapply2 program_matching. 
unfold program; split_all.
split; auto; repeat eapply2 nf_compound. 
(* 1 *)  
eapply2 match_app. 
replace sigma4
with (map (lift (length (nil: list Tree))) sigma4 ++ nil).
2: simpl; rewrite map_lift0; eapply2 app_nil_r. 
unfold_op; eapply2 match_app.
(* 1 *) 
replace sigma4
with (map (lift (length (nil: list Tree))) sigma4 ++ nil).
2: simpl; rewrite map_lift0; eapply2 app_nil_r. 
unfold_op; eapply2 match_app.
(* 1 *) 
replace sigma4
with (map (lift (length (nil: list Tree))) sigma4 ++ nil).
2: simpl; rewrite map_lift0; eapply2 app_nil_r. 
unfold_op; eapply2 match_app.
eapply2 program_matching. 
unfold program; split_all.
(* 1 *) 
replace sigma0
with (map (lift (length (nil: list Tree))) sigma0 ++ nil).
2: simpl; rewrite map_lift0; eapply2 app_nil_r. 
unfold_op; eapply2 match_app.
eapply2 program_matching. 
unfold program; split_all.
Qed. 

Lemma A42_matching: forall M N, 
matching (A42 (Ref 1) (Ref 0)) (A42 M N) (cons (lift 1 M) (cons N nil)).
Proof. 
intros. unfold A42.
eapply2 A31_matching.  
replace (cons (lift 1 M) (cons N nil)) 
with (((map (lift (length (nil : list Tree)))  (cons (lift 1 M)  (cons N nil))) ++ nil)).
2: simpl; split_all. 2: unfold lift; rewrite ! lift_rec_null; auto. 
eapply2 match_app. 
 eapply2 program_matching. 
unfold program; split_all. split; auto. 
repeat eapply2 nf_compound.
(* 1 *)  
replace (lift 1 M :: N :: nil) with 
((map (lift (length(cons N nil))) (cons M nil)) ++ (cons N nil))
by split_all. 
eapply2 match_app. 
(* 2 *) 
replace (cons N nil) with ((map (lift (length (nil: (list Tree)))) (cons N nil)) ++ nil).
all: cycle 1. 
simpl. unfold lift; rewrite lift_rec_null; auto. 
all: cycle 1. 
eapply2 match_app.
(* 2 *) 
replace (cons N nil) with ((map (lift (length (nil: (list Tree)))) (cons N nil)) ++ nil).
all: cycle 1. 
simpl. unfold lift; rewrite lift_rec_null; auto. 
all: cycle 1. 
eapply2 match_app.
(* 2 *) 
replace (cons N nil) with ((map (lift (length (nil: (list Tree)))) (cons N nil)) ++ nil).
all: cycle 1. 
simpl. unfold lift; rewrite lift_rec_null; auto. 
all: cycle 1. 
eapply2 match_app.
eapply2 program_matching.
unfold program; split_all. 
(* 1 *) 
replace (cons M nil) with ((map (lift (length (nil: (list Tree)))) (cons M nil)) ++ nil).
all: cycle 1. 
simpl. unfold lift; rewrite lift_rec_null; auto. 
eapply2 match_app.
eapply2 program_matching.
unfold program; split_all. 
Qed. 

 

Lemma A43_matching: forall M N P, 
matching (A43 (Ref 2) (Ref 1) (Ref 0)) (A43 M N P) (cons (lift 2 M) (cons (lift 1 N) (cons P nil))).
Proof. 
intros. unfold A43. 
unfold app_comb. 
replace (cons (lift 2 M) (cons (lift 1 N) (cons P nil))) 
with (((map (lift (length (nil: list Tree))) (cons (lift 2 M) (cons (lift 1 N)  (cons P nil)))) ++ nil)).
2: simpl; split_all.  2: unfold lift; rewrite ! lift_rec_null; auto.
eapply2 A32_matching.
simpl. unfold lift; rewrite ! lift_rec_null. 
(* 1 *) 
replace (cons (lift_rec M 0 2) (cons (lift_rec N 0 1) (cons P nil))) 
with (((map (lift (length (cons P nil))) (cons (lift 1 M) (cons N nil))) ++ (cons P nil))). 
2:simpl; split_all. 2: unfold lift; rewrite lift_rec_lift_rec; try omega; auto.  
eapply2 match_app. 
replace (cons P nil) with ((map (lift (length (nil: (list Tree)))) (cons P nil)) ++ nil).
2: split_all. 2: unfold lift; rewrite lift_rec_null; auto. 
eapply2 match_app.
(* 1 *) 
replace (lift 1 M :: N :: nil) with 
((map (lift (length (nil: (list Tree)))) (cons (lift 1 M) (cons N nil))) ++ nil) .
all: cycle 1. simpl. 
unfold lift; rewrite ! lift_rec_null. auto. 
eapply2 match_app.
eapply2 program_matching. 
unfold_op; unfold program; split_all. split; auto; repeat eapply2 nf_compound.  
(* 1 *) 
replace (lift 1 M :: N :: nil) with 
((map (lift (length(cons N nil))) (cons M nil)) ++ (cons N nil))
by split_all. 
eapply2 match_app. 
(* 2 *) 
replace (cons N nil) with ((map (lift (length (nil: (list Tree)))) (cons N nil)) ++ nil).
all: cycle 1. 
simpl. unfold lift; rewrite lift_rec_null; auto. 
all: cycle 1. 
eapply2 match_app.
(* 2 *) 
replace (cons N nil) with ((map (lift (length (nil: (list Tree)))) (cons N nil)) ++ nil).
all: cycle 1. 
simpl. unfold lift; rewrite lift_rec_null; auto. 
all: cycle 1. 
eapply2 match_app.
(* 2 *) 
replace (cons N nil) with ((map (lift (length (nil: (list Tree)))) (cons N nil)) ++ nil).
all: cycle 1. 
simpl. unfold lift; rewrite lift_rec_null; auto. 
replace (cons M nil) with ((map (lift (length (nil: (list Tree)))) (cons M nil)) ++ nil).
all: cycle 1. 
simpl. unfold lift; rewrite lift_rec_null; auto. 
all: cycle 1. 
eapply2 match_app.
unfold_op; eapply2 program_matching.
unfold program; split_all. 
(* 1 *) 
replace (cons N nil) with ((map (lift (length (nil: (list Tree)))) (cons N nil)) ++ nil).
all: cycle 1. 
simpl. unfold lift; rewrite lift_rec_null; auto. 
replace (cons N nil) with ((map (lift (length (nil: (list Tree)))) (cons N nil)) ++ nil).
all: cycle 1. 
simpl. unfold lift; rewrite lift_rec_null; auto. 
eapply2 match_app.
eapply2 program_matching.
unfold program; split_all.
simpl. 
unfold lift; rewrite ! lift_rec_null. 
auto.  
Qed. 

*) 