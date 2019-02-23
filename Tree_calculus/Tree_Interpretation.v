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
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)


Require Import Omega Max Bool List.
Require Import IntensionalLib.SF_calculus.Test.  
Require Import IntensionalLib.SF_calculus.General.  
Require Import IntensionalLib.Wave_as_SF.SF_Terms.  
Require Import IntensionalLib.Wave_as_SF.SF_Tactics.  
Require Import IntensionalLib.Wave_as_SF.SF_reduction.  
Require Import IntensionalLib.Wave_as_SF.SF_Normal.  
Require Import IntensionalLib.Wave_as_SF.SF_Closed.  
Require Import IntensionalLib.Wave_as_SF.Substitution.  
Require Import IntensionalLib.Wave_as_SF.SF_Eval.  
Require Import IntensionalLib.Wave_as_SF.Star.  
Require Import IntensionalLib.Wave_as_SF.Wait.  
Require Import IntensionalLib.Wave_as_SF.Fixpoints.  
Require Import IntensionalLib.Wave_as_SF.Wave_Factor.  
Require Import IntensionalLib.Wave_as_SF.Wave_Factor2.  
Require Import IntensionalLib.Wave_as_SF.Equal.  
Require Import IntensionalLib.Wave_as_SF.Extensions.  

Definition A31 M := 
(App
     (App (Op Node) (App (Op Node) 
(App
     (App (Op Node)
        (App (Op Node)
           (App
              (App (Op Node)
                 (App (Op Node) (App k_op (App k_op M))))
(App
     (App (Op Node)
        (App (Op Node)
           (App (App (Op Node) (App (Op Node) (App (Op Node) (Op Node))))
              (App (App (Op Node) (Op Node)) (Op Node)))))
     (App (App (Op Node) (Op Node)) (Op Node))) 
))) 
(App (App (Op Node) (Op Node))
     (App (Op Node)
        (App (Op Node)
           (App (App (Op Node) (App (Op Node) (Op Node)))
              (App (Op Node) (Op Node))))))
)))
                    
     (App k_op a_op)).

Lemma A3_red1: forall M, sf_red (App (A_k 3) M) (A31 M).
Proof.
intros; unfold A_k. 
eapply transitive_red. 
eapply2 star_opt_beta. 
unfold subst. 
rewrite subst_rec_preserves_star_opt.
rewrite subst_rec_app.
rewrite subst_rec_closed. 
2: unfold a_op; split_all. 
rewrite subst_rec_preserves_app_comb.
unfold subst_rec. insert_Ref_out.
unfold star_opt.
rewrite occurs_closed. 
2: unfold a_op; split_all. 
unfold app_comb at 1. 
unfold occurs0 at 1.
unfold app_comb at 1. 
rewrite ! orb_false_l.
fold occurs0.
rewrite ! orb_true_l. 
fold star_opt.
eapply2 preserves_app_sf_red.
eapply2 preserves_app_sf_red.
eapply2 preserves_app_sf_red.
unfold app_comb, star_opt; fold star_opt. 
rewrite occurs_closed. 
2: unfold_op; split_all. 
unfold occurs0 at 1. 
rewrite ! orb_true_r. 
rewrite ! orb_true_l. 
eapply2 preserves_app_sf_red.
eapply2 preserves_app_sf_red.
unfold occurs0 at 1. 
rewrite ! orb_true_r. 
rewrite ! occurs0_lift. 
unfold_op; unfold occurs0.
rewrite ! orb_true_r. 
rewrite ! orb_false_l. 
eapply2 preserves_app_sf_red. 
eapply2 preserves_app_sf_red.
eapply2 preserves_app_sf_red.
eapply2 preserves_app_sf_red.
unfold subst, lift; simpl.
rewrite subst_rec_lift_rec; try omega. 
rewrite ! lift_rec_null.   
replace (
match lift_rec M 0 1 with
  | Ref 0 => App (Op Node) (Op Node)
  | Ref (S _) =>
      App (App (Op Node) (Op Node)) (App (App (Op Node) (Op Node)) M)
  | Op _ => App (App (Op Node) (Op Node)) (App (App (Op Node) (Op Node)) M)
  | App _ _ =>
      App (App (Op Node) (Op Node)) (App (App (Op Node) (Op Node)) M)
  end 
) 
with (App k_op (App k_op M)).  auto.  
case M; split_all. 
case n; split_all.
Qed. 

Definition A32 M N := 
(App
     (App (Op Node)
        (App (Op Node)
           (App
              (App (Op Node)
                 (App (Op Node) (App (App (Op Node) (Op Node))
     (App (App (Op Node) (Op Node))
        (App
           (App (Op Node)
              (App (Op Node)
                 (App (App (Op Node) (App (Op Node) (Op Node)))
                    (App (Op Node) (Op Node)))))
           (App
              (App (Op Node)
                 (App (Op Node) (App (App (Op Node) (Op Node)) N)))
              (App (App (Op Node) (Op Node)) M)))))
)) 
(App
     (App (Op Node)
        (App (Op Node)
           (App (App (Op Node) (App (Op Node) (App (Op Node) (Op Node))))
              (App (App (Op Node) (Op Node)) (Op Node)))))
     (App (App (Op Node) (Op Node)) (Op Node))) ))) 
(App (App (Op Node) (Op Node))
     (App (Op Node)
        (App (Op Node)
           (App (App (Op Node) (App (Op Node) (Op Node)))
              (App (Op Node) (Op Node)))))) ).

Lemma A3_red2: forall M N, sf_red (App (A31 M) N) (A32 M N).
Proof.
intros; unfold A31; unfold_op. 
eval_tac. eval_tac. eval_tac. eval_tac. eval_tac. eval_tac. eval_tac. 
eval_tac. eval_tac. eval_tac. eval_tac. eval_tac. eval_tac.
eapply2 preserves_app_sf_red. 
eapply2 preserves_app_sf_red. 
eapply2 preserves_app_sf_red. 
eapply2 preserves_app_sf_red. 
eapply2 preserves_app_sf_red. 
eapply2 preserves_app_sf_red. 
eapply2 preserves_app_sf_red. 
eapply2 preserves_app_sf_red.
eval_tac. eval_tac.
eapply2 preserves_app_sf_red.
eval_tac. eval_tac. eval_tac.  
eapply2 preserves_app_sf_red. 
eapply2 preserves_app_sf_red. 
eval_tac. eval_tac.  eval_tac. 
eval_tac. eval_tac. 
Qed.  

(* delete 

Lemma A3_red2: forall M N, sf_red (App (App (A_k 3) M) N) (A32 M N).
Proof.
intros; unfold A_k. 
eapply transitive_red. 
eapply2 star_opt_beta2. 
unfold subst. 
rewrite ! subst_rec_app.
rewrite ! (subst_rec_closed a_op). 
2: unfold a_op; split_all. 
rewrite ! subst_rec_preserves_app_comb.
rewrite ! subst_rec_ref. 
insert_Ref_out.
rewrite ! subst_rec_ref. 
insert_Ref_out.
unfold lift; rewrite ! lift_rec_null. 
rewrite subst_rec_lift_rec; try omega.
rewrite lift_rec_null. 
eapply transitive_red. 
unfold a_op. 
eapply2 star_opt_beta.
unfold subst; rewrite subst_rec_preserves_star_opt.
rewrite subst_rec_preserves_app_comb. 
unfold subst_rec. insert_Ref_out.
unfold app_comb.
unfold star_opt.
unfold_op; unfold occurs0; fold occurs0. 
rewrite ! orb_false_l.
rewrite ! orb_true_l. 
eapply2 preserves_app_sf_red. 
eapply2 preserves_app_sf_red. 
eapply2 preserves_app_sf_red. 
eapply2 preserves_app_sf_red. 
eapply2 preserves_app_sf_red. 
eapply2 preserves_app_sf_red. 
rewrite occurs0_lift. 
unfold subst; simpl.
rewrite ! subst_rec_lift_rec; try omega.
rewrite ! lift_rec_null.
auto.   
Qed. 

*) 

Definition A33 M N P := app_comb (app_comb M N) P.

Lemma A3_red3: forall M N P, sf_red (App (A32 M N) P) (A33 M N P).
Proof.
intros; unfold A32.
eval_tac. eval_tac. 
eapply2 preserves_app_sf_red.
eval_tac. eval_tac. eval_tac. 
eapply2 preserves_app_sf_red. 
eapply2 preserves_app_sf_red.
eval_tac. eval_tac. eval_tac. 
Qed. 

  
 
Lemma A3_red4 : forall M N P Q, 
sf_red (App (A33 M N P) Q) (App (App (App M N) P) Q). 
Proof. 
intros. unfold A33. 
eapply transitive_red. 
eapply2 app_comb_red. 
eapply transitive_red. 
eapply preserves_app_sf_red.
eapply2 app_comb_red. auto.  auto.  
Qed. 

Definition S_pm := star_opt (star_opt (star_opt (App (App (Ref 2) (Ref 0)) (App (Ref 1) (Ref 0))))). 
Definition new_S := A31 S_pm. 


Lemma new_S_correct : forall M N P, sf_red (App (App (App new_S M) N) P) (App (App M P) (App N P)). 
Proof. 
intros. unfold new_S, A31. 
eval_tac. eval_tac. eval_tac. eval_tac. eval_tac.  
eapply transitive_red. eval_tac. eval_tac. eval_tac. eval_tac. eval_tac.
eval_tac. eval_tac. eval_tac. eval_tac. eval_tac.
eval_tac. eval_tac. eval_tac. eval_tac. eval_tac.
 eval_tac. eval_tac. eval_tac. eval_tac. eval_tac.
eval_tac. eval_tac. eval_tac. eval_tac. eval_tac.
 eval_tac. eval_tac. eval_tac.
eapply2 preserves_app_sf_red. 
eapply2 preserves_app_sf_red. 
 eval_tac. eval_tac.  eval_tac. 
eapply2 preserves_app_sf_red. 
 eval_tac. eval_tac.  eval_tac. 
 eval_tac. eval_tac.
Qed.


Definition Fpm := 
extension (A33 (Ref 2) (Ref 1) (Ref 0))
          (App k_op (star_opt (App (App (Ref 0) (App (A31(Ref 1)) (Ref 2))) (Ref 3)))) (
extension (A32 (Ref 1) (Ref 0))
          (App k_op (star_opt (App (App (Ref 0) (A31 (Ref 1))) (Ref 2)))) ( 
(App k_op k_op))).


Definition new_F := A31 Fpm. 

Lemma new_F_new_S: forall M N, sf_red (App (App (App new_F new_S) M) N) M. 
Proof. 
intros. unfold new_F, new_S. 
unfold A31, Fpm. 
eval_tac.  eval_tac. eval_tac.  eval_tac. 
eval_tac.  eval_tac. eval_tac.  eval_tac. 
eval_tac.  eval_tac. eval_tac.  eval_tac. 
eval_tac.  eval_tac. eval_tac.  eval_tac. 
eval_tac.  eval_tac. eval_tac.  eval_tac. 
eval_tac.  eval_tac. eval_tac.  eval_tac. 
eval_tac.
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply succ_red. eapply2 k_red. 
auto. 
eapply succ_red. eapply2 k_red. auto.  
eapply succ_red. eapply2 k_red. auto.  
eapply succ_red. eapply2 s_red.
eapply succ_red. eapply2 k_red. 
eapply succ_red. eapply2 k_red. auto.  
eapply succ_red. eapply2 s_red.
eapply succ_red. eapply2 k_red. auto.
(* 1 *)  
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply succ_red. eapply2 k_red. 
auto. all: auto. 
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
(* 4 *) 
eapply2 extensions_by_matchfail.
unfold A33; split_all. 
unfold app_comb; unfold_op; split_all. 
eapply2 matchfail_compound_l.
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_l.
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
eapply2 matchfail_op.
unfold factorable. right; auto. congruence. 
auto. auto. 
(* A32 *) 
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply2 extensions_by_matchfail.
unfold A32, A31; split_all. 
eapply2 matchfail_compound_l.
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_l.
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_l.
eapply2 matchfail_compound_r.
eapply2 matchfail_op.
unfold factorable. right; auto. congruence. 
auto. auto.
(* k_op *) 
eval_tac. 
Qed. 

 

Lemma new_F_new_F: forall M N, sf_red (App (App (App new_F new_F) M) N) M. 
Proof. 
intros. unfold new_F, new_S. 
unfold A31, Fpm. 
eval_tac.  eval_tac. eval_tac.  eval_tac. 
eval_tac.  eval_tac. eval_tac.  eval_tac. 
eval_tac.  eval_tac. eval_tac.  eval_tac. 
eval_tac.  eval_tac. eval_tac.  eval_tac. 
eval_tac.  eval_tac. eval_tac.  eval_tac. 
eval_tac.  eval_tac. eval_tac.  eval_tac. 
eval_tac.
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply succ_red. eapply2 k_red. 
auto. 
eapply succ_red. eapply2 k_red. auto.  
eapply succ_red. eapply2 k_red. auto.  
eapply succ_red. eapply2 s_red.
eapply succ_red. eapply2 k_red. 
eapply succ_red. eapply2 k_red. auto.  
eapply succ_red. eapply2 s_red.
eapply succ_red. eapply2 k_red. auto.
(* 1 *)  
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply succ_red. eapply2 k_red. 
auto. all: auto. 
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
(* 4 *) 
eapply2 extensions_by_matchfail.
unfold A33; split_all. 
unfold app_comb; unfold_op; split_all. 
eapply2 matchfail_compound_l.
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_l.
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
eapply2 matchfail_op.
unfold factorable. right; auto. congruence. 
auto. auto. 
(* A32 *) 
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply2 extensions_by_matchfail.
unfold A32, A31; split_all. 
eapply2 matchfail_compound_l.
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_l.
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_l.
eapply2 matchfail_compound_r.
eapply2 matchfail_op.
unfold factorable. right; auto. congruence. 
auto. auto.
(* k_op *) 
eval_tac. 
Qed. 


Lemma A32_matching: forall M N, 
matching (A32 (Ref 1) (Ref 0)) (A32 M N) (cons (lift 1 M) (cons N nil)).
Proof. 
intros. unfold A32. 


replace (cons (lift 1 M) (cons N nil)) 
with (((map (lift (length (cons (lift 1 M)  (cons N nil))))) nil) ++ (cons (lift 1 M) (cons N nil))). 
2: simpl; split_all. 
eapply2 match_app. 
all: cycle 1. 
eapply2 program_matching. 
unfold program; split_all. split; auto. 
repeat eapply2 nf_compound.
(* 1 *) 
replace (lift 1 M :: N :: nil) with 
((map (lift (length (nil: (list SF)))) (cons (lift 1 M) (cons N nil))) ++ nil) .
all: cycle 1. simpl. 
unfold lift; rewrite ! lift_rec_null. auto. 
eapply2 match_app. 
(* 1 *) 
replace (lift 1 M :: N :: nil) with 
((map (lift (length (nil: (list SF)))) (cons (lift 1 M) (cons N nil))) ++ nil) .
all: cycle 1. simpl. 
unfold lift; rewrite ! lift_rec_null. auto. 
eapply2 match_app. 
(* 1 *) 
replace (lift 1 M :: N :: nil) with 
((map (lift (length (cons (lift 1 M) (cons N nil)))) nil) ++ (cons (lift 1 M) (cons N nil)))
by split_all. 
eapply2 match_app. 
all: cycle 1. 
eapply2 program_matching. 
unfold program; split_all. split; auto. 
repeat eapply2 nf_compound.
(* 1 *) 
replace (lift 1 M :: N :: nil) with 
((map (lift (length (nil: (list SF)))) (cons (lift 1 M) (cons N nil))) ++ nil) .
all: cycle 1. simpl. 
unfold lift; rewrite ! lift_rec_null. auto. 
eapply2 match_app.
(* 1 *)  
replace (lift 1 M :: N :: nil) with 
((map (lift (length (nil: (list SF)))) (cons (lift 1 M) (cons N nil))) ++ nil) .
all: cycle 1. simpl. 
unfold lift; rewrite ! lift_rec_null. auto. 
eapply2 match_app.
(* 1 *)  
replace (lift 1 M :: N :: nil) with 
((map (lift (length (nil: (list SF)))) (cons (lift 1 M) (cons N nil))) ++ nil) .
all: cycle 1. simpl. 
unfold lift; rewrite ! lift_rec_null. auto. 
eapply2 match_app.
eapply2 program_matching. 
unfold program; split_all. 
(* 1 *)  
replace (lift 1 M :: N :: nil) with 
((map (lift (length (nil: (list SF)))) (cons (lift 1 M) (cons N nil))) ++ nil) .
all: cycle 1. simpl. 
unfold lift; rewrite ! lift_rec_null. auto. 
eapply2 match_app.
eapply2 program_matching. 
unfold program; split_all. 
(* 1 *)  
replace (lift 1 M :: N :: nil) with 
((map (lift (length (nil: (list SF)))) (cons (lift 1 M) (cons N nil))) ++ nil) .
all: cycle 1. simpl. 
unfold lift; rewrite ! lift_rec_null. auto. 
eapply2 match_app.
eapply2 program_matching. 
unfold program; split_all. 
split; auto. 
repeat eapply2 nf_compound.
(* 1 *)  
replace (lift 1 M :: N :: nil) with 
((map (lift (length(cons N nil))) (cons M nil)) ++ (cons N nil))
by split_all. 
eapply2 match_app. 
(* 2 *) 
replace (cons N nil) with ((map (lift (length (nil: (list SF)))) (cons N nil)) ++ nil).
all: cycle 1. 
simpl. unfold lift; rewrite lift_rec_null; auto. 
all: cycle 1. 
eapply2 match_app.
(* 2 *) 
replace (cons N nil) with ((map (lift (length (nil: (list SF)))) (cons N nil)) ++ nil).
all: cycle 1. 
simpl. unfold lift; rewrite lift_rec_null; auto. 
all: cycle 1. 
eapply2 match_app.
(* 2 *) 
replace (cons N nil) with ((map (lift (length (nil: (list SF)))) (cons N nil)) ++ nil).
all: cycle 1. 
simpl. unfold lift; rewrite lift_rec_null; auto. 
all: cycle 1. 
eapply2 match_app.
eapply2 program_matching.
unfold program; split_all. 
(* 1 *) 
replace (cons M nil) with ((map (lift (length (nil: (list SF)))) (cons M nil)) ++ nil).
all: cycle 1. 
simpl. unfold lift; rewrite lift_rec_null; auto. 
eapply2 match_app.
eapply2 program_matching.
unfold program; split_all. 
Qed. 

 

Lemma A33_matching: forall M N P, 
matching (A33 (Ref 2) (Ref 1) (Ref 0)) (A33 M N P) (cons (lift 2 M) (cons (lift 1 N) (cons P nil))).
Proof. 
intros. unfold A33. 
unfold app_comb. 
replace (cons (lift 2 M) (cons (lift 1 N) (cons P nil))) 
with (((map (lift (length (nil: list SF))) (cons (lift 2 M) (cons (lift 1 N)  (cons P nil)))) ++ nil)).
2: simpl; split_all.  2: unfold lift; rewrite ! lift_rec_null; auto.
eapply2 match_app. 
eapply2 program_matching. 
unfold program; split_all. split; auto. unfold_op; 
repeat eapply2 nf_compound.
(* 1 *) 
replace (cons (lift 2 M) (cons (lift 1 N) (cons P nil))) 
with (((map (lift (length (cons P nil))) (cons (lift 1 M) (cons N nil))) ++ (cons P nil))). 
2: simpl; split_all. 2: unfold lift; rewrite lift_rec_lift_rec; try omega; auto.  
eapply2 match_app. 
replace (cons P nil) with ((map (lift (length (nil: (list SF)))) (cons P nil)) ++ nil).
2: split_all. 2: unfold lift; rewrite lift_rec_null; auto. 
eapply2 match_app.
replace (cons P nil) with ((map (lift (length (nil: (list SF)))) (cons P nil)) ++ nil).
2: split_all. 2: unfold lift; rewrite lift_rec_null; auto. 
eapply2 match_app.
replace (cons P nil) with ((map (lift (length (nil: (list SF)))) (cons P nil)) ++ nil).
2: split_all. 2: unfold lift; rewrite lift_rec_null; auto. 
eapply2 match_app.
left; unfold_op; auto. unfold_op; auto.  
eapply2 program_matching. 
unfold_op; unfold program; split_all.
(* 1 *) 
replace (lift 1 M :: N :: nil) with 
((map (lift (length (nil: (list SF)))) (cons (lift 1 M) (cons N nil))) ++ nil) .
all: cycle 1. simpl. 
unfold lift; rewrite ! lift_rec_null. auto. 
eapply2 match_app.
unfold_op; left; auto. 
unfold_op; auto. 
eapply2 program_matching. 
unfold_op; unfold program; split_all. 
(* 1 *) 
replace (lift 1 M :: N :: nil) with 
((map (lift (length (nil: (list SF)))) (cons (lift 1 M) (cons N nil))) ++ nil) .
all: cycle 1. simpl. 
unfold lift; rewrite ! lift_rec_null. auto. 
eapply2 match_app.
eapply2 program_matching. 
unfold_op; unfold program; split_all. 
split; auto; repeat eapply2 nf_compound. 
(* 1 *)  
replace (lift 1 M :: N :: nil) with 
((map (lift (length(cons N nil))) (cons M nil)) ++ (cons N nil))
by split_all. 
eapply2 match_app. 
(* 2 *) 
replace (cons N nil) with ((map (lift (length (nil: (list SF)))) (cons N nil)) ++ nil).
all: cycle 1. 
simpl. unfold lift; rewrite lift_rec_null; auto. 
all: cycle 1. 
eapply2 match_app.
(* 2 *) 
replace (cons N nil) with ((map (lift (length (nil: (list SF)))) (cons N nil)) ++ nil).
all: cycle 1. 
simpl. unfold lift; rewrite lift_rec_null; auto. 
all: cycle 1. 
eapply2 match_app.
(* 2 *) 
replace (cons N nil) with ((map (lift (length (nil: (list SF)))) (cons N nil)) ++ nil).
all: cycle 1. 
simpl. unfold lift; rewrite lift_rec_null; auto. 
replace (cons M nil) with ((map (lift (length (nil: (list SF)))) (cons M nil)) ++ nil).
all: cycle 1. 
simpl. unfold lift; rewrite lift_rec_null; auto. 
all: cycle 1. 
eapply2 match_app.
left; unfold_op; auto. 
unfold_op; auto. 
unfold_op; eapply2 program_matching.
unfold program; split_all. 
(* 1 *) 
replace (cons N nil) with ((map (lift (length (nil: (list SF)))) (cons N nil)) ++ nil).
all: cycle 1. 
simpl. unfold lift; rewrite lift_rec_null; auto. 
replace (cons N nil) with ((map (lift (length (nil: (list SF)))) (cons N nil)) ++ nil).
all: cycle 1. 
simpl. unfold lift; rewrite lift_rec_null; auto. 
eapply2 match_app.
left; unfold_op; auto. 
unfold_op; auto. 
unfold_op; eapply2 program_matching.
unfold program; split_all.
simpl. 
unfold lift; rewrite ! lift_rec_null. 
auto.  
Qed. 

 
Lemma new_F_1: forall P M N, sf_red (App (App (App new_F (App new_S P)) M) N) (App (App N new_S) P). 
Proof. 
intros. unfold new_F.
eapply transitive_red. 
unfold A31, Fpm. 
eval_tac. eval_tac.  eval_tac.  eval_tac.  eval_tac.  eval_tac. 
eval_tac. eval_tac.  eval_tac.  eval_tac.  eval_tac.  eval_tac. 
eval_tac. eval_tac.  eval_tac.  eval_tac.  eval_tac.  eval_tac. 
eval_tac. eval_tac.  eval_tac.  eval_tac.  eval_tac.  eval_tac. 
eval_tac. 
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply succ_red. eapply2 k_red. 
all: auto. 
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply succ_red. eapply2 k_red. 
all: auto. 
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
all: cycle 1. 
eval_tac.  eval_tac.  eval_tac.
2: auto. 
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
all: cycle 1. 
unfold new_S. 
eapply2 A3_red2.
eval_tac. eval_tac.  2: auto. 
(* 1 *) 
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
(* A33 *) 
eapply2 extensions_by_matchfail.
unfold A33, A32; split_all. 
unfold app_comb; unfold_op; split_all. 
eapply2 matchfail_compound_l.
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_l.
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
eapply2 matchfail_op.
unfold factorable. right; auto. congruence. 
auto. auto. 
(* A32 *) 
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply2 extensions_by_matching.
eapply2 A32_matching. 
eval_tac. auto. 
(* 1 *)  
unfold fold_left, subst.  unfold_op. 
rewrite ! subst_rec_app. 
rewrite ! subst_rec_op.
eval_tac. eval_tac. eval_tac. 
eapply transitive_red. 
eapply preserves_app_sf_red.
eapply preserves_app_sf_red.
eapply succ_red. eapply2 k_red.
auto.  eval_tac. eval_tac. 
(* 1 *) 
eapply2 preserves_app_sf_red.
insert_Ref_out. unfold lift; rewrite lift_rec_null; auto. 
Qed.
  
  

 
Lemma new_F_1f: forall P M N, sf_red (App (App (App new_F (App new_F P)) M) N) (App (App N new_F) P). 
Proof. 
intros. unfold new_F.
eapply transitive_red. 
unfold A31, Fpm. 
eval_tac. eval_tac.  eval_tac.  eval_tac.  eval_tac.  eval_tac. 
eval_tac. eval_tac.  eval_tac.  eval_tac.  eval_tac.  eval_tac. 
eval_tac. eval_tac.  eval_tac.  eval_tac.  eval_tac.  eval_tac. 
eval_tac. eval_tac.  eval_tac.  eval_tac.  eval_tac.  eval_tac. 
eval_tac. 
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply succ_red. eapply2 k_red. 
all: auto. 
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply succ_red. eapply2 k_red. 
all: auto. 
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
all: cycle 1. 
eval_tac.  eval_tac.  eval_tac.
2: auto. 
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
all: cycle 1. 
unfold new_S. 
eapply2 A3_red2.
eval_tac. eval_tac.  2: auto. 
(* 1 *) 
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
(* A33 *) 
eapply2 extensions_by_matchfail.
unfold A33, A32; split_all. 
unfold app_comb; unfold_op; split_all. 
eapply2 matchfail_compound_l.
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_l.
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
eapply2 matchfail_op.
unfold factorable. right; auto. congruence. 
auto. auto. 
(* A32 *) 
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply2 extensions_by_matching.
eapply2 A32_matching. 
eval_tac. auto. 
(* 1 *)  
unfold fold_left, subst.  unfold_op. 
rewrite ! subst_rec_app. 
rewrite ! subst_rec_op.
eval_tac. eval_tac. eval_tac. 
eapply transitive_red. 
eapply preserves_app_sf_red.
eapply preserves_app_sf_red.
eapply succ_red. eapply2 k_red.
auto.  eval_tac. eval_tac. 
(* 1 *) 
eapply2 preserves_app_sf_red.
insert_Ref_out. unfold lift; rewrite lift_rec_null; auto. 
Qed.
  
  

Lemma new_F_2S : forall P Q M N, sf_red (App (App (App new_F (App (App new_S P) Q)) M) N) 
    (App (App N (A32 S_pm P)) Q).
Proof. 
intros. unfold new_F.
eapply transitive_red. 
unfold A31, Fpm. 
eval_tac. eval_tac.  eval_tac.  eval_tac.  eval_tac.  eval_tac. 
eval_tac. eval_tac.  eval_tac.  eval_tac.  eval_tac.  eval_tac. 
eval_tac. eval_tac.  eval_tac.  eval_tac.  eval_tac.  eval_tac. 
eval_tac. eval_tac.  eval_tac.  eval_tac.  eval_tac.  eval_tac. 
eval_tac. 
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply succ_red. eapply2 k_red. 
all: auto. 
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply succ_red. eapply2 k_red. 
all: auto. 
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
all: cycle 1. 
eval_tac.  eval_tac.  eval_tac.
2: auto. 
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
all: cycle 1. 
unfold new_S. 
eapply preserves_app_sf_red. 
eapply2 A3_red2. auto. 
eval_tac. eval_tac.  2: auto. 
(* 1 *) 
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red.
auto.
eapply2 A3_red3.
eval_tac. auto. 
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red.    
(* A33 *) 
eapply2 extensions_by_matching.
eapply2 A33_matching.
auto. auto.  
(* 1 *)  
unfold fold_left, subst.  unfold_op. 
rewrite ! subst_rec_app. 
rewrite ! subst_rec_op.
eval_tac. eval_tac. eval_tac.  
eapply transitive_red. 
eapply preserves_app_sf_red.
eapply preserves_app_sf_red.
eapply succ_red. eapply2 k_red.
auto.  eval_tac. eval_tac. 
(* 1 *) 
insert_Ref_out. unfold lift; rewrite ! lift_rec_null; auto.
rewrite subst_rec_lift_rec; try omega.  
rewrite ! lift_rec_null. 
(* 1 *) 
eapply2 preserves_app_sf_red. 
(* 1 *) 
eapply2 preserves_app_sf_red. 
eapply2 preserves_app_sf_red. 
eapply2 preserves_app_sf_red. 
eapply2 preserves_app_sf_red. 
eapply2 preserves_app_sf_red. 
eapply2 preserves_app_sf_red. 
eapply2 preserves_app_sf_red. 




eapply2 A3_red.

Check newS.
 
