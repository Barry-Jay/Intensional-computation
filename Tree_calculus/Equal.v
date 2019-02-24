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
(*                      Equal.v                                       *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)


Require Import ArithRing Bool Max Omega.
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


Lemma subst_rec_closed_Fop: 
forall M k, subst_rec Fop M k = Fop. 
Proof. 
intros. rewrite ! (subst_rec_closed Fop); [|simpl; auto]. auto. omega. 
Qed.  



(* General equality *)


Definition equal_body:=  
  App
     (App (App Fop (Ref 1))
        (App (App (App Fop (Ref 0)) k_op) 
             (App k_op (App k_op (App k_op i_op))))) 
     (star_opt (star_opt (App (App (App Fop (Ref 2)) (App k_op i_op))
        (star_opt (star_opt (App (App (App (App (Ref 6) (Ref 3)) (Ref 1))
                                      (App (App (Ref 6) (Ref 2)) (Ref 0)))
                                 (App k_op i_op)))))))
. 

  

Definition equal_fn := star_opt (star_opt (star_opt equal_body)). 

Lemma equal_fn_closed: maxvar equal_fn = 0.
Proof. cbv; auto.   Qed. 

Definition equal_comb := app_comb (Y_k 3) equal_fn. 

Lemma equal_comb_closed : maxvar equal_comb = 0.
Proof. cbv; omega. Qed. 


Lemma equal_comb_op : forall o, sf_red (App (App equal_comb (Op o)) (Op o)) k_op.
Proof. 
intros. 
eapply transitive_red.  unfold equal_comb.
eapply transitive_red. eapply preserves_app_sf_red.  eapply2 app_comb_red. all: auto. 
eapply transitive_red.   eapply2 Y3_fix.
unfold equal_fn at 1.
eapply transitive_red. eapply2 star_opt_beta3.  
unfold equal_body, lift, subst.
rewrite ! subst_rec_app; rewrite ! subst_rec_ref. 
unfold lift_rec. 
insert_Ref_out. 
rewrite ! subst_rec_ref. insert_Ref_out.
unfold lift; rewrite ! lift_rec_null.
rewrite ! (subst_rec_closed_Fop). 
rewrite ! (subst_rec_closed (Op o)).  2: simpl; auto.  2: simpl; auto. 
rewrite ! (subst_rec_closed k_op); [|simpl; auto]. 
rewrite ! (subst_rec_closed i_op); [|simpl; auto].
case o. 
eapply transitive_red. eapply2 factor_leaf. 
eapply transitive_red. eapply2 factor_leaf. 
auto.  
Qed.


Lemma unequal_op_compound : 
forall M o, compound M -> 
              sf_red (App (App equal_comb (Op o)) M) (App k_op i_op). 
Proof. 
split_all. 
eapply transitive_red.  unfold equal_comb. 
eapply preserves_app_sf_red. eapply2 app_comb_red. auto. 
eapply transitive_red. eapply2 Y3_fix. 
unfold equal_fn at 1.
eapply transitive_red. eapply2 star_opt_beta3.
unfold equal_body, lift, subst.
rewrite ! subst_rec_app; rewrite ! subst_rec_ref.
insert_Ref_out. rewrite ! subst_rec_ref.
insert_Ref_out. 
unfold lift, lift_rec; fold lift_rec. 
rewrite ! (subst_rec_closed_Fop). 
rewrite ! (subst_rec_closed (Op o)).   2: simpl; auto. 
rewrite ! (subst_rec_closed k_op); [|simpl; auto]. 
rewrite ! (subst_rec_closed i_op); [|simpl; auto].
rewrite ! lift_rec_null.
rewrite ! subst_rec_lift_rec; try omega. 
rewrite ! lift_rec_null. 
case o. 
eapply transitive_red. eapply2 factor_leaf.
inversion H; subst.  
eapply transitive_red. eapply2 factor_stem. eval_tac.  
eapply transitive_red. eapply2 factor_fork. eval_tac.  
Qed. 

Lemma unequal_op : 
forall M o, factorable M-> M <> (Op o) -> 
              sf_red (App (App equal_comb (Op o)) M) (App k_op i_op). 
Proof. 
split_all. unfold factorable in *. inversion H. inversion H1; subst. 
2: eapply2 unequal_op_compound. 
generalize H0; case o; case x; congruence. 
Qed. 



Lemma unequal_compound_op : 
forall M o, compound M -> 
              sf_red (App (App equal_comb M) (Op o))(App k_op i_op).
Proof.
split_all. 
eapply transitive_red. unfold equal_comb.
eapply transitive_red. eapply preserves_app_sf_red. eapply2 app_comb_red. auto.   
  eapply2 Y3_fix. 
unfold equal_fn at 1.
eapply transitive_red. eapply2 star_opt_beta3.
unfold equal_body, lift, subst.
rewrite ! subst_rec_app; rewrite ! subst_rec_ref.
insert_Ref_out. rewrite ! subst_rec_ref.
insert_Ref_out. 
unfold lift, lift_rec; fold lift_rec. 
rewrite ! lift_rec_null. 
rewrite ! (subst_rec_closed_Fop).
rewrite subst_rec_lift_rec; try omega. 
rewrite ! lift_rec_null.  
rewrite ! (subst_rec_closed (Op o)).  2: simpl; auto.  
rewrite ! (subst_rec_closed k_op); [|simpl; auto]. 
rewrite ! (subst_rec_closed i_op); [|simpl; auto].
case o. 
inversion H; subst. 
eapply transitive_red. eapply2 factor_stem. 
rewrite ! subst_rec_preserves_star_opt. 
eapply transitive_red. 
eapply2 star_opt_beta2.
unfold subst; 
rewrite ! subst_rec_app; rewrite ! subst_rec_ref.
insert_Ref_out. 
rewrite ! (subst_rec_closed_Fop). 
rewrite ! (subst_rec_closed (Op Node)).  2: simpl; auto.  
rewrite ! (subst_rec_closed k_op); [|simpl; auto]. 
rewrite ! (subst_rec_closed i_op); [|simpl; auto].
eapply transitive_red. eapply2 factor_leaf. auto. 
eapply transitive_red. eapply2 factor_fork. 
rewrite ! subst_rec_preserves_star_opt. 
eapply transitive_red. 
eapply2 star_opt_beta2.
unfold subst; 
rewrite ! subst_rec_app; rewrite ! subst_rec_ref.
insert_Ref_out. 
unfold lift, lift_rec; fold lift_rec. 
rewrite ! (subst_rec_closed_Fop). 
rewrite ! (subst_rec_closed (Op Node)); [|simpl; auto]. 
rewrite ! (subst_rec_closed k_op); [|simpl; auto]. 
rewrite ! (subst_rec_closed i_op); [|simpl; auto].
eapply transitive_red. eapply2 factor_leaf. auto. 
Qed.

Lemma unequal_op2 : 
forall M o, normal M -> maxvar M = 0 -> M <> (Op o) -> 
              sf_red (App (App equal_comb M) (Op o))(App k_op i_op).
Proof. 
split_all.
assert((exists o, M = (Op o)) \/ compound M) .
eapply2 programs_are_factorable. 
unfold program; auto.
inversion H2. 
2: eapply2 unequal_compound_op. 
split_all. inversion H3; subst. eapply2 unequal_op.
unfold factorable; eauto.   
Qed. 


Lemma equal_compounds : 
forall M N, compound M -> compound N -> 
sf_red (App (App equal_comb M) N) 
        (App (App 
                (App (App equal_comb (left_component M)) 
                     (left_component N))
                (App (App equal_comb (right_component M)) 
                     (right_component N)))
             (App k_op i_op))
.
Proof.
split_all. 
eapply transitive_red. unfold equal_comb.   eapply preserves_app_sf_red. 
eapply2 app_comb_red. auto.  
eapply transitive_red. eapply2 Y3_fix. 
replace (app_comb (Y_k 3) equal_fn) with equal_comb by auto. 
unfold equal_fn.
eapply transitive_red. eapply2 star_opt_beta3.
unfold equal_body, lift, subst.
rewrite ! subst_rec_app; rewrite ! subst_rec_ref.
insert_Ref_out. rewrite ! subst_rec_ref.
insert_Ref_out. 
unfold lift, lift_rec; fold lift_rec. 
rewrite ! lift_rec_null. 
rewrite (subst_rec_closed_Fop).
rewrite subst_rec_lift_rec; try omega. 
rewrite ! lift_rec_null.  
rewrite ! (subst_rec_closed k_op); [|simpl; auto]. 
rewrite ! (subst_rec_closed i_op); [|simpl; auto].
rewrite ! subst_rec_lift_rec; try omega. 
rewrite ! lift_rec_null. 
rewrite ! subst_rec_preserves_star_opt.
rewrite ! subst_rec_app. 
rewrite ! subst_rec_ref. 
insert_Ref_out. 
unfold lift;  rewrite ! lift_rec_lift_rec; try omega. 
unfold plus. 
rewrite ! subst_rec_lift_rec; try omega.
rewrite ! (subst_rec_closed_Fop). 
rewrite ! (subst_rec_closed k_op); [|simpl; auto]. 
rewrite ! (subst_rec_closed i_op); [|simpl; auto].
rewrite ! subst_rec_preserves_star_opt.
rewrite ! subst_rec_app. 
rewrite ! subst_rec_ref. 
insert_Ref_out. 
rewrite ! subst_rec_ref. 
insert_Ref_out. 
rewrite ! subst_rec_ref. 
insert_Ref_out. 
rewrite ! (subst_rec_closed k_op); [|simpl; auto]. 
rewrite ! (subst_rec_closed i_op); [|simpl; auto].
(* 1 *) 
inversion H; subst.  
eapply transitive_red. eapply2 factor_stem.
eapply transitive_red. eapply2 star_opt_beta2. 
unfold subst; 
rewrite ! subst_rec_app.
insert_Ref_out. 
unfold lift, lift_rec; fold lift_rec .
rewrite  (subst_rec_closed_Fop). 
rewrite ! subst_rec_lift_rec; try omega.
rewrite ! lift_rec_null.
rewrite  (subst_rec_closed k_op); [|simpl; auto]. 
rewrite (subst_rec_closed i_op); [|simpl; auto].
rewrite ! subst_rec_preserves_star_opt.
rewrite ! subst_rec_app. 
rewrite ! subst_rec_ref. 
insert_Ref_out. 
rewrite ! subst_rec_ref. 
insert_Ref_out. 
unfold lift;  rewrite ! lift_rec_lift_rec; try omega.
unfold plus. 
rewrite ! subst_rec_lift_rec; try omega. 
rewrite ! (subst_rec_closed k_op); [|simpl; auto]. 
rewrite ! (subst_rec_closed i_op); [|simpl; auto].
unfold lift_rec; fold lift_rec.
inversion H0; subst. 
(* 3 *)  
eapply transitive_red. eapply2 factor_stem.
eapply transitive_red. eapply2 star_opt_beta2. 
unfold subst; 
rewrite ! subst_rec_app.
insert_Ref_out. 
unfold lift, lift_rec; fold lift_rec. 
rewrite ! (subst_rec_closed k_op); [|simpl; auto]. 
rewrite ! (subst_rec_closed i_op); [|simpl; auto].
rewrite ! subst_rec_lift_rec; try omega.
rewrite ! lift_rec_null.
unfold subst_rec; fold subst_rec. 
insert_Ref_out. 
rewrite ! subst_rec_ref. 
insert_Ref_out. 
unfold lift;  rewrite ! lift_rec_lift_rec; try omega.
unfold plus. 
rewrite ! subst_rec_lift_rec; try omega.
rewrite ! lift_rec_null. 
eapply2 zero_red. 
(* 2 *) 
eapply transitive_red. eapply2 factor_fork.
eapply transitive_red. eapply2 star_opt_beta2. 
unfold subst; 
rewrite ! subst_rec_app.
insert_Ref_out. 
unfold lift, lift_rec; fold lift_rec. 
rewrite ! (subst_rec_closed k_op); [|simpl; auto]. 
rewrite ! (subst_rec_closed i_op); [|simpl; auto].
rewrite ! subst_rec_lift_rec; try omega.
rewrite ! lift_rec_null.
unfold subst_rec; fold subst_rec. 
insert_Ref_out. 
rewrite ! subst_rec_ref. 
insert_Ref_out. 
unfold lift;  rewrite ! lift_rec_lift_rec; try omega.
unfold plus. 
rewrite ! subst_rec_lift_rec; try omega.
rewrite ! lift_rec_null. simpl; auto.
(* 1 *)  
eapply transitive_red. eapply2 factor_fork.
eapply transitive_red. eapply2 star_opt_beta2. 
unfold subst; 
rewrite ! subst_rec_app.
insert_Ref_out. 
unfold lift, lift_rec; fold lift_rec. 
rewrite  (subst_rec_closed_Fop). 
rewrite ! subst_rec_lift_rec; try omega.
rewrite ! lift_rec_null.
rewrite ! subst_rec_preserves_star_opt.
rewrite ! subst_rec_app. 
rewrite ! subst_rec_ref. 
insert_Ref_out. 
rewrite ! subst_rec_ref. 
insert_Ref_out. 
unfold lift;  rewrite ! lift_rec_lift_rec; try omega.
unfold plus. 
rewrite ! subst_rec_lift_rec; try omega. 
inversion H0; subst. 
(* 2 *)  
eapply transitive_red. eapply2 factor_stem.
eapply transitive_red. eapply2 star_opt_beta2. 
unfold subst; 
rewrite ! subst_rec_app.
rewrite ! subst_rec_lift_rec; try omega.
rewrite ! lift_rec_null.
unfold subst_rec; fold subst_rec. 
insert_Ref_out. 
rewrite ! subst_rec_ref. 
insert_Ref_out. 
unfold lift;  rewrite ! lift_rec_lift_rec; try omega.
unfold plus. 
rewrite ! subst_rec_lift_rec; try omega.
rewrite ! lift_rec_null. simpl; auto. 
(* 1 *) 
eapply transitive_red. eapply2 factor_fork.
eapply transitive_red. eapply2 star_opt_beta2. 
unfold subst; 
rewrite ! subst_rec_app.
insert_Ref_out. 
unfold lift, lift_rec; fold lift_rec. 
rewrite ! (subst_rec_closed k_op); [|simpl; auto]. 
rewrite ! (subst_rec_closed i_op); [|simpl; auto].
rewrite ! subst_rec_lift_rec; try omega.
rewrite ! lift_rec_null.
unfold subst_rec; fold subst_rec. 
insert_Ref_out. 
rewrite ! subst_rec_ref. 
insert_Ref_out. 
unfold lift;  rewrite ! lift_rec_lift_rec; try omega.
unfold plus. 
rewrite ! subst_rec_lift_rec; try omega.
rewrite ! lift_rec_null. simpl; auto.
Qed.



Theorem equal_programs : forall M, program M -> sf_red (App (App equal_comb M) M) k_op.
Proof. 
cut(forall p M, p >= rank M -> program M -> 
sf_red (App (App equal_comb M) M) k_op)
.
unfold program; split_all. eapply2 H. 
induction p; split_all. 
assert(rank M >0) by eapply2 rank_positive. noway. 
(* p > 0 *)
assert(factorable M) . eapply2 programs_are_factorable.  
inversion H1; split_all; subst.  inversion H2; subst. 
eapply2 equal_comb_op.
apply transitive_red with 
(App (App (App (App equal_comb (left_component M)) (left_component M))
          (App (App equal_comb (right_component M)) (right_component M))) 
     (App k_op i_op))
.
eapply2 equal_compounds. 

apply transitive_red with (App (App k_op k_op) (App k_op i_op)).
eapply2 preserves_app_sf_red. 
eapply2 preserves_app_sf_red. 
(* left *) 
eapply2 IHp.  
assert(rank (left_component M) < rank M) by eapply2 rank_compound_l. 
omega. 
unfold program in *; split_all. inversion H0. split. 
inversion H3; cbv; auto.
assert(maxvar (left_component M) <= maxvar M) by 
(eapply2 left_component_preserves_maxvar). 
omega. 
(* right *) 
eapply2 IHp.  
assert(rank (right_component M) < rank M) .  eapply2 rank_compound_r. 
omega. 
unfold program in *; split_all. inversion H0.  split. 
inversion H2; subst; split_all; inversion H3; auto; inversion H6; auto. 
assert(maxvar (right_component M) <= maxvar M) by 
(eapply2 right_component_preserves_maxvar). 
omega. 
(* 1*)
repeat eval_tac; auto. 
Qed. 

Set Keep Proof Equalities.

Theorem unequal_programs : forall M N, program M -> program N -> M<>N ->
                                       sf_red (App (App equal_comb M) N) (App k_op i_op).

Proof. 
cut(forall p  M N, p >= rank M -> program M -> program N -> M<>N ->  
sf_red (App (App equal_comb M) N) (App k_op i_op)
). 
split_all. eapply2 H. 
induction p; split_all. 
assert(rank M >0) by eapply2 rank_positive. noway. 
(* p > 0 *)
assert(factorable M) by eapply2 programs_are_factorable.  
assert(factorable N) by eapply2 programs_are_factorable.  
unfold program in *. 
inversion H3; inversion H4; split_all. inversion H5; inversion H6; subst.   
eapply2 unequal_op.
inversion H5; subst. inversion H1. eapply2 unequal_op.
inversion H6; inversion H0; subst. eapply2 unequal_compound_op.
(* both compounds *) 
apply transitive_red with 
(App (App (App (App equal_comb (left_component M)) (left_component N))
          (App (App equal_comb (right_component M)) (right_component N)))
     (App k_op i_op))
.
eapply2 equal_compounds.  inversion H0; inversion H1. 

assert(left_component M = left_component N \/ left_component M <> left_component N) 
by repeat (decide equality). 
assert(right_component M = right_component N \/ right_component M <> right_component N) 
by repeat (decide equality). 
inversion H11. 
inversion H12. 
(* 3 *) 
assert False. eapply2 H2. 
eapply2 components_monotonic; split_all. noway. 
(* 2 *) 
apply transitive_red with (App (App k_op (App k_op i_op)) (App k_op i_op)).
eapply2 preserves_app_sf_red. 
eapply2 preserves_app_sf_red. 
rewrite H13. eapply2 equal_programs.
unfold program; split. 
inversion H9; subst; split_all;  unfold_op; auto. 
assert(maxvar (left_component N) <= maxvar N) by 
(eapply2 left_component_preserves_maxvar). 
omega. 
eapply2 IHp.  
assert(rank (right_component M) < rank M) by eapply2 rank_compound_r. 
omega. 
split. 
inversion H7; subst; split_all. 
assert(maxvar (right_component M) <= maxvar M) by 
(eapply2 right_component_preserves_maxvar). 
omega. 
split. 
inversion H9; subst; split_all. 
assert(maxvar (right_component N) <= maxvar N) by 
(eapply2 right_component_preserves_maxvar). 
omega. 
eval_tac. 
(* 1 *) 
apply transitive_red with (App (App (App k_op i_op) (App (App equal_comb (right_component M)) (right_component N))) (App k_op i_op)).
eapply2 preserves_app_sf_red. 
eapply2 preserves_app_sf_red. 
eapply2 IHp.  
assert(rank (left_component M) < rank M) by eapply2 rank_compound_l. 
omega. 
split. 
inversion H7; subst; split_all. 
unfold_op; auto. unfold_op; auto. 
assert(maxvar (left_component M) <= maxvar M) by 
(eapply2 left_component_preserves_maxvar). 
omega. 
split. 
inversion H9; subst; split_all. 
unfold_op; auto. unfold_op; auto. 
assert(maxvar (left_component N) <= maxvar N) by 
(eapply2 left_component_preserves_maxvar). 
omega.  
eval_tac.  eval_tac. 
Qed. 

(* delete ? 

Fixpoint equal_pattern P M := (* assumes that the pattern is a program *) 
match P with 
| Ref _ => star_opt M 
| Op Sop =>  (App (App (App Fop M) 
  (App (App (App (App M Fop) k_op) k_op) i_op))
     (App k_op (App k_op (App k_op i_op))))
| Op F => (App(App (App Fop M)
        (App
           (App
              (App (App (App (App M Fop) k_op) k_op) i_op)
              (App k_op i_op)) k_op))
     (App k_op (App k_op (App k_op i_op))))
| App P1 P2 => App (App (App Fop M) (App k_op i_op)) 
  (star_opt (star_opt (App (App (equal_pattern P1 (Ref 1)) 
  (equal_pattern P2 (Ref 0))) (App k_op i_op))))
end.

Lemma equal_comb_to_equal_pattern :
forall P M Q R, program P -> sf_red (App (App (App (App equal_comb P) M) Q) R) 
(App (App (equal_pattern P M) Q) R).
Proof.
unfold program; intros P M Q R p; inversion p;  fold equal_pattern.  
eapply transitive_red. 
unfold equal_comb.  eapply transitive_red. eapply preserves_app_sf_red. 
 eapply preserves_app_sf_red. 
eapply transitive_red.  eapply preserves_app_sf_red. 
eapply2 app_comb_red. auto.
eapply transitive_red.  eapply2 Y3_fix.  
replace (app_comb (Y_k 3) equal_fn) with equal_comb by auto. 
unfold equal_fn. 
eapply transitive_red. eapply2 star_opt_beta3. 
unfold equal_body, subst, subst_rec; fold subst_rec. insert_Ref_out. 
unfold subst_rec; fold subst_rec; insert_Ref_out. 
unfold lift, lift_rec; fold lift_rec; unfold subst_rec; fold subst_rec.
rewrite ! lift_rec_null. rewrite ! subst_rec_lift_rec; try omega.
unfold_op. 
rewrite ! lift_rec_null.  insert_Ref_out.    
unfold lift, lift_rec; fold lift_rec; unfold subst_rec; fold subst_rec.
assert(forall P Q N k, subst_rec (eq_op P Q) N k = eq_op (subst_rec P N k) (subst_rec Q N k)). 
intros. unfold eq_op, iff, not, S_not_F; unfold_op; unfold subst_rec; fold subst_rec. auto. 
rewrite ! H1.  
repeat (unfold subst_rec; fold subst_rec; insert_Ref_out). 
unfold lift; rewrite ! lift_rec_null. rewrite ! subst_rec_lift_rec; try omega.
rewrite ! lift_rec_null.
rewrite ! subst_rec_preserves_star_opt. 
repeat (unfold subst_rec; fold subst_rec; insert_Ref_out). 
rewrite ! subst_rec_preserves_star_opt. 
repeat (unfold subst_rec; fold subst_rec; insert_Ref_out). 
unfold lift; rewrite ! lift_rec_lift_rec; try omega. unfold plus. 
rewrite ! subst_rec_lift_rec; try omega.
rewrite (lift_rec_closed equal_comb); auto. auto. auto. auto. 
(* 1 *) 
induction P; intros. 
(* 3 *) 
simpl in  H0; discriminate.
(* 2 *)
eval_tac. case o. 
(* 3 *) 
eapply2 preserves_app_sf_red. eapply2 preserves_app_sf_red. 
  eapply2 preserves_app_sf_red. eapply2 preserves_app_sf_red. 
unfold eq_op, iff, not, S_not_F; unfold_op. eval_tac. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply succ_red. eapply2 f_compound_red. eval_tac.  auto. auto.  eval_tac. 
(* 2 *) 
 eapply2 preserves_app_sf_red. eapply2 preserves_app_sf_red. 
  eapply2 preserves_app_sf_red. eapply2 preserves_app_sf_red. 
unfold eq_op, iff, not, S_not_F; unfold_op. eval_tac. eval_tac. 
(* 1 *) 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply succ_red. eapply2 f_compound_red. 
assert(status (App P1 P2) = Passive) by eapply2 closed_implies_passive.  
inversion H; auto. 
rewrite H6 in H1; discriminate. 
eapply2 star_opt_beta2. auto. auto. 
unfold_op. 
unfold subst; rewrite ! subst_rec_app.  
unfold left_component, right_component. 
rewrite ! subst_rec_op. rewrite ! subst_rec_preserves_star_opt. 
unfold subst_rec; fold subst_rec.  insert_Ref_out. 
unfold lift; rewrite lift_rec_lift_rec; try omega. unfold plus. 
rewrite ! subst_rec_lift_rec; try omega. 
rewrite ! (subst_rec_closed equal_comb). 2: auto. 
unfold subst_rec; fold subst_rec; insert_Ref_out. 
rewrite lift_rec_null. 
unfold lift; rewrite ! lift_rec_closed. 2: simpl in H0; max_out. 
2: simpl in H0; max_out.
unfold equal_pattern; fold equal_pattern. 
do 3 eapply2 preserves_app_sf_red. 
 


2: simpl in *; max_out. 
2: simpl in *; max_out. 
2: auto. 
eapply2 preserves_app_sf_red. 


  

repeat eval_tac.  auto.  auto. 
eapply transitive_red. eval_tac. auto. auto. auto. auto. 


repeat eapply2 preserves_app_sf_red. 
  insert_Ref_out.    



*) 

(* 

Fixpoint size M := 
match M with 
| Ref _ => 1 
| Op _ => 1
| App M1 M2 => S(size M2 + size M1)
end . 

Lemma size_equal_comb : size equal_comb = 6079. 
Proof. cbv; auto. Qed. 
*) 
