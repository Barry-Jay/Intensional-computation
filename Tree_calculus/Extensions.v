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
(*                    Extensions.v                                    *)
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
Require Import IntensionalLib.Tree_calculus.Wave_Factor.  
Require Import IntensionalLib.Tree_calculus.Wave_Factor2.  
Require Import IntensionalLib.Tree_calculus.Equal.  
Require Import IntensionalLib.Tree_calculus.Case.  


Set Keep Proof Equalities.


Definition extension P M R := App (App (Op Node) (App (Op Node)  (App k_op R))) (case P M). 


Lemma extension_normal: 
forall P M R, normal P -> normal M -> normal R -> normal (extension P M R).
Proof.
intros. unfold extension. 
repeat eapply2 nf_compound. all: unfold_op; auto. eapply2 case_normal.
Qed. 
 
Proposition extensions_by_matching:
  forall P N sigma,  matching P N sigma ->
                     forall M R, sf_red (App (extension P M R) N) (fold_left subst sigma M) .
Proof.
  intros. unfold extension. eapply succ_red. eapply2 s_red.
  eapply transitive_red. eapply preserves_app_sf_red. eapply2 case_by_matching. eval_tac. eval_tac.
Qed.



Lemma lift_rec_preserves_extension: 
  forall P M R n k, lift_rec (extension P M R) n k =
                    extension P (lift_rec M (pattern_size P +n) k) (lift_rec R n k).
Proof.
  intros. unfold extension. unfold_op. unfold lift_rec; fold lift_rec.
rewrite lift_rec_preserves_case. auto. 
Qed.


Lemma subst_rec_preserves_extension: 
  forall P M R N k, subst_rec (extension P M R) N k =
                    extension P (subst_rec M N (k+ pattern_size P)) (subst_rec R N k).
Proof.
  intros. unfold extension. unfold_op. unfold subst_rec; fold subst_rec.
rewrite subst_rec_preserves_case. auto. 
Qed.

 

Lemma maxvar_extension : 
forall P M R, maxvar (extension P M R) = max (maxvar M - (pattern_size P)) (maxvar R).
Proof.  intros. unfold extension; simpl. rewrite maxvar_case. auto. rewrite max_swap. auto. Qed. 


Lemma extension_ref: forall i M R N, sf_red (App (extension (Ref i) M R) N)  (subst_rec M N 0).
Proof.
  split_all. unfold extension. unfold_op.  eapply succ_red. eapply2 s_red.
  unfold case. unfold_op. eapply transitive_red. eapply preserves_app_sf_red.
  eapply2 star_opt_beta. eval_tac. unfold subst; split_all. eval_tac.
Qed. 

Lemma extension_op : forall o M R, sf_red (App (extension (Op o) M R) (Op o)) M.
Proof.
  intros. unfold extension, case; unfold_op.  
eapply succ_red. eapply2 s_red. 
case o. 
eapply transitive_red. eapply preserves_app_sf_red. 
eapply2 star_opt_beta. eval_tac.
unfold subst; rewrite ! subst_rec_app. 
rewrite subst_rec_closed. 2: rewrite Fop_closed; auto. 
unfold subst_rec; fold subst_rec.  insert_Ref_out. 
unfold lift, lift_rec; fold lift_rec. 
rewrite subst_rec_lift_rec; try omega. 
unfold subst; simpl. insert_Ref_out. 
unfold lift; rewrite ! lift_rec_null. 
eapply transitive_red. eapply preserves_app_sf_red. eapply2 factor_leaf. auto. eval_tac. 
Qed.


Lemma extension_op_fail : 
forall o M R N, factorable N -> Op o <> N -> sf_red (App (extension (Op o) M R) N) (App R N).
Proof.
  intros. unfold extension, case; unfold_op; unfold maxvar. 
  eapply succ_red. apply s_red. auto. auto. auto. 
generalize H0; case o; intro.
eapply transitive_red. eapply preserves_app_sf_red. eapply2 star_opt_beta. 
eval_tac. 
unfold swap; unfold_op. unfold subst; rewrite ! subst_rec_app. 
rewrite subst_rec_closed. 
2: simpl; omega. 
unfold subst_rec; fold subst_rec. insert_Ref_out. 
unfold lift; rewrite lift_rec_null.
rewrite subst_rec_lift_rec; try omega. 
rewrite ! lift_rec_null.  
inversion H. inversion H2; subst.
gen_case H0 o; gen_case H0 x; congruence. 
inversion H2; subst.  
 eapply transitive_red. eapply preserves_app_sf_red. eapply2 factor_stem. auto. 
eval_tac. eval_tac. 
 eapply transitive_red. eapply preserves_app_sf_red. eapply succ_red. 
eapply2 k_red. auto.  eval_tac.  auto. 
 eapply transitive_red. eapply preserves_app_sf_red. eapply2 factor_fork. auto. 
eval_tac. eval_tac.   
eapply transitive_red. eapply preserves_app_sf_red. eapply succ_red. eapply2 k_red. auto. 
eval_tac. auto. 
Qed. 

Lemma subst_rec_preserves_compound: 
forall (M: Tree), compound M -> forall N k, compound(subst_rec M N k).
Proof. intros M c; induction c; unfold subst; split_all. Qed. 


Lemma swapred: forall N R, sf_red (App (swap N) R) (App R N). 
Proof.
intros; unfold swap; unfold_op. eval_tac. eval_tac. 
eapply2 preserves_app_sf_red. eval_tac. eval_tac. 
Qed. 



Lemma extension_compound_op: forall P1 P2 M R o, compound (App P1 P2) -> 
sf_red (App (extension (App P1 P2) M R) (Op o)) (App R (Op o)). 
Proof. 
  intros. unfold extension, case; fold case. 
eapply succ_red. eapply2 s_red. 
assert(is_program (App P1 P2) = true \/ is_program(App P1 P2) <> true)
by decide equality. 
inversion H0. 
rewrite H1.
eapply transitive_red. eapply preserves_app_sf_red. 
eapply2 star_opt_beta. 
eval_tac. 
unfold subst; rewrite ! subst_rec_app. 
rewrite subst_rec_closed. 
2: rewrite equal_comb_closed; omega. 
unfold subst_rec; fold subst_rec. 
insert_Ref_out. unfold lift; rewrite ! lift_rec_null. 
unfold swap, subst_rec; fold subst_rec.  
assert(program (App P1 P2)) by eapply2 program_is_program.
inversion H2. simpl in H4; max_out.
rewrite ! subst_rec_lift_rec; try omega.
rewrite lift_rec_null.  
rewrite ! subst_rec_closed; auto; try omega. 
eapply transitive_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply2 unequal_op. 
eapply2 programs_are_factorable.  discriminate. auto. auto. auto. 
unfold_op; eval_tac. eval_tac. eval_tac. 
eapply2 preserves_app_sf_red;  eval_tac.
(* 1 *) 
assert(is_program (App P1 P2) = false) by 
eapply2 not_true_iff_false. 
rewrite H2.
unfold case_app.  
eapply transitive_red.  eapply preserves_app_sf_red. eapply2 star_opt_beta. eval_tac. 
 unfold subst; rewrite ! subst_rec_app. 
rewrite subst_rec_closed. 
2: rewrite Fop_closed; omega. 
unfold subst_rec; fold subst_rec. 
insert_Ref_out. unfold lift; rewrite ! lift_rec_null. 
rewrite ! subst_rec_lift_rec; try omega.
rewrite lift_rec_null.  
rewrite subst_rec_closed. 2: simpl; omega. 
case o. 
eapply transitive_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. eapply2 factor_leaf. all: auto. 
eval_tac. eval_tac. eval_tac. 
eapply transitive_red. eapply preserves_app_sf_red. 
eapply succ_red. eapply2 k_red. auto.  
eval_tac. insert_Ref_out. unfold lift; rewrite lift_rec_null.  auto.  
Qed. 

(* 
Lemma extension_normal: forall P M  R,normal M -> normal R -> normal (extension P M R).
Proof.
  induction P; unfold extension; unfold_op; intros; 
  eapply2 nf_compound; eapply2 nf_compound; eapply2 case_normal. 
Qed. 



Lemma extension_pattern_normal: 
forall P M R j, pattern_normal (pattern_size P + j) M -> pattern_normal j R -> 
pattern_normal j (extension P M R).
Proof.
  induction P; unfold extension; unfold_op; intros; 
  eapply2 pnf_compound; eapply2 pnf_compound; try (eapply2 pnf_normal; fail); 
match goal with | |- pattern_normal ?j (case ?P _) => 
replace j with (pattern_size P + j - (pattern_size P)) by omega;  
eapply2 case_pattern_normal
end. 
Qed. 

*) 
 
Lemma active_not_closed: forall P, status P = Active -> maxvar P <>0. 
Proof.
intros. assert(maxvar P = 0 \/ maxvar P <> 0) by decide equality. 
inversion H0. assert(status P = Passive) by eapply2 closed_implies_passive. 
rewrite H in *. discriminate. 
auto. 
Qed. 
 
Inductive matchfail : Tree -> Tree -> Prop :=
| matchfail_op: forall o M, factorable M -> Op o <> M -> matchfail (Op o) M
| matchfail_compound_op: forall p1 p2 o, compound (App p1 p2) -> matchfail (App p1 p2) (Op o)
| matchfail_active_op: forall p1 p2 o, status (App p1 p2) = Active -> matchfail (App p1 p2) (Op o)
| matchfail_compound_l: forall p1 p2 M1 M2, compound (App p1 p2) -> compound (App M1 M2) ->
               matchfail p1 M1 -> matchfail (App p1 p2) (App M1 M2)
| matchfail_compound_r: forall p1 p2 M1 M2 sigma1, compound (App p1 p2) -> compound (App M1 M2) ->
               matching p1 M1 sigma1 -> matchfail p2 M2 -> matchfail (App p1 p2) (App M1 M2)
| matchfail_active_l: forall p1 p2 M1 M2, status(App p1 p2) = Active -> compound (App M1 M2) ->
               matchfail p1 M1 -> matchfail (App p1 p2) (App M1 M2)
| matchfail_active_r: forall p1 p2 M1 M2 sigma1, status (App p1 p2) = Active -> compound (App M1 M2) ->
               matching p1 M1 sigma1 -> matchfail p2 M2 -> matchfail (App p1 p2) (App M1 M2)
.

Hint Constructors matchfail. 



Lemma matchfail_lift: forall P M, matchfail P M -> forall k, matchfail P (lift k M).
Proof.
  induction P; split_all; inversion H; subst; unfold lift, lift_rec; fold lift_rec. 
(* 7 *) 
  gen2_case H1 H2 M. inversion H1; split_all. inversion H0.  discriminate.  inv1 compound.
  eapply2 matchfail_op. inversion H1; split_all. inversion H0; discriminate. 
 unfold factorable. right.
  replace (App (lift_rec t 0 k) (lift_rec t0 0 k)) with (lift_rec (App t t0) 0 k) by auto. 
  eapply2 lift_rec_preserves_compound. discriminate. 
(* 6 *) 
auto. auto. 
(* 4 *) 
eapply2 matchfail_compound_l.
replace (App (lift_rec M1 0 k) (lift_rec M2 0 k)) with (lift k (App M1 M2)) by auto.
unfold lift. eapply2 lift_rec_preserves_compound.
(* 3 *) 
eapply2 matchfail_compound_r.
replace (App (lift_rec M1 0 k) (lift_rec M2 0 k)) with (lift_rec (App M1 M2) 0 k) by auto. 
eapply2 lift_rec_preserves_compound.
eapply2 matching_lift. 
(* 2 *) 
apply matchfail_active_l. auto. 
replace (App (lift_rec M1 0 k) (lift_rec M2 0 k)) with (lift_rec (App M1 M2) 0 k) by auto. 
eapply2 lift_rec_preserves_compound.
eapply2 IHP1. 
(* 1 *) 
eapply matchfail_active_r. auto. 
replace (App (lift_rec M1 0 k) (lift_rec M2 0 k)) with (lift_rec (App M1 M2) 0 k) by auto. 
eapply2 lift_rec_preserves_compound.
eapply2 matching_lift. eapply2 IHP2. 
Qed.

Lemma matchfail_unequal : 
forall P M, maxvar P = 0 -> matchfail P M -> sf_red (App (App equal_comb M) P) (App k_op i_op). 
Proof. 
induction P; split_all. inversion H0; subst. 
inversion H0; split_all; subst; split_all. 
inversion H2. inversion H1; subst. gen_case H3 o; gen_case H3 x; congruence.
(* 2 *) 
eapply2 unequal_compound_op. 
(* 1 *) 
inversion H0; subst. 
eapply2 unequal_op. unfold factorable; auto.  discriminate. 
assert(status (App P1 P2) = Passive). eapply2 closed_implies_passive. 
rewrite H1 in H4; discriminate. 
eapply transitive_red. eapply2 equal_compounds. simpl. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply2 IHP1. max_out. auto. auto. eval_tac.  eval_tac. 
assert(M1 = P1 /\ sigma1 = nil). eapply2 program_matching3. max_out. inversion H1; subst. 
eapply transitive_red. eapply2 equal_compounds. simpl. 
eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red. 
eapply2 equal_programs. eapply2 program_matching2. max_out. 
eapply2 IHP2. max_out. auto. eval_tac.
assert(status (App P1 P2) = Passive). eapply2 closed_implies_passive. 
rewrite H1 in H3; discriminate. 
assert(status (App P1 P2) = Passive). eapply2 closed_implies_passive. 
rewrite H1 in H3; discriminate. 
Qed. 


Lemma case_by_matchfail:
  forall P N R,  matchfail P N  -> forall M, sf_red (App (App (case P M) N) R) (App R N). 
Proof.
  induction P; intros; inversion H; subst.
  (* 7 *)
  unfold case; fold case. 
eapply transitive_red. eapply preserves_app_sf_red.
eapply2 star_opt_beta.  auto. 
unfold subst; rewrite ! subst_rec_app.
rewrite subst_rec_closed. 
unfold lift; rewrite ! subst_rec_lift_rec; try omega.
rewrite lift_rec_null. 
2: rewrite Fop_closed; omega. 
unfold swap, subst_rec; fold subst_rec. 
insert_Ref_out. 
rewrite ! subst_rec_closed. 
2: simpl; auto. 2: simpl; auto. 
unfold lift; rewrite lift_rec_null. 
inversion H1. inversion H0. subst.
gen_case H2 x; gen_case H2 o; congruence. 
inversion H0; subst. inversion H1; subst.
inversion H3; discriminate . 
eapply transitive_red. eapply preserves_app_sf_red. 
eapply2 factor_stem. auto. eval_tac. eval_tac.
eapply transitive_red. eapply preserves_app_sf_red. 
eapply succ_red. eapply2 k_red. auto.  eval_tac.  auto. 
eapply transitive_red. eapply preserves_app_sf_red. 
eapply2 factor_fork. auto. eval_tac. eval_tac.
eapply transitive_red. eapply preserves_app_sf_red. 
eapply succ_red. eapply2 k_red. auto.  eval_tac.  auto.
  (* 6 *) 
  unfold case; fold case.
assert(is_program (App P1 P2) = true \/ is_program(App P1 P2) <> true)
by decide equality. 
inversion H0. 
rewrite H1. 
assert(program (App P1 P2)) by eapply2 program_is_program. 
eapply transitive_red.  eapply preserves_app_sf_red. 
eapply2 star_opt_beta. auto. 
unfold subst; rewrite ! subst_rec_app. rewrite subst_rec_closed.
unfold  subst_rec; fold subst_rec.  
insert_Ref_out. 2: rewrite equal_comb_closed; omega. 
unfold lift; rewrite subst_rec_lift_rec; try omega. rewrite ! lift_rec_null.
replace (subst_rec (swap (Ref 0)) (Op o) 0) 
with  (swap (Op o)) by (unfold swap; unfold_op; unfold subst_rec; auto). 
rewrite ! subst_rec_closed. 
2: unfold_op; auto.  
eapply transitive_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply2 unequal_op. 
eapply2 programs_are_factorable.  discriminate. auto. auto. auto. 
unfold_op; eval_tac. eval_tac. eval_tac.  
eapply2 preserves_app_sf_red;  eval_tac.
inversion H2. simpl in H5; max_out; omega. 
inversion H2; simpl in H5; max_out; omega. 
(* 6 *) 
assert(is_program (App P1 P2) = false) by 
eapply2 not_true_iff_false. 
rewrite H2. 
unfold case_app.
eapply transitive_red. eapply preserves_app_sf_red. 
eapply2 star_opt_beta. auto. 
unfold subst; rewrite ! subst_rec_app.
rewrite subst_rec_closed. 
unfold lift; rewrite ! subst_rec_lift_rec; try omega.
rewrite lift_rec_null. 
2: rewrite Fop_closed; omega. 
unfold swap, subst_rec; fold subst_rec. 
insert_Ref_out. 
rewrite ! subst_rec_closed. 
2: simpl; auto. 2: simpl; auto. 
unfold lift; rewrite lift_rec_null. 
case o.
eapply transitive_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply2 factor_leaf.  auto. auto. 
 eval_tac. eval_tac.  eval_tac.
eapply transitive_red. eapply preserves_app_sf_red. 
   eval_tac. eval_tac. auto. 
(* 5 *) 
unfold case; fold case.
assert(is_program (App P1 P2) = true \/ is_program(App P1 P2) <> true)
by decide equality. 
inversion H0. 
assert(program (App P1 P2)) by eapply2 program_is_program.
inversion H2. 
assert(status (App P1 P2) = Passive) by eapply2 closed_implies_passive.
rewrite H6 in H3; discriminate.  
(* 5 *) 
assert(is_program (App P1 P2) = false) by 
eapply2 not_true_iff_false. 
rewrite H2. 
unfold case_app.  eapply transitive_red. eapply preserves_app_sf_red. 
eapply2 star_opt_beta. auto. 
unfold subst; rewrite ! subst_rec_app.
rewrite subst_rec_closed. 
unfold lift; rewrite ! subst_rec_lift_rec; try omega.
rewrite lift_rec_null. 
2: rewrite Fop_closed; omega. 
unfold swap, subst_rec; fold subst_rec. 
insert_Ref_out. 
rewrite ! subst_rec_closed. 
2: simpl; auto. 2: simpl; auto. 
unfold lift; rewrite lift_rec_null. 
case o.
eapply transitive_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply2 factor_leaf.  auto. auto. 
 eval_tac. eval_tac.  eval_tac.
eapply transitive_red. eapply preserves_app_sf_red. 
   eval_tac. eval_tac. auto. 
(* 4 *) 
  unfold case; fold case.
assert(is_program (App P1 P2) = true \/ is_program(App P1 P2) <> true)
by decide equality. 
inversion H0. 
rewrite H1. 
assert(program (App P1 P2)) by eapply2 program_is_program. 
eapply transitive_red.  eapply preserves_app_sf_red. 
eapply2 star_opt_beta. auto. 
unfold subst; rewrite ! subst_rec_app. rewrite subst_rec_closed. 
unfold subst_rec; fold subst_rec. insert_Ref_out. 2: rewrite equal_comb_closed; omega. 
unfold lift; rewrite subst_rec_lift_rec; try omega. rewrite ! lift_rec_null.
replace (subst_rec (swap (Ref 0)) (App M1 M2) 0)
with (swap (App M1 M2))
by (unfold swap; unfold_op; unfold subst_rec; fold subst_rec; 
insert_Ref_out; unfold lift; rewrite lift_rec_null; auto). 
rewrite ! subst_rec_closed. 
2: unfold_op; auto.  
eapply transitive_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply2 equal_compounds. auto. auto. auto.  simpl. 
eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red. 
eapply preserves_app_sf_red.  eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply2 matchfail_unequal. inversion H4.  simpl in H7; max_out. auto. auto. auto. auto. auto. 
eval_tac. eval_tac. eval_tac. eval_tac. 
eapply2 preserves_app_sf_red; eval_tac. 
inversion H4; simpl in H7; max_out; omega. 
inversion H4; simpl in H7; max_out; omega. 
assert(is_program (App P1 P2) = false) by 
eapply2 not_true_iff_false. 
rewrite H4. 
unfold case_app.
eapply transitive_red.  eapply preserves_app_sf_red. 
eapply2 star_opt_beta. auto. 
unfold subst; rewrite ! subst_rec_app. rewrite subst_rec_closed. 
unfold subst_rec; fold subst_rec. insert_Ref_out. 
2: rewrite Fop_closed; omega. 
unfold lift; rewrite subst_rec_lift_rec; try omega. rewrite ! lift_rec_null.
replace (subst_rec (swap (Ref 0)) (App M1 M2) 0)
with (swap (App M1 M2))
by (unfold swap; unfold_op; unfold subst_rec; fold subst_rec; 
insert_Ref_out; unfold lift; rewrite lift_rec_null; auto). 
rewrite ! subst_rec_closed. 
2: unfold_op; auto.
(* 4 *) 
inversion H3; subst.   
eapply transitive_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red.
eapply2 factor_stem.
auto. auto.  
eapply transitive_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red.
 eapply star_opt_beta2.  auto. auto.
unfold subst; rewrite ! subst_rec_app. 
unfold lift; rewrite ! subst_rec_lift_rec; try omega. rewrite ! lift_rec_null.
unfold subst_rec; fold subst_rec. insert_Ref_out. unfold_op. 
unfold subst_rec; fold subst_rec. insert_Ref_out.
unfold lift;  rewrite ! lift_rec_null. 
rewrite ! subst_rec_lift_rec; try omega.
rewrite ! lift_rec_null.   
eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red. 
eapply preserves_app_sf_red.  eapply preserves_app_sf_red. 
eapply2 IHP1. auto. auto. auto. auto. eval_tac. eval_tac. eval_tac. 
eapply transitive_red. eapply preserves_app_sf_red. 
eapply succ_red. eapply2 k_red.  auto. eval_tac.  auto. 
(* 4 *) 
eapply transitive_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red.
eapply2 factor_fork.
auto. auto.  
eapply transitive_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red.
 eapply star_opt_beta2.  auto. auto.
unfold subst; rewrite ! subst_rec_app. 
unfold lift; rewrite ! subst_rec_lift_rec; try omega. rewrite ! lift_rec_null.
unfold subst_rec; fold subst_rec. insert_Ref_out. unfold_op. 
unfold subst_rec; fold subst_rec. insert_Ref_out.
unfold lift;  rewrite ! lift_rec_null. 
rewrite ! subst_rec_lift_rec; try omega.
rewrite ! lift_rec_null.   
eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red. 
eapply preserves_app_sf_red.  eapply preserves_app_sf_red. 
eapply2 IHP1. auto. auto. auto. auto. eval_tac. eval_tac. eval_tac. 
eapply transitive_red. eapply preserves_app_sf_red. 
eapply succ_red. eapply2 k_red.  auto. eval_tac.  auto.
(* 3 *) 
  unfold case; fold case.
assert(is_program (App P1 P2) = true \/ is_program(App P1 P2) <> true)
by decide equality. 
inversion H0. 
rewrite H1. 
assert(program (App P1 P2)) by eapply2 program_is_program. 
eapply transitive_red.  eapply preserves_app_sf_red. 
eapply2 star_opt_beta. auto. 
unfold subst; rewrite ! subst_rec_app. rewrite subst_rec_closed. 
unfold subst_rec; fold subst_rec. insert_Ref_out. 2: rewrite equal_comb_closed; omega. 
unfold lift; rewrite subst_rec_lift_rec; try omega. rewrite ! lift_rec_null.
replace (subst_rec (swap (Ref 0)) (App M1 M2) 0)
with (swap (App M1 M2))
by (unfold swap; unfold_op; unfold subst_rec; fold subst_rec; 
insert_Ref_out; unfold lift; rewrite lift_rec_null; auto). 
rewrite ! subst_rec_closed. 
2: unfold_op; auto.   
eapply transitive_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply2 equal_compounds. auto. auto. auto.  simpl. 
eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red. 
eapply preserves_app_sf_red.  eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
assert(M1 = P1 /\ sigma1 = nil). eapply2 program_matching3. inversion H5. simpl in *; max_out.
 inversion H7; subst. 
eapply2 equal_programs. eapply2 (program_app P1 P2).
eapply2 matchfail_unequal. inversion H5; simpl in *; max_out. 
auto. auto. auto.  auto. eval_tac. eval_tac. eval_tac.  
eapply2 preserves_app_sf_red; eval_tac. 
inversion H5; simpl in *; max_out; omega. 
inversion H5; simpl in *; max_out; omega. 
assert(is_program (App P1 P2) = false) by 
eapply2 not_true_iff_false.
rewrite H5. 
(* 3 *)  
unfold case_app.
eapply transitive_red.  eapply preserves_app_sf_red. 
eapply2 star_opt_beta. auto. 
unfold subst; rewrite ! subst_rec_app. rewrite subst_rec_closed. 
unfold subst_rec; fold subst_rec. insert_Ref_out. 
2: rewrite Fop_closed; omega. 
unfold lift; rewrite subst_rec_lift_rec; try omega. rewrite ! lift_rec_null.
replace (subst_rec (swap (Ref 0)) (App M1 M2) 0)
with (swap (App M1 M2))
by (unfold swap; unfold_op; unfold subst_rec; fold subst_rec; 
insert_Ref_out; unfold lift; rewrite lift_rec_null; auto). 
rewrite ! subst_rec_closed. 
2: unfold_op; auto.
(* 3 *) 
inversion H3; subst.   
eapply transitive_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red.
eapply2 factor_stem.
auto. auto.  
eapply transitive_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red.
 eapply star_opt_beta2.  auto. auto.
unfold subst; rewrite ! subst_rec_app. 
unfold lift; rewrite ! subst_rec_lift_rec; try omega. rewrite ! lift_rec_null.
unfold subst_rec; fold subst_rec. insert_Ref_out. unfold_op. 
unfold subst_rec; fold subst_rec. insert_Ref_out.
unfold lift;  rewrite ! lift_rec_null. 
rewrite ! subst_rec_lift_rec; try omega.
rewrite ! lift_rec_null.   
eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red. 
eapply preserves_app_sf_red.  eapply preserves_app_sf_red. eapply preserves_app_sf_red.
eapply2 case_by_matching.  auto. auto. auto. auto. auto.  
eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red. 
eapply preserves_app_sf_red.  eapply preserves_app_sf_red. eapply succ_red. eapply2 k_red.
auto. auto. auto. auto. auto.  
rewrite ! fold_subst_list.
eapply transitive_red. eapply list_subst_preserves_sf_red. 
eapply preserves_app_sf_red. eapply preserves_app_sf_red.
eapply IHP2. eapply2 matchfail_lift. 
unfold lift; simpl. auto. auto.  unfold lift; simpl. 
eapply transitive_red. eapply list_subst_preserves_sf_red. eval_tac. 
eapply transitive_red. eapply list_subst_preserves_sf_red. eval_tac. 
repeat rewrite list_subst_preserves_app. repeat rewrite list_subst_preserves_op. eval_tac. 
 eapply transitive_red. eapply preserves_app_sf_red. eapply succ_red.  eapply2 k_red. auto. 
eapply succ_red.  eapply2 k_red. auto.   
replace(lift_rec R 0 (length sigma1)) with (lift (length sigma1) R) by auto. 
replace(lift_rec M2 0 (length sigma1)) with (lift (length sigma1) M2) by auto.
eapply2 preserves_app_sf_red. 
 rewrite list_subst_lift; auto.  rewrite ! list_subst_lift; auto.
(* 3 *) 
eapply transitive_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red.
eapply2 factor_fork.
auto. auto.  
eapply transitive_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red.
 eapply star_opt_beta2.  auto. auto.
unfold subst; rewrite ! subst_rec_app. 
unfold lift; rewrite ! subst_rec_lift_rec; try omega. rewrite ! lift_rec_null.
unfold subst_rec; fold subst_rec. insert_Ref_out. unfold_op. 
unfold subst_rec; fold subst_rec. insert_Ref_out.
unfold lift;  rewrite ! lift_rec_null. 
rewrite ! subst_rec_lift_rec; try omega.
rewrite ! lift_rec_null.   
eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red. 
eapply preserves_app_sf_red.  eapply preserves_app_sf_red. eapply preserves_app_sf_red.
eapply2 case_by_matching.  auto. auto. auto. auto. auto.  
eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red. 
eapply preserves_app_sf_red.  eapply preserves_app_sf_red. eapply succ_red. eapply2 k_red.
auto. auto. auto. auto. auto.  
rewrite ! fold_subst_list.
eapply transitive_red. eapply list_subst_preserves_sf_red. 
eapply preserves_app_sf_red. eapply preserves_app_sf_red.
eapply IHP2. eapply2 matchfail_lift. 
unfold lift; simpl. auto. auto.  unfold lift; simpl. 
eapply transitive_red. eapply list_subst_preserves_sf_red. eval_tac. 
eapply transitive_red. eapply list_subst_preserves_sf_red. eval_tac. 
repeat rewrite list_subst_preserves_app. repeat rewrite list_subst_preserves_op. eval_tac. 
 eapply transitive_red. eapply preserves_app_sf_red. eapply succ_red.  eapply2 k_red. auto. 
eapply succ_red.  eapply2 k_red. auto.   
replace(lift_rec R 0 (length sigma1)) with (lift (length sigma1) R) by auto. 
replace(lift_rec M0 0 (length sigma1)) with (lift (length sigma1) M0) by auto.
replace(lift_rec M2 0 (length sigma1)) with (lift (length sigma1) M2) by auto.
eapply2 preserves_app_sf_red. 
 rewrite list_subst_lift; auto.  rewrite ! list_subst_lift; auto.
(* 2 *) 
 unfold case; fold case.
assert(is_program (App P1 P2) = true \/ is_program(App P1 P2) <> true)
by decide equality. 
inversion H0. 
rewrite H1. 
assert(program (App P1 P2)) by eapply2 program_is_program.
assert(factorable (App P1 P2)) by eapply2 programs_are_factorable. 
inversion H6; subst. inversion H7; discriminate. 
inversion H7; subst; simpl in H2; discriminate.   
assert(is_program (App P1 P2) = false) by 
eapply2 not_true_iff_false.
rewrite H4. 
(* 2 *)  
unfold case_app.
eapply transitive_red.  eapply preserves_app_sf_red. 
eapply2 star_opt_beta. auto. 
unfold subst; rewrite ! subst_rec_app. rewrite subst_rec_closed. 
unfold subst_rec; fold subst_rec. insert_Ref_out. 
2: rewrite Fop_closed; omega. 
unfold lift; rewrite subst_rec_lift_rec; try omega. rewrite ! lift_rec_null.
replace (subst_rec (swap (Ref 0)) (App M1 M2) 0)
with (swap (App M1 M2))
by (unfold swap; unfold_op; unfold subst_rec; fold subst_rec; 
insert_Ref_out; unfold lift; rewrite lift_rec_null; auto). 
rewrite ! subst_rec_closed. 
2: unfold_op; auto.
(* 2 *) 
inversion H3; subst.   
eapply transitive_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red.
eapply2 factor_stem.
auto. auto.  
eapply transitive_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red.
 eapply star_opt_beta2.  auto. auto.
unfold subst; rewrite ! subst_rec_app. 
unfold lift; rewrite ! subst_rec_lift_rec; try omega. rewrite ! lift_rec_null.
unfold subst_rec; fold subst_rec. insert_Ref_out. unfold_op. 
unfold subst_rec; fold subst_rec. insert_Ref_out.
unfold lift;  rewrite ! lift_rec_null. 
rewrite ! subst_rec_lift_rec; try omega.
rewrite ! lift_rec_null.   
eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red. 
eapply preserves_app_sf_red.  eapply preserves_app_sf_red.
eapply2 IHP1. auto. auto. auto. auto.  eval_tac. eval_tac. eval_tac. 
eapply transitive_red. eapply preserves_app_sf_red.  eapply succ_red. eapply2 k_red.
auto. eval_tac. auto. 
(* 2 *) 
eapply transitive_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red.
eapply2 factor_fork.
auto. auto.  
eapply transitive_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red.
 eapply star_opt_beta2.  auto. auto.
unfold subst; rewrite ! subst_rec_app. 
unfold lift; rewrite! subst_rec_lift_rec; try omega. rewrite ! lift_rec_null.
unfold subst_rec; fold subst_rec. insert_Ref_out. unfold_op. 
unfold subst_rec; fold subst_rec. insert_Ref_out.
unfold lift;  rewrite ! lift_rec_null. 
rewrite ! subst_rec_lift_rec; try omega.
rewrite ! lift_rec_null.   
eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red. 
eapply preserves_app_sf_red.  eapply preserves_app_sf_red.
eapply2 IHP1. auto. auto. auto. auto.  eval_tac. eval_tac. eval_tac. 
eapply transitive_red. eapply preserves_app_sf_red.  eapply succ_red. eapply2 k_red.
auto. eval_tac. auto. 
(* 1 *) 
 unfold case; fold case.
assert(is_program (App P1 P2) = true \/ is_program(App P1 P2) <> true)
by decide equality. 
inversion H0. 
rewrite H1. 
assert(program (App P1 P2)) by eapply2 program_is_program. 
assert(factorable (App P1 P2)) by eapply2 programs_are_factorable. 
inversion H7; subst. inversion H8; discriminate.  
inversion H8; subst; simpl in H2; discriminate.
(* 1 *) 
assert(is_program (App P1 P2) = false) by 
eapply2 not_true_iff_false.
rewrite H5. 
(* 3 *)  
unfold case_app.
eapply transitive_red.  eapply preserves_app_sf_red. 
eapply2 star_opt_beta. auto. 
unfold subst; rewrite ! subst_rec_app. rewrite subst_rec_closed. 
unfold subst_rec; fold subst_rec. insert_Ref_out. 
2: rewrite Fop_closed; omega. 
unfold lift; rewrite subst_rec_lift_rec; try omega. rewrite ! lift_rec_null.
replace (subst_rec (swap (Ref 0)) (App M1 M2) 0)
with (swap (App M1 M2))
by (unfold swap; unfold_op; unfold subst_rec; fold subst_rec; 
insert_Ref_out; unfold lift; rewrite lift_rec_null; auto). 
rewrite ! subst_rec_closed. 
2: unfold_op; auto.
(* 1 *) 
inversion H3; subst.   
eapply transitive_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red.
eapply2 factor_stem.
auto. auto.  
eapply transitive_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red.
 eapply star_opt_beta2.  auto. auto.
unfold subst; rewrite ! subst_rec_app. 
unfold lift; rewrite ! subst_rec_lift_rec; try omega. rewrite ! lift_rec_null.
unfold subst_rec; fold subst_rec. insert_Ref_out. unfold_op. 
unfold subst_rec; fold subst_rec. insert_Ref_out.
unfold lift;  rewrite ! lift_rec_null. 
rewrite ! subst_rec_lift_rec; try omega.
rewrite ! lift_rec_null.   
eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red. 
eapply preserves_app_sf_red.  eapply preserves_app_sf_red. eapply preserves_app_sf_red.
eapply2 case_by_matching.  auto. auto. auto. auto. auto.  
eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red. 
eapply preserves_app_sf_red.  eapply preserves_app_sf_red. eapply succ_red. eapply2 k_red.
auto. auto. auto. auto. auto.  
rewrite ! fold_subst_list.
eapply transitive_red. eapply list_subst_preserves_sf_red. 
eapply preserves_app_sf_red. eapply preserves_app_sf_red.
eapply IHP2. eapply2 matchfail_lift. 
unfold lift; simpl. auto. auto.  unfold lift; simpl. 
eapply transitive_red. eapply list_subst_preserves_sf_red. eval_tac. 
eapply transitive_red. eapply list_subst_preserves_sf_red. eval_tac. 
repeat rewrite list_subst_preserves_app. repeat rewrite list_subst_preserves_op. eval_tac. 
 eapply transitive_red. eapply preserves_app_sf_red. eapply succ_red.  eapply2 k_red. auto. 
eapply succ_red.  eapply2 k_red. auto.   
replace(lift_rec R 0 (length sigma1)) with (lift (length sigma1) R) by auto. 
replace(lift_rec M2 0 (length sigma1)) with (lift (length sigma1) M2) by auto.
eapply2 preserves_app_sf_red. 
 rewrite list_subst_lift; auto.  rewrite ! list_subst_lift; auto.
(* 1 *) 
eapply transitive_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red.
eapply2 factor_fork.
auto. auto.  
eapply transitive_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red.
 eapply star_opt_beta2.  auto. auto.
unfold subst; rewrite ! subst_rec_app. 
unfold lift; rewrite ! subst_rec_lift_rec; try omega. rewrite ! lift_rec_null.
unfold subst_rec; fold subst_rec. insert_Ref_out. unfold_op. 
unfold subst_rec; fold subst_rec. insert_Ref_out.
unfold lift;  rewrite ! lift_rec_null. 
rewrite ! subst_rec_lift_rec; try omega.
rewrite ! lift_rec_null.   
eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red. 
eapply preserves_app_sf_red.  eapply preserves_app_sf_red. eapply preserves_app_sf_red.
eapply2 case_by_matching.  auto. auto. auto. auto. auto.  
eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red. 
eapply preserves_app_sf_red.  eapply preserves_app_sf_red. eapply succ_red. eapply2 k_red.
auto. auto. auto. auto. auto.  
rewrite ! fold_subst_list.
eapply transitive_red. eapply list_subst_preserves_sf_red. 
eapply preserves_app_sf_red. eapply preserves_app_sf_red.
eapply IHP2. eapply2 matchfail_lift. 
unfold lift; simpl. auto. auto.  unfold lift; simpl. 
eapply transitive_red. eapply list_subst_preserves_sf_red. eval_tac. 
eapply transitive_red. eapply list_subst_preserves_sf_red. eval_tac. 
repeat rewrite list_subst_preserves_app. repeat rewrite list_subst_preserves_op. eval_tac. 
 eapply transitive_red. eapply preserves_app_sf_red. eapply succ_red.  eapply2 k_red. auto. 
eapply succ_red.  eapply2 k_red. auto.   
replace(lift_rec R 0 (length sigma1)) with (lift (length sigma1) R) by auto. 
replace(lift_rec M0 0 (length sigma1)) with (lift (length sigma1) M0) by auto.
replace(lift_rec M2 0 (length sigma1)) with (lift (length sigma1) M2) by auto.
eapply2 preserves_app_sf_red. 
 rewrite list_subst_lift; auto.  rewrite ! list_subst_lift; auto.
Qed. 



Proposition extensions_by_matchfail:
  forall P N,  matchfail P N -> forall M R, sf_red (App (extension P M R) N) (App R N).
Proof.
  intros. unfold extension. eval_tac. 
  eapply transitive_red. eapply2 case_by_matchfail.  
  eapply transitive_red. eapply preserves_app_sf_red. eapply succ_red. eapply2 k_red. auto. 
auto. auto. 
Qed. 

Lemma match_program: 
forall P M, normal P -> program M -> matchfail P M \/ exists sigma, matching P M sigma.
Proof. 
induction P; split_all. 
(* 3 *) 
right. exist (cons M nil). 
(* 2 *) 
gen_case H0 M. inversion H0; split_all.  simpl in *; discriminate. 
case o; case o0; split_all. 
right; eauto. 
left; auto; eapply2 matchfail_op. eapply2 programs_are_factorable. discriminate. 
(* 1 *) 
gen_case H0 M; inversion H0; auto. 
(* 2 *) 
simpl in *; discriminate. 
(* 2 *) 
inversion H; subst; left; auto. 
(* 1 *) 
inversion H; subst. inversion H1; subst.
(* 3 *)  
assert(status (App t t0) = Passive) by eapply2 closed_implies_passive. 
rewrite H3 in H10; discriminate. 
(* 2 *) 
simpl in H2; max_out. 
assert(matchfail P1 t \/ (exists sigma : list Tree, matching P1 t sigma)).
eapply2 IHP1. unfold program; split_all. 
assert(matchfail P2 t0 \/ (exists sigma : list Tree, matching P2 t0 sigma)). 
eapply2 IHP2. unfold program; split_all. 
(* 2 *) 
inversion H2. left; eapply2 matchfail_active_l.
inversion H11. 
inversion H12. left; eapply2 matchfail_active_r.
inversion H12; inversion H13. 
right; exist (map (lift (length x)) x0++x). 
(* 1 *) 
inversion H1; subst.
(* 3 *)  
assert(status (App t t0) = Passive) by eapply2 closed_implies_passive. 
rewrite H3 in H10; discriminate. 
(* 1 *) 
simpl in H2; max_out. 
assert(matchfail P1 t \/ (exists sigma : list Tree, matching P1 t sigma)).
eapply2 IHP1. unfold program; split_all. 
assert(matchfail P2 t0 \/ (exists sigma : list Tree, matching P2 t0 sigma)). 
eapply2 IHP2. unfold program; split_all. 
(* 2 *) 
inversion H2. left; eapply2 matchfail_compound_l. 
inversion H11; inversion H12; subst. left; eapply2 matchfail_compound_r. 
inversion H13; subst. right; eauto.
Qed. 


Lemma match_app_comb: 
forall P1 P2 Q1 Q2 sigma1 sigma2, matching P1 Q1 sigma1 -> matching P2 Q2 sigma2 -> 
matching (app_comb P1 P2) (app_comb Q1 Q2) (app (map (lift (length (nil: list Tree))) 
((map (lift (length sigma2)) sigma1) ++ sigma2)) nil).
Proof.
intros; unfold app_comb. 
eapply2 match_app.
eapply2 program_matching. 
unfold_op; split; auto. repeat eapply2 nf_compound.  
eapply2 match_app.
replace sigma2 with (map (lift (length (nil: list Tree))) sigma2 ++ nil) .
2: simpl; rewrite map_lift0; auto. 2: eapply2 app_nil_r.  
eapply2 match_app.
replace sigma2 with (map (lift (length (nil: list Tree))) sigma2 ++ nil) .
2: simpl; rewrite map_lift0; auto. 2: eapply2 app_nil_r.  
eapply2 match_app.
replace sigma2 with (map (lift (length (nil: list Tree))) sigma2 ++ nil) .
2: simpl; rewrite map_lift0; auto. 2: eapply2 app_nil_r.  
unfold_op; eapply2 match_app.
eapply2 program_matching.  split; auto. 
replace sigma1 with (map (lift (length (nil: list Tree))) sigma1 ++ nil) .
2: simpl; rewrite map_lift0; auto. 2: eapply2 app_nil_r.  
unfold_op; eapply2 match_app.
eapply2 program_matching.  split; auto.
Qed.
 


 
Lemma matchfail_app_comb_r : 
forall P1 P2 Q1 Q2, matchfail P2 Q2 -> matchfail (app_comb P1 P2) (app_comb Q1 Q2).
Proof.
intros; unfold app_comb. 
eapply2 matchfail_compound_r.
unfold_op; eapply2 program_matching.
unfold program; split; auto. repeat eapply2 nf_compound.   
unfold_op; eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
Qed. 

Lemma matchfail_app_comb_l : 
forall P1 P2 Q1 Q2 sigma, matching P2 Q2 sigma -> matchfail P1 Q1 -> matchfail (app_comb P1 P2) (app_comb Q1 Q2).
Proof.
intros; unfold app_comb. 
eapply2 matchfail_compound_r.
unfold_op; eapply2 program_matching.
unfold program; split; auto. repeat eapply2 nf_compound.   
unfold_op; eapply2 matchfail_compound_r. 
repeat eapply2 match_app. 
Qed. 
