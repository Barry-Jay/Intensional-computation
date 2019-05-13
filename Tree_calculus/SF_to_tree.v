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
(*                    SF_to_tree.v                                    *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)


Require Import Omega Max Bool List.
Require Import IntensionalLib.SF_calculus.Test.  
Require Import IntensionalLib.SF_calculus.General.  
Require Import IntensionalLib.Tree_calculus.SF_Terms.  
Require Import IntensionalLib.Tree_calculus.SF_reduction.  
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

(* translation of Sop *) 

Definition trans_S0 := star_opt (star_opt (star_opt (App (App (Ref 2) (Ref 0)) (App (Ref 1) (Ref 0))))).
Definition trans_S := A31 trans_S0. 

Lemma trans_S_red: forall M N P, sf_red (App (App (App trans_S M) N) P) (App (App M P) (App N P)).
Proof.
intros; unfold trans_S.  
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red.
eapply2 A3_red2. auto. auto. 
eapply transitive_red. eapply preserves_app_sf_red. eapply2 A3_red3. auto.
eapply transitive_red. eapply2 A3_red4.
eval_tac. eval_tac. eval_tac. eval_tac. eval_tac. eval_tac. eval_tac. 
eapply2 preserves_app_sf_red.
eapply2 preserves_app_sf_red.  eval_tac.
Qed. 




(* translation of Fop *) 


Definition trans_F0 := 
extension  (A31 (Ref 0)) k_op (
extension (A33 (Ref 0) (Ref 1) (Ref 2)) (App k_op (star_opt (App (App (Ref 0) (App (A31 (Ref 1)) (Ref 2))) (Ref 3)))) (
extension (A32 (Ref 0) (Ref 1)) (App k_op (star_opt (App (App (Ref 0) (App (A_k 1) (Ref 1))) (Ref 2)))) (
i_op)))
.


Definition trans_F := A31 trans_F0. 


Lemma trans_F_op_red: 
forall M N P, sf_red (App (App (App trans_F (A31 P)) M) N) M.
Proof.
intros; unfold trans_F.
eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red.  
eapply2 A3_red2. all: auto. 
eapply transitive_red. eapply preserves_app_sf_red.  eapply2 A3_red3. auto.
eapply transitive_red. eapply2 A3_red4. 
(* 1 *) 
unfold trans_F0.  
eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red.  
2: auto. 2: auto. 
eapply2 extensions_by_matching.
unfold A31. 
unfold app_comb at 1 3. 
rewrite star_opt_occurs_true.
2: cbv; auto. 2: discriminate. 
rewrite (star_opt_occurs_true (App (Op Node) (App (Op Node) i_op))). 
2: cbv; auto. 2: omega. 2: discriminate.  
eapply2 match_app. 2: unfold_op; repeat eapply2 match_app. all: unfold_op; auto. 
eapply2 match_app. eapply2 match_app.
rewrite star_opt_occurs_true.
2: cbv; auto. 2: discriminate. 
rewrite (star_opt_occurs_true (App (Op Node)
           (App (Op Node)
              (App (App (Op Node) (Op Node))
                 (App
                    (App (Op Node)
                       (App (Op Node)
                          (App (App (Op Node) (App (Op Node) (Op Node)))
                             (App (Op Node) (Op Node)))))
                    (App
                       (App (Op Node)
                          (App (Op Node)
                             (App (App (Op Node) (Op Node)) (Ref 0))))
                       (App (App (Op Node) (Op Node)) (lift 1 P)))))))). 
2: cbv; omega. 2: discriminate. 
eapply2 match_app. eapply2 match_app. eapply2 match_app.
repeat eapply2 match_app. 
all: unfold_op; auto.
(* 2 *)
rewrite star_opt_occurs_true.
2: cbv; auto. 2: discriminate. 
rewrite ! (star_opt_occurs_true (Op Node)).
2: cbv; omega. 2:discriminate. 
eapply2 match_app. 2: unfold_op; repeat eapply2 match_app. all: unfold_op; auto. 
eapply2 match_app. eapply2 match_app.
eapply2 match_app. eapply2 match_app.
eapply2 match_app. eapply2 match_app.
unfold occurs. 
 simpl. 
eapply2 match_app. eapply2 match_app. eapply2 match_app.
eapply2 match_app. eapply2 match_app. eapply2 match_app.
eapply2 match_app. eapply2 match_app. 
all: cycle 1. 
unfold_op; repeat eapply2 match_app.
unfold_op; repeat eapply2 match_app.
simpl. unfold_op; repeat eapply2 match_app.
unfold_op; repeat eapply2 match_app.
left; unfold_op; auto. 
all: unfold_op; auto. 
simpl. omega. discriminate. discriminate. 
(* 2 *) 
unfold length; fold length. 
rewrite ! map_lift0. 
unfold app, map, fold_left.
unfold_op; unfold subst.  simpl. 
rewrite ! app_nil_r. 
2: instantiate(1:= P::nil). 
simpl. eval_tac. 
(* 1 *) 
case P. 
(* 4 *) 
intros. unfold lift, lift_rec. relocate_lt. unfold plus, eqnat. 
repeat eapply2 match_app. 
(* 3 *) 
replace (Ref n :: nil) with ((map (lift (length (nil: list Tree))) (Ref n :: nil)) ++ nil).  
repeat eapply2 match_app.
eapply2 program_matching. unfold program; auto. 
unfold subst; simpl. insert_Ref_out.  
replace (Ref n :: nil) with ((map (lift (length (nil: list Tree))) (Ref n :: nil)) ++ nil).  
repeat eapply2 match_app.
eapply2 program_matching. unfold program; auto.
simpl. unfold lift; simpl. relocate_lt. auto. 
simpl. unfold lift; simpl. relocate_lt. auto. 
(* 2 *) 
intro; unfold lift, lift_rec. relocate_lt.  unfold plus. 
unfold subst; simpl.  insert_Ref_out.  simpl. 
replace (Op o :: nil) with ((map (lift (length (nil: list Tree))) (Op o :: nil)) ++ nil).  
repeat eapply2 match_app.
eapply2 program_matching. unfold program; auto. 
replace (Op o :: nil) with ((map (lift (length (nil: list Tree))) (Op o :: nil)) ++ nil).  
repeat eapply2 match_app.
eapply2 program_matching. unfold program; auto. 
simpl. unfold lift; simpl. auto. 
simpl. unfold lift; simpl. auto.
(* 1 *)
intro; unfold lift, lift_rec; fold lift_rec. fold occurs. 
intro. rewrite ! occurs_lift_rec_zero. simpl.  relocate_lt. unfold plus. 
unfold subst, subst_rec; fold subst_rec. 
rewrite ! subst_rec_lift_rec; try omega. insert_Ref_out. 
rewrite ! lift_rec_null. 
replace (App t t0 :: nil) with ((map (lift (length (nil: list Tree))) (App t t0 :: nil)) ++ nil).
eapply2 match_app.   
eapply2 program_matching. unfold program; auto. 
replace (App t t0 :: nil) with ((map (lift (length (nil: list Tree))) (App t t0 :: nil)) ++ nil).
eapply2 match_app.   
eapply2 program_matching. unfold program; auto. 
simpl. unfold lift; simpl. rewrite ! lift_rec_null. auto. 
simpl. unfold lift; simpl. rewrite ! lift_rec_null.  auto.
Qed. 


Lemma trans_F2_red: forall P Q M N, sf_red (App (App (App trans_F (A32 P Q)) M) N) (App (App N (App (A_k 1) P)) Q).
Proof.
intros. 
eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red.  
eapply2 A3_red2. all: auto. 
eapply transitive_red. eapply preserves_app_sf_red.  eapply2 A3_red3. auto.
eapply transitive_red. eapply2 A3_red4. 
(* 1 *) 
unfold trans_F0.  
eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red.  
2: auto. 2: auto. 
eapply2 extensions_by_matchfail.
unfold A31, A32. 
unfold app_comb at 1. 
rewrite star_opt_occurs_true.
2: cbv; auto. 2: discriminate.
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r. 
rewrite star_opt_occurs_true. 
eapply2 matchfail_compound_l. unfold_op. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r. 
rewrite star_opt_occurs_false. 
eapply2 matchfail_compound_op. unfold_op; auto.  
cbv; auto. cbv; auto. discriminate. 
(* 1 *) 
eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red.  
2: auto. 2: auto.
eapply2 extensions_by_matchfail. 
unfold A32, A33. eapply2 matchfail_app_comb_l.
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r.
unfold occurs. unfold_op.  
simpl. 
eapply2 matchfail_compound_l.
(* 1 *)  
eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red.  
2: auto. 2: auto.
eapply2 extensions_by_matching. 
unfold A32. eapply2 match_app_comb.
eapply2 program_matching.
unfold_op; split; auto.
repeat eapply2 star_opt_normal. 
repeat eapply2 nf_compound. 
eapply2 match_app_comb. 
(* 1 *) 
unfold length; fold length. 
rewrite ! map_lift0. 
unfold app, map, fold_left.
unfold_op; unfold subst.  subst_tac.
rewrite ! subst_rec_preserves_star_opt.
eapply transitive_red. eapply preserves_app_sf_red. 
eapply succ_red. eapply k_red. auto. auto. auto. 
eapply transitive_red. eapply star_opt_beta.
unfold subst. rewrite ! subst_rec_app. rewrite ! subst_rec_ref.
insert_Ref_out. rewrite ! subst_rec_ref.
insert_Ref_out. rewrite ! subst_rec_ref.
insert_Ref_out. 
rewrite ! (subst_rec_closed (A_k 1)).
2: cbv; auto. 
unfold lift; rewrite ! lift_rec_null. rewrite ! lift_rec_lift_rec; try omega. 
subst_tac. auto. 
Qed. 
 
 
Lemma subst_rec_preserves_A31: forall M N k, subst_rec (A31 M) N k = A31 (subst_rec M N k).
Proof.
intros; unfold A31. rewrite ! subst_rec_preserves_star_opt. 
rewrite ! subst_rec_preserves_app_comb. 
rewrite subst_rec_closed.  2: cbv; omega. rewrite subst_rec_ref. insert_Ref_out.  
unfold lift. replace (S k) with (1+k) by omega. rewrite subst_rec_lift_rec1; auto. omega. 
Qed. 
  



Lemma trans_F3_red: forall P Q R M N, sf_red (App (App (App trans_F (A33 P Q R)) M) N) (App (App N (App (A31 P) Q)) R).
Proof.
intros. 
eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red.  
eapply2 A3_red2. all: auto. 
eapply transitive_red. eapply preserves_app_sf_red.  eapply2 A3_red3. auto.
eapply transitive_red. eapply2 A3_red4. 
(* 1 *) 
unfold trans_F0.  
eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red.  
2: auto. 2: auto. 
eapply2 extensions_by_matchfail.
unfold A31, A33. 
unfold app_comb at 1. 
rewrite star_opt_occurs_true.
2: cbv; auto. 2: discriminate.
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r. 
rewrite star_opt_occurs_true. 
eapply2 matchfail_compound_l. unfold_op. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r. 
rewrite star_opt_occurs_false. 
eapply2 matchfail_compound_op. unfold_op; auto.  
cbv; auto. cbv; auto. discriminate. 
(* 1 *) 
eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red.  
2: auto. 2: auto.
eapply2 extensions_by_matching. 
(* 2 *) 
unfold A33. eapply2 match_app_comb. eapply2 match_app_comb. 
(* 1 *) 
unfold length; fold length. 
rewrite ! map_lift0. 
unfold app, map, fold_left.
unfold_op; unfold subst.
rewrite ! subst_rec_app. rewrite ! subst_rec_op. 
rewrite ! subst_rec_preserves_star_opt. 
rewrite ! subst_rec_app. rewrite ! subst_rec_ref. insert_Ref_out.
eapply transitive_red. 
eapply preserves_app_sf_red. eapply succ_red. eapply2 k_red. auto. auto. 
eapply transitive_red.  eapply2 star_opt_beta. 
unfold subst.
rewrite ! subst_rec_app.
rewrite ! subst_rec_preserves_A31. 
 rewrite ! subst_rec_ref. insert_Ref_out.
 rewrite ! subst_rec_ref. insert_Ref_out.
 rewrite ! subst_rec_ref. insert_Ref_out.
unfold lift. rewrite ! lift_rec_lift_rec; try omega. 
unfold plus. 
rewrite ! subst_rec_lift_rec; try omega. 
 rewrite ! lift_rec_null. 
auto. 
Qed. 
  
 
Definition op_to_tree o := 
match o with 
| Sop => trans_S
| Fop => trans_F
end.
 

Fixpoint sf_to_tree M := 
match M with 
| SF_Terms.Op o => op_to_tree o
| SF_Terms.App M1 M2 => App (sf_to_tree M1) (sf_to_tree M2)
end.


Lemma sf_to_tree_closed: forall M, maxvar (sf_to_tree M) = 0. 
Proof. 
induction M; split_all.
case o; unfold op_to_tree. 
(* 3 *) 
unfold trans_S. unfold_op; simpl; auto. 
(* 2 *) 
unfold trans_F; unfold_op. unfold A31. rewrite maxvar_star_opt. rewrite ! maxvar_app_comb.
replace (maxvar (lift 1 trans_F0)) with 0. 
cbv; auto.
unfold trans_F0. 
unfold lift; rewrite ! lift_rec_preserves_extension. rewrite ! maxvar_extension.
cbv; auto.   
(* 1 *) 
rewrite IHM1; rewrite IHM2; auto. 
Qed. 
  



Theorem translation_preserves_sf_reduction:
forall M N, SF_reduction.sf_red1 M N -> sf_red (sf_to_tree M) (sf_to_tree N). 
Proof. 
induction M; split_all; inversion H; subst; simpl; auto.
(* 3 *) 
cut(sf_red
         (sf_to_tree (SF_Terms.App (SF_Terms.App (SF_Terms.Op Sop) M) N0))
         (sf_to_tree (SF_Terms.App (SF_Terms.App (SF_Terms.Op Sop) M') N'))). 
2: eapply2 IHM1.
simpl. intro.  
eapply transitive_red. 
eapply preserves_app_sf_red. 
eexact H0. eapply2 IHM2. 
eapply2 trans_S_red.
(* 2 *) 
gen_case IHM1 o. 
(* 3 *) 
eapply transitive_red.
eapply preserves_app_sf_red.
eapply2 (IHM1  (SF_Terms.App
            (SF_Terms.App (SF_Terms.Op SF_Terms.Fop) (SF_Terms.Op Sop)) N) ).
auto. 
simpl. eapply2 trans_F_op_red.
(* 2 *) 
eapply transitive_red.
eapply preserves_app_sf_red.
eapply2 (IHM1  (SF_Terms.App
            (SF_Terms.App (SF_Terms.Op SF_Terms.Fop) (SF_Terms.Op SF_Terms.Fop)) N) ).
auto. 
simpl. eapply2 trans_F_op_red.
(* 1 *) 
eapply transitive_red.
eapply preserves_app_sf_red.
eapply2 (IHM1 (SF_Terms.App (SF_Terms.App (SF_Terms.Op SF_Terms.Fop) P') M)).
eapply2 (IHM2 N'). 
simpl.
assert(SF_reduction.compound P').
eapply2 (SF_reduction.preserves_compound_sf_red).
eapply2 SF_Tactics.succ_red.
(* 1 *) 
clear - H0.
inversion H0; subst; simpl. 
(* 4 *) 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red.
auto. eapply2 A3_red2. auto. auto. 
eapply transitive_red. eapply2 trans_F2_red. 
eapply2 preserves_app_sf_red. 
eapply2 preserves_app_sf_red.
apply A3_red1. 
(* 3 *) 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red.
auto. eapply preserves_app_sf_red. eapply2 A3_red2. auto. auto. auto. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red.
auto. eapply2 A3_red3. auto. auto. 
eapply transitive_red. eapply2 trans_F3_red. eapply2 zero_red. 
(* 2 *) 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red.
auto. eapply2 A3_red2. auto. auto. 
eapply transitive_red. eapply2 trans_F2_red. 
eapply2 preserves_app_sf_red. 
eapply2 preserves_app_sf_red. 
eapply2 A3_red1. 
(* 1 *) 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red.
auto. eapply preserves_app_sf_red. eapply2 A3_red2. auto. auto. auto. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red.
auto. eapply2 A3_red3. auto. auto. 
eapply transitive_red. eapply2 trans_F3_red. eapply2 zero_red. 
Qed. 

