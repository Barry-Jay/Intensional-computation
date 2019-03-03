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
(*                         Wave_Factor.v                              *)
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


Definition closed M := maxvar M <= 0. 


Definition tree_test is0 is1 is2 := 
star_opt (App (App (App (App (App (Op Node) (Ref 0)) 
                   (App k_op (App k_op is0)))
              (App k_op (App k_op (App k_op (App k_op is2)))))
    (App k_op i_op))
is1).

Lemma tree_test_zero : 
forall is0 is1 is2, closed is0 -> 
sf_red (App (tree_test is0 is1 is2) (Op Node)) is0.
Proof. 
intros; unfold tree_test.
eapply transitive_red. 
eapply2 star_opt_beta. 
unfold subst, k_op; simpl. 
insert_Ref_out. unfold lift; rewrite ! lift_rec_null.
eval_tac.
rewrite subst_rec_closed; auto. 
 Qed. 


Lemma tree_test_one : 
forall is0 is1 is2 t, 
closed is0 -> closed is1 -> 
sf_red (App (tree_test is0 is1 is2) (App (Op Node) t)) 
(App (App is0 (App k_op i_op)) is1).
Proof. 
intros; unfold tree_test, i_op, k_op.
eapply transitive_red.
eapply2 star_opt_beta. 
unfold subst; simpl. 
insert_Ref_out. unfold lift; rewrite lift_rec_null. 
eapply transitive_red.
 eapply preserves_app_sf_red.
 eapply preserves_app_sf_red.
eapply succ_red. eapply2 s_red. 
 eapply preserves_app_sf_red.
eapply succ_red. eapply2 k_red. 
all: auto.  
eapply transitive_red. eapply preserves_app_sf_red.
 eapply preserves_app_sf_red.
eapply succ_red. eapply2 k_red. 
all: auto. 
rewrite ! subst_rec_closed; auto.  
 Qed.


Lemma tree_test_two : 
forall is0 is1 is2 t u, 
closed is2 -> 
sf_red (App (tree_test is0 is1 is2) (App (App (Op Node) t) u)) is2.
Proof. 
intros; unfold tree_test, k_op.
eapply transitive_red. eapply2 star_opt_beta. 
unfold subst; simpl. 
insert_Ref_out. unfold lift; rewrite ! lift_rec_null. 
eapply transitive_red. eapply preserves_app_sf_red.
 eapply preserves_app_sf_red.
eapply succ_red. eapply2 f_red. 
 eapply preserves_app_sf_red.
eapply succ_red. eapply2 k_red. 
all: auto.  
eapply transitive_red. eapply preserves_app_sf_red.
 eapply preserves_app_sf_red.
eapply succ_red. eapply2 k_red. 
all: auto.  
eapply transitive_red. eapply preserves_app_sf_red.
eapply succ_red. eapply2 k_red. 
all: auto. eval_tac.
rewrite subst_rec_closed; auto.  
Qed. 

Definition is_leaf := tree_test k_op (App k_op i_op) (App k_op i_op). 
Definition is_stem := tree_test (App k_op i_op) k_op (App k_op i_op).
Definition is_fork := tree_test (App k_op i_op) (App k_op i_op) k_op.

Lemma leaf_test : 
sf_red (App is_leaf (Op Node)) k_op /\
sf_red (App is_stem (Op Node)) (App k_op i_op) /\ 
sf_red (App is_fork (Op Node)) (App k_op i_op).
Proof.
repeat split; unfold is_leaf, is_stem, is_fork, tree_test, i_op, k_op; 
repeat eval_tac.
Qed. 

Lemma stem_test : forall t, 
sf_red (App is_leaf (App (Op Node) t)) (App k_op i_op) /\
sf_red (App is_stem (App (Op Node) t)) k_op /\ 
sf_red (App is_fork (App (Op Node) t)) (App k_op i_op).
Proof.
repeat split; unfold is_leaf, is_stem, is_fork, tree_test, i_op, k_op; 
repeat eval_tac.
Qed. 

Lemma fork_test : forall t u, 
sf_red (App is_leaf (App (App (Op Node) t) u)) (App k_op i_op) /\
sf_red (App is_stem (App (App (Op Node) t) u)) (App k_op i_op) /\ 
sf_red (App is_fork (App (App (Op Node) t) u)) k_op.
Proof.
repeat split; unfold is_leaf, is_stem, is_fork, tree_test, i_op, k_op; 
repeat eval_tac.
Qed. 

Definition swap := 
  star_opt (star_opt (star_opt (App (App (Ref 2) (Ref 0)) (Ref 1)))).


Lemma swap_swaps: forall r t u, 
sf_red(App (App (App swap r) t) u) (App (App r u) t).
Proof.
intros; unfold swap. 
eapply transitive_red. 
eapply star_opt_beta3.
unfold subst, lift; simpl. 
insert_Ref_out. 
unfold lift; rewrite ! lift_rec_null. 
rewrite ! subst_rec_lift_rec; try omega.
rewrite ! lift_rec_null. 
auto. 
Qed. 



Definition compose := 
star_opt (star_opt (star_opt (App (Ref 2) (App (Ref 1) (Ref 0))))). 


Lemma compose_composes : 
forall r t u, sf_red (App (App (App compose r) t) u) (App r (App t u)).
Proof.
intros; unfold compose. 
eapply transitive_red. 
eapply star_opt_beta3.
unfold subst, lift; simpl. 
insert_Ref_out. 
unfold lift; rewrite ! lift_rec_null.
rewrite ! subst_rec_lift_rec; try omega.
rewrite ! lift_rec_null. 
auto.
Qed.
 





Definition Fop := 
star_opt (star_opt (star_opt (
App (App (App is_leaf (Ref 2)) (Ref 1)) 
    (App (App (App is_stem (Ref 2)) 
   (App (App (App (Op Node) (App (Ref 2) (Op Node))) (Ref 1)) (App swap (Ref 0))))
         (App (App (App (Op Node) (Ref 2)) (Ref 1)) 
             (App (App compose (Ref 0)) (Op Node)))))))
.
 


Lemma Fop_normal: normal Fop. 
Proof.
replace Fop with (multi_star 3  (App (App (App is_leaf (Ref 2)) (Ref 1))
              (App
                 (App (App is_stem (Ref 2))
                    (App
                       (App (App (Op Node) (App (Ref 2) (Op Node))) (Ref 1))
                       (App Wave_Factor.swap (Ref 0))))
                 (App (App (App (Op Node) (Ref 2)) (Ref 1))
                    (App (App compose (Ref 0)) (Op Node)))))).
2: unfold Fop, multi_star; congruence.
match goal with 
| |- normal (multi_star 3 ?M) => replace 3 with (maxvar M) 
end. 
2: cbv; auto. 
eapply2 bind_normal_to_normal.
eapply2 bn_app. 
eapply2 bn_app. 
eapply2 bn_app. eapply2 bn_normal. cbv. repeat eapply2 nf_compound. 
cbv; auto.  cbv; auto. 
eapply2 bn_app. 
eapply2 bn_app. 
eapply2 bn_app.   
eapply2 bn_normal. cbv. repeat eapply2 nf_compound. cbv; auto.  
eapply2 bn_app. 
eapply2 bn_app. cbv. eapply2 bn_normal. repeat eapply2 nf_compound.  cbv; auto. cbv; auto.  
eapply2 bn_app. 
eapply2 bn_app. 
eapply2 bn_app. 
eapply2 bn_normal; unfold compose; repeat eapply2 nf_compound. unfold_op; auto. unfold_op; auto. 
fold subst_rec star_opt.
simpl .
all: unfold_op; simpl; auto. 
Qed. 
   

Lemma factor_leaf: 
forall u t, sf_red (App (App (App Fop (Op Node)) u) t) u.
Proof.
intros; unfold Fop. 
eapply transitive_red.
eapply2 star_opt_beta3.  
unfold subst; simpl.
eval_tac. eval_tac. eval_tac. cbv.  eval_tac. eval_tac. 
insert_Ref_out. 
unfold lift; rewrite lift_rec_null. 
rewrite subst_rec_lift_rec; try omega. 
rewrite lift_rec_null; auto. 
Qed. 

 
Lemma factor_stem: 
forall v u t, sf_red (App (App (App Fop (App (Op Node) v)) u) t) 
(App (App t (Op Node)) v).
Proof.
intros; unfold Fop.
eapply transitive_red.
eapply2 star_opt_beta3.  
unfold subst; simpl.
eval_tac. eval_tac. eval_tac.
eapply transitive_red. eapply preserves_app_sf_red. 
 eapply preserves_app_sf_red.  eapply preserves_app_sf_red.  eapply preserves_app_sf_red. 
 eval_tac. eval_tac. eval_tac.
insert_Ref_out. 
unfold lift; rewrite ! lift_rec_null. 
rewrite subst_rec_lift_rec; try omega. 
rewrite lift_rec_null; auto.
eval_tac. eval_tac.  eval_tac. eval_tac. 
eapply transitive_red. eapply preserves_app_sf_red. 
 eapply preserves_app_sf_red.  eapply preserves_app_sf_red.  eapply preserves_app_sf_red. 
 eval_tac. eval_tac. eval_tac.
insert_Ref_out. 
unfold lift; rewrite ! lift_rec_null. 
rewrite subst_rec_lift_rec; try omega. 
rewrite lift_rec_null; auto.
insert_Ref_out. 
unfold lift; rewrite ! lift_rec_null. 
rewrite subst_rec_lift_rec; try omega. 
rewrite lift_rec_null; auto.
eapply transitive_red. eapply preserves_app_sf_red. 
 eapply preserves_app_sf_red.  eapply preserves_app_sf_red. 
 eval_tac. eval_tac. 
eapply succ_red. eapply2 f_red.  eval_tac.
eapply succ_red. eapply2 s_red.  auto. 
insert_Ref_out. 
unfold lift; rewrite ! lift_rec_null. 
rewrite ! subst_rec_lift_rec; try omega. 
rewrite lift_rec_null; auto.
eval_tac. eval_tac.  eval_tac. eval_tac. eval_tac.
eval_tac. eval_tac.  eval_tac. eval_tac. eval_tac.
eapply transitive_red. eapply preserves_app_sf_red. 
 eapply preserves_app_sf_red. 
 eval_tac. auto.  eval_tac. auto.  
Qed. 

 