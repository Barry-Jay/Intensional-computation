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
(*                      Adding.v                                      *)
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
Require Import IntensionalLib.Fieska_calculus.Tagging.

Definition s_op2 g f := App (App s_op g) f .

Ltac unfold_op := unfold s_op2, a_op, i_op, id, k_op, f_op, s_op. 


Lemma s_op2_normal: forall M N, normal M -> normal N -> normal (App (App (Op Sop) M) N).
Proof. intros; nf_out. Qed. 

Lemma k_op_normal: forall M, normal M -> normal (App (App (Op Fop) (Op Fop)) M).
Proof. intros;  nf_out. Qed. 

Ltac nf_out2 := 
match goal with 
| |- normal (App (App (Op Sop) _) _) => apply s_op2_normal; nf_out2
| |- normal (App (App (Op Fop) (Op Fop)) _) => apply k_op_normal; nf_out2
| _ => nf_out
end. 


Lemma A_k_compound2: forall k M, compound (App (A_k k) M).
Proof.
induction k; split_all. 
unfold a_op. case k; split_all. case n; split_all. 
Qed. 

Hint Resolve A_k_compound2. 


(* pairing *) 

Definition left_projection M := App (App (App (Op Fop) M) M) (Op Kop). 
Definition right_projection M := App (App (App (Op Fop) M) M) (App (Op Kop) (Op Iop)). 
Definition fst_projection M := right_projection(left_projection M). 
Definition snd_projection M := right_projection M.  

Lemma fst_out : forall M N, sf_red (fst_projection (s_op2 M N)) M. 
Proof. 
intros; unfold fst_projection, left_projection, right_projection.  unfold_op. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. auto. eapply succ_red. 
eapply2 f_compound_red. eval_tac. eapply succ_red. 
eapply2 f_compound_red. eval_tac. auto. eapply succ_red. 
eapply2 f_compound_red. eval_tac. 
Qed. 

Lemma snd_out : forall M N, sf_red (snd_projection (s_op2 M N)) N. 
Proof. 
intros; unfold snd_projection, left_projection, right_projection.  unfold_op. 
eapply succ_red. eapply2 f_compound_red. eval_tac.
Qed. 

Lemma fst_preserves_sf_red: 
forall M N, sf_red M N -> sf_red (fst_projection M) (fst_projection N).
Proof. 
intros; unfold fst_projection, left_projection, right_projection.  
repeat eapply2 preserves_app_sf_red. Qed.

Lemma snd_preserves_sf_red: 
forall M N, sf_red M N -> sf_red (snd_projection M) (snd_projection N).
Proof. 
intros; unfold snd_projection, left_projection, right_projection.  
repeat eapply2 preserves_app_sf_red. Qed. 


Lemma subst_rec_preserves_left_projection : 
forall M N k, subst_rec (left_projection M) N k = left_projection (subst_rec M N k). 
Proof. intros; unfold left_projection. simpl. auto. Qed. 

Lemma subst_rec_preserves_right_projection : 
forall M N k, subst_rec (right_projection M) N k = right_projection (subst_rec M N k). 
Proof. intros; unfold right_projection. simpl. auto. Qed. 

Lemma subst_rec_preserves_fst_projection : 
forall M N k, subst_rec (fst_projection M) N k = fst_projection (subst_rec M N k). 
Proof. 
intros; unfold fst_projection. rewrite subst_rec_preserves_right_projection. 
rewrite subst_rec_preserves_left_projection. auto.
Qed. 

Lemma subst_rec_preserves_snd_projection : 
forall M N k, subst_rec (snd_projection M) N k = snd_projection (subst_rec M N k). 
Proof. 
intros; unfold snd_projection. apply subst_rec_preserves_right_projection. 
Qed. 



(* substitutions 

[| Add x u sigma |] = A add (S (S sigma x) u) -- the order simplifies beta-reduction
add sigma t traverses t, looking for variables.
add sigma i traverses sigma, looking for i. 

*) 

Definition add_fn := star_opt (star_opt (* recursion argument and sigma *) 
(* tag *) 
(extension (App (App (Op Aop) (App (App (Op Aop) (App (App (Op Aop) (Y_k 3)) (Ref 2))) 
(Ref 1))) (Ref 0)) 
           (App (App (App (App (Op Aop) (Ref 4)) (Ref 3)) (Ref 1))
                (App (App (App (Op Aop) (Ref 4)) (Ref 3)) (Ref 0)))
(* var *) 
(extension (App (App (Op Aop)  (App (App (Op Aop) (Y_k 3)) var_fn)) (Ref 0))
                     (App (App (App (App (Op Eop) (Ref 0)) 
                                    (snd_projection (fst_projection (Ref 1)))) (* x *) 
                               (snd_projection (Ref 1))) (* u *) 
                          (App (fst_projection (fst_projection (Ref 1)))  (* sigma *) 
                               (App (App (Op Aop)  (App (App (Op Aop) (Y_k 3)) var_fn)) (Ref 0))))
(* abs *)
(extension (App (App (Op Aop)  (App (App (Op Aop)  
(App (App (Op Aop)  (App (App (Op Aop) (Ref 5)) (Ref 4))) (Ref 3))) (s_op2 (Ref 2) (Ref 1))))
(Ref 0))
           (App (App (Op Aop)  (App (App (Op Aop)  (App (App (Op Aop)  
(App (App (Op Aop)  (Ref 5)) (Ref 4))) (Ref 3)))
                                         (s_op2 (App (App (App (Op Aop) (Ref 7)) (Ref 6)) (Ref 2)) (Ref 1))))
                               (Ref 0))
(* add  *) 
(extension (App (App (Op Aop) (Ref 3)) 
                (App (App (Op Sop) (App (App (Op Sop) (Ref 2)) (Ref 1))) (Ref 0)))
           (App (App (Op Aop) (Ref 3)) 
                (App (App (Op Sop) 
                (App (App (Op Sop) (App (App (App (Op Aop) (Ref 5)) (Ref 4)) (Ref 2))) (Ref 1)))
                (App (App (App (Op Aop) (Ref 5)) (Ref 4)) (Ref 0))))
(* Nil *) 
(fst_projection (fst_projection (Ref 0)))))))).

Definition add :=  App (App (Op Aop) (Y_k 3)) add_fn.



Definition abs_fn := star_opt  (* rec'n argument *) 
(extension (App (App s_op (Ref 1)) (Ref 0)) (* y::ys *) 
           (star_opt (star_opt (star_opt (* sigma_x t u *) 
             (App (App (Op Aop)  (App (App (Op Aop)  (App (App (Op Aop)  (Ref 5)) (Ref 3))) 
                                 (s_op2 (App (App (Op Aop) add) (s_op2 (Ref 2) (Ref 0))) (Ref 4))))
                       (Ref 1)))))
           (App k_op (star_opt (star_opt (star_opt (App (App (App (Op Aop) add) 
                                                        (s_op2 (Ref 2) (Ref 0))) 
                                                        (Ref 1)))))))
.

Definition abs xs sigma_x t := 
  App (App (Op Aop)  (App (App (Op Aop)  (App (App (Op Aop)  
  (App (App (Op Aop) (Y_k 4)) abs_fn)) xs)) sigma_x)) t. 


Lemma add_fn_closed: maxvar add_fn = 0. 
Proof. cbv. auto. Qed. 


Lemma add_fn_normal: normal add_fn. 
Proof. 
unfold add_fn. unfold_op. 
repeat apply star_opt_normal. 
unfold fst_projection, snd_projection, left_projection, right_projection. 
cbv; nf_out; repeat (eapply2 nf_active; nf_out).
Qed. 

Lemma abs_many_red : 
forall x1 xs sigma_x t u, sf_red (App (abs (App (App s_op x1) xs) sigma_x t) u)
                                      (abs xs (s_op2 (App (App (Op Aop) add) (s_op2 sigma_x u)) x1) t).
Proof.
intros; unfold abs, abs_fn, s_op2; unfold_op. 
eapply succ_red. eapply2 a_red. 
eapply transitive_red. eapply preserves_app_sf_red. eapply succ_red. eapply a_red. auto. auto. auto. 
eapply transitive_red. eapply preserves_app_sf_red. eapply succ_red. eapply a_red. auto. auto. auto.
eapply transitive_red. eapply preserves_app_sf_red. eapply succ_red. eapply a_red. auto. auto. auto.
auto. auto. auto. auto. 
eapply transitive_red. eapply Y4_fix. 
eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red.  
eapply preserves_app_sf_red.  
eapply2 star_opt_beta. auto. auto. auto. 
unfold subst. rewrite subst_rec_preserves_extension. 
eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red.  
eapply extensions_by_matching. 
eapply match_app; nf_out. auto. auto. 
unfold map, app, length, fold_left, subst.  
repeat (rewrite subst_rec_preserves_star_opt at 1). auto. auto. 
eapply transitive_red.  eapply2 star_opt_beta3.
unfold pattern_size; fold pattern_size. unfold plus; fold plus. 
unfold subst; rewrite 6? subst_rec_preserves_app at 1. rewrite 6? subst_rec_preserves_app at 1.  
repeat (unfold subst_rec; fold subst_rec; insert_Ref_out; unfold pred). 
unfold lift; rewrite ! lift_rec_lift_rec; try omega. rewrite ! lift_rec_null. unfold plus; fold plus. 
unfold lift; rewrite ! subst_rec_lift_rec; try omega. rewrite ! lift_rec_null.
auto. 
Qed. 


Lemma abs_red : 
forall sigma_x t u, sf_red (App (abs s_op sigma_x t) u) 
                           (App (App (App (Op Aop) add) (s_op2 sigma_x u)) t). 
Proof.
intros; unfold abs, abs_fn; unfold_op. 
eapply succ_red. eapply2 a_red. 
eapply transitive_red. eapply preserves_app_sf_red. eapply succ_red. eapply a_red. auto. auto. auto. 
eapply transitive_red. eapply preserves_app_sf_red. eapply succ_red. eapply a_red. auto. auto. auto. 
eapply transitive_red. eapply preserves_app_sf_red. eapply succ_red. eapply a_red. auto. auto. auto. 
auto. auto. auto. auto. auto. auto. 
(* 1 *) 
eapply transitive_red. eapply preserves_app_sf_red. eapply Y4_fix. auto. 
eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red.  
eapply preserves_app_sf_red.  eapply preserves_app_sf_red. 
eapply2 star_opt_beta. auto. auto. auto. auto. 
unfold subst. rewrite subst_rec_preserves_extension. 
eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red.  
eapply preserves_app_sf_red.  eapply extensions_by_matchfail. 
eapply matchfail_compound_op; nf_out. auto. auto. auto. 
rewrite ? subst_rec_app. 
rewrite ? subst_rec_op. 
rewrite ? subst_rec_preserves_star_opt. 
(* 1 *)  
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
 eapply preserves_app_sf_red. eapply succ_red. eapply2 k_red. auto. auto. auto. auto. 
eapply transitive_red. eapply star_opt_beta3. 
unfold subst. (rewrite 12? subst_rec_preserves_app at 1). 
unfold subst_rec; fold subst_rec. insert_Ref_out. 
unfold subst_rec; fold subst_rec. insert_Ref_out.  unfold pred.
rewrite 4 ? (subst_rec_closed act) at 1; try (rewrite act_closed; omega). 
unfold subst_rec; fold subst_rec. insert_Ref_out.  
unfold lift.  
rewrite ? lift_rec_lift_rec; try omega. unfold plus; fold plus. 
rewrite ? subst_rec_lift_rec; try omega.
rewrite ? lift_rec_null; try omega.
unfold subst_rec; fold subst_rec. insert_Ref_out.  unfold lift; rewrite lift_rec_null. 
auto. 
Qed. 


Lemma add_red_empty: 
forall sigma x u, 
sf_red (App (App add (s_op2 (s_op2 sigma x) u)) (Op Iop)) (App sigma (Op Iop)) .
Proof.
intros. unfold_op;  unfold add at 1. eval_tac. 
eapply transitive_red. eapply2 Y3_fix. 
replace (App (App (Op Aop) (Y_k 3)) add_fn) with add by auto. 
unfold add_fn.
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply2 star_opt_beta2.  auto. 
unfold subst; rewrite ! subst_rec_preserves_extension. 
eapply transitive_red. eapply2 extensions_by_matchfail.
eapply transitive_red. eapply2 extensions_by_matchfail.
eapply transitive_red. eapply2 extensions_by_matchfail.
eapply transitive_red. eapply2 extensions_by_matchfail.
rewrite ! subst_rec_preserves_fst_projection. 
unfold subst_rec; fold subst_rec. insert_Ref_out.
unfold lift. rewrite lift_rec_lift_rec; try omega. unfold plus. 
rewrite ! subst_rec_lift_rec; try omega.  
rewrite ! lift_rec_null. 
eapply transitive_red. eapply preserves_app_sf_red. 
eapply fst_preserves_sf_red. eapply2 fst_out. auto. 
eapply transitive_red. eapply preserves_app_sf_red. 
eapply2 fst_out. auto. auto. 
Qed. 


Lemma add_red_add: 
forall i u sigma sigma2, 
sf_red (App (App add sigma) (App (App (Op Aop) add) (s_op2 (s_op2 sigma2 i) u)))
        (App (App (Op Aop) add) (s_op2 (s_op2 (App (App (App (Op Aop) add) sigma) sigma2) i) 
        (App (App (App (Op Aop) add) sigma) u))). 
Proof.
intros. unfold_op;  unfold add at 1. eval_tac. 
eapply transitive_red. eapply2 Y3_fix. 
replace (App (App (Op Aop) (Y_k 3)) add_fn) with add by auto. 
unfold add_fn.
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply2 star_opt_beta2.  auto. 
unfold subst; rewrite ! subst_rec_preserves_extension. 
eapply transitive_red. eapply2 extensions_by_matchfail.
eapply2 matchfail_compound_l. eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. unfold A_k; auto. eapply2 matchfail_compound_r. 
unfold_op; auto. 
eapply2 matchfail_compound_l. unfold A_k; auto. eapply2 matchfail_compound_l. 
unfold_op; eapply2 matchfail_op. unfold factorable. left; eauto. discriminate. 
(* 1 *) 
eapply transitive_red. eapply2 extensions_by_matchfail.
eapply2 matchfail_compound_l. eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r. eapply2 program_matching. 
unfold program; auto.
(* 2 *)  
unfold add_fn. 
unfold extension at 1. 
rewrite star_opt_occurs_true. 2: cbv; auto.  2: discriminate. 
rewrite (star_opt_occurs_true s_op). 2: cbv; auto. 2: discriminate.  
rewrite star_opt_occurs_true. 2: cbv; auto. 
2: rewrite star_opt_occurs_true. 2: discriminate. 2: cbv; auto. 
2: discriminate. 
unfold var_fn,tag at 1. 
rewrite star_opt_eta. 2: cbv; auto.  
unfold subst, subst_rec; fold subst_rec. insert_Ref_out. 
rewrite subst_rec_closed; [|auto]. unfold pred. 
rewrite star_opt_occurs_true. 2: cbv; auto. 2: discriminate. 
rewrite (star_opt_occurs_true  (App (Op Sop) _)). 
2: cbv; auto. 2: discriminate. 
(* 2 *) 
eapply2 matchfail_compound_l. eapply2 matchfail_compound_r. 
unfold star_opt at 2 1. unfold occurs0; fold occurs0. 
rewrite orb_false_l. 
rewrite star_opt_occurs_true. 2: cbv; auto. 2: discriminate. 
eapply2 matchfail_compound_l. eapply2 matchfail_op. 
unfold factorable. right; auto. discriminate. 
(* 1 *) 
eapply transitive_red. eapply2 extensions_by_matchfail.
eapply2 matchfail_compound_l. eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. eapply2 matchfail_compound_r. 
unfold_op; auto. 
eapply2 matchfail_compound_l. eapply2 matchfail_compound_l. 
eapply2 matchfail_op. 
unfold factorable. unfold_op; left; eauto. discriminate. 
(* 1 *) 
eapply transitive_red. eapply2 extensions_by_matching. 
eapply2 match_app. eapply2 match_app. eapply2 match_app. 
unfold map, app, length, fold_left, subst. 
unfold pattern_size; fold pattern_size. unfold plus; fold plus. 
unfold_op.
rewrite ! subst_rec_app at 1. rewrite ! subst_rec_op at 1. 
repeat (rewrite subst_rec_ref at 1; insert_Ref_out). unfold lift. 
rewrite ! lift_rec_lift_rec; try omega. unfold plus. 
rewrite ! subst_rec_lift_rec; try omega.
rewrite ! lift_rec_null.
auto. 
Qed.


Lemma add_red_var_unequal: 
forall i u sigma j, program i -> program j -> i <> j -> 
sf_red (App (App add (s_op2 (s_op2 sigma i) u)) (var j)) (App sigma (var j)).       
Proof.
intros. unfold_op;  unfold add at 1. eval_tac. 
eapply transitive_red. eapply2 Y3_fix. 
replace (App (App (Op Aop) (Y_k 3)) add_fn) with add by auto. 
unfold add_fn.
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply2 star_opt_beta2.  auto. 
unfold subst; rewrite ! subst_rec_preserves_extension. 
eapply transitive_red. eapply2 extensions_by_matchfail.
eapply2 matchfail_compound_l. eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. unfold A_k; auto. eapply2 matchfail_compound_r. 
unfold_op; auto. 
eapply2 matchfail_compound_l. unfold A_k; auto. eapply2 matchfail_compound_l. 
unfold_op; eapply2 matchfail_op. unfold factorable. left; eauto. discriminate. 
eapply transitive_red. eapply2 extensions_by_matching.
eapply2 match_app. eapply2 match_app. eapply2 match_app. 
eapply2 program_matching. 
unfold program; auto.
eapply2 program_matching.  unfold program; auto. 
unfold map, app, length, fold_left, subst. 
unfold pattern_size; fold pattern_size.
rewrite ! pattern_size_closed; auto.  unfold plus; fold plus. 
unfold_op.
rewrite ! subst_rec_app. rewrite ! subst_rec_op at 1. 
rewrite ! subst_rec_preserves_snd_projection. 
rewrite ! subst_rec_preserves_fst_projection. 
repeat (rewrite subst_rec_ref at 1; insert_Ref_out). unfold lift. 
rewrite ! lift_rec_lift_rec; try omega. unfold plus. 
rewrite ! subst_rec_lift_rec; try omega.
rewrite ! lift_rec_null.
auto. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. auto. 
eapply transitive_red. eapply snd_preserves_sf_red. eapply2 fst_out.
eapply2 snd_out.  
eapply transitive_red. eapply snd_out. auto. 
eapply preserves_app_sf_red.
eapply fst_preserves_sf_red. eapply2 fst_out. auto. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red.
eapply2 unequal_programs. auto. auto. eval_tac. 
eapply transitive_red. eapply preserves_app_sf_red. eapply2 fst_out. auto. 
auto. 
Qed.

Lemma add_red_var_equal: 
forall i u sigma, program i -> 
sf_red (App (App add (s_op2 (s_op2 sigma i) u)) (var i)) u.       
Proof.
intros. unfold_op;  unfold add at 1. eval_tac. 
eapply transitive_red. eapply2 Y3_fix. 
replace (App (App (Op Aop) (Y_k 3)) add_fn) with add by auto. 
unfold add_fn.
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply2 star_opt_beta2.  auto. 
unfold subst; rewrite ! subst_rec_preserves_extension. 
eapply transitive_red. eapply2 extensions_by_matchfail.
eapply2 matchfail_compound_l. eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. unfold A_k; auto. eapply2 matchfail_compound_r. 
unfold_op; auto. 
eapply2 matchfail_compound_l. unfold A_k; auto. eapply2 matchfail_compound_l. 
unfold_op; eapply2 matchfail_op. unfold factorable. left; eauto. discriminate. 
eapply transitive_red. eapply2 extensions_by_matching.
eapply2 match_app. 
eapply2 program_matching. 
unfold program; auto. 
unfold map, app, length, fold_left, subst. 
unfold pattern_size; fold pattern_size.
rewrite ! pattern_size_closed; auto.  unfold plus; fold plus. 
unfold_op.
rewrite ! subst_rec_app. rewrite ! subst_rec_op at 1. 
rewrite ! subst_rec_preserves_snd_projection. 
rewrite ! subst_rec_preserves_fst_projection. 
repeat (rewrite subst_rec_ref at 1; insert_Ref_out). unfold lift. 
rewrite ! lift_rec_lift_rec; try omega. unfold plus. 
rewrite ! subst_rec_lift_rec; try omega.
rewrite ! lift_rec_null.
auto. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. auto. 
eapply transitive_red. eapply snd_preserves_sf_red. eapply2 fst_out.
eapply2 snd_out.  eapply2 snd_out. 
eapply transitive_red. eapply preserves_app_sf_red. 
eapply transitive_red. eapply fst_preserves_sf_red. eapply2 fst_out.
eapply2 fst_out. auto. auto. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red.
eapply2 equal_programs. auto. auto. eval_tac. 
Qed.



Lemma add_red_tag: 
forall sigma M N, sf_red (App (App add sigma) (tag M N)) 
                         (App (App (App (App (Op Aop) add) sigma) M) 
                         (App (App (App (Op Aop) add) sigma) N)). 
Proof.
intros. unfold add at 1. eval_tac. 
eapply transitive_red. eapply2 Y3_fix. 
replace (App (App (Op Aop) (Y_k 3)) add_fn) with add by auto. 
unfold add_fn.
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply2 star_opt_beta2.  auto. 
unfold subst; rewrite ! subst_rec_preserves_extension. 
eapply transitive_red. eapply2 extensions_by_matching.
eapply2 match_app. eapply2 match_app. 
eapply2 match_app. eapply2 match_app. 
eapply2 match_app. eapply2 program_matching. 
unfold program; auto. 
unfold map, app, length, fold_left, subst. 
unfold pattern_size; fold pattern_size.
rewrite ! pattern_size_closed; auto.  unfold plus; fold plus. 
unfold_op.
repeat (unfold subst_rec; fold subst_rec; insert_Ref_out; unfold pred). 
unfold lift. rewrite ! lift_rec_lift_rec; try omega. unfold plus. 
rewrite ! subst_rec_lift_rec; try omega.
rewrite ! lift_rec_null.
auto. 
Qed. 
  

Lemma add_red_abs : 
forall xs sigma x t sigma2, 
  sf_red (App (App add sigma2) (abs xs (s_op2 sigma x) t))
         (abs xs (s_op2 (App (App (App (Op Aop) add) sigma2) sigma) x) t)
.
Proof.
intros; unfold add; unfold abs at 1. 
eval_tac. 
eapply transitive_red. eapply2 Y3_fix. 
unfold add_fn at 1. 
eapply  transitive_red. eapply preserves_app_sf_red.  
eapply star_opt_beta2. auto.
unfold subst. rewrite ! subst_rec_preserves_extension. 
eapply  transitive_red. eapply2 extensions_by_matchfail. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
unfold_op; eapply match_op.
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_op. unfold_op; 
unfold factorable; split_all; left; eauto. discriminate. 
eapply  transitive_red. 
eapply2 extensions_by_matchfail.
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r.
unfold_op; eapply match_op.
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_l. 
eapply matchfail_op. unfold factorable; split_all; eauto. discriminate.
eapply  transitive_red. eapply2 extensions_by_matching. 
unfold_op. 
eapply2 match_app. 
eapply2 match_app. 
eapply2 match_app. 
eapply2 match_app.
eapply2 match_app. 
eapply2 match_app.
unfold map, app, length, fold_left. 
unfold_op; unfold pattern_size; fold pattern_size; unfold plus; fold plus.
unfold subst; rewrite ! subst_rec_app. rewrite ! subst_rec_op. 
unfold lift; rewrite ! lift_rec_null. 
do 20 (rewrite subst_rec_ref at 1; insert_Ref_out; unfold pred). 
do 10 (rewrite subst_rec_ref at 1; insert_Ref_out; unfold pred). 
unfold lift; rewrite ! lift_rec_lift_rec; try omega. unfold plus. 
rewrite ! subst_rec_lift_rec; try omega.  rewrite ! lift_rec_null.
insert_Ref_out. 
repeat (unfold subst_rec; fold subst_rec; insert_Ref_out). 
unfold lift; rewrite ! lift_rec_lift_rec; try omega. unfold plus. 
rewrite ! subst_rec_lift_rec; try omega.  rewrite ! lift_rec_null.
auto. 
Qed. 


(* 
abs (A y ys) sigma_x t u  --> abs ys (S(S sigma_x u) y) t
abs nil sigma_x t u --> act t (S sigma_x u) 
act y sigma --> applysub sigma y 
applysub (S (S sigma x) u) x -> u 
applysub (S (S sigma x) u) y -> applysub sigma y 
applysub nil x ---> x 
*) 

