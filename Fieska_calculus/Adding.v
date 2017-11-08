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

Lemma k_op_normal: forall M, normal M -> normal (App (Op Kop) M).
Proof. intros;  nf_out. Qed. 

Ltac nf_out2 := 
match goal with 
| |- normal (App (App (Op Sop) _) _) => apply s_op2_normal; nf_out2
| |- normal (App (Op Kop) _) => apply k_op_normal; nf_out2
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


Definition swap M N := App (App (Op Sop) (App (Op Aop) M)) (App (Op Kop) N).


Definition add_fn := star_opt (star_opt (star_opt 
(* recursion argument, (sigma,x) u  *) 
(* tag *) 
(extension (App (App (Op Aop)(App (App (Op Aop)(App (App (Op Aop) (Y_k 3)) (Ref 2))) (Ref 1))) (Ref 0)) 
        (App (App (App (App (Op Aop) (App (App (Op Aop) (Ref 5)) (Ref 4))) (Ref 3)) (Ref 1))
             (App (App (App (Op Aop) (App (App (Op Aop) (Ref 5)) (Ref 4)) )(Ref 3)) (Ref 0)))
(* var *) 
(extension (App (App (Op Aop) (App (App (Op Aop)(Y_k 3)) (Ref 1))) (Ref 0))  (* var y *) 
                     (App (App (App (App (Op Eop) (Ref 0)) 
                                     (snd_projection (Ref 3))) (* y = x *) 
                               (Ref 2))  (* u *) 
                          (App (fst_projection (Ref 3)) 
                               (App (App (Op Aop) (App (App (Op Aop)(Y_k 3)) (Ref 1)) )(Ref 0))))
                                          (* sigma (var y) *) 
(* add  *) 
(* | Add i u sigma => App (App (Op Aop) add) (s_op2 (s_op2 (lambda_to_fieska sigma) (ref i)) (lambda_to_fieska u))
*) 
(extension (App (App (Op Aop) (App (App (Op Aop) (App (App (Op Aop) (Y_k 4)) 
                                                      (Ref 2)))
                                   (Ref 1)))
           (Ref 0))
  (* add (sigma2, x2) u *) 
   (App (App (Op Aop) (App (App (Op Aop) (App (App (Op Aop) (Y_k 4)) (Ref 2)))
     (s_op2 (App (App (App (Op Aop) (App (App (Op Aop) (Ref 5)) 
                                         (Ref 4))) 
                      (Ref 3)) 
                 (fst_projection (Ref 1)))
        (snd_projection (Ref 1)))))
     (App (App (App (Op Aop) (App (App (Op Aop) (Ref 5)) (Ref 4))) (Ref 3)) (Ref 0)))
(* abs = swap (App (App (Op Aop) add (s_op2 sigma x)) t *) 
(extension (swap (App (App (Op Aop) (Ref 3)) (App (App (Op Sop) (Ref 2)) (Ref 1))) (Ref 0))
           (swap (App (App (Op Aop) (Ref 3)) (App (App (Op Sop) 
                                             (App (App (App (Op Aop) 
                                                            (App (App (Op Aop) (Ref 6))
                                                                 (Ref 5)))
                                                       (Ref 4)) 
                                                  (Ref 2)))
                                                  (Ref 1)))
                 (Ref 0))
(* dummy case *) 
(fst_projection (Ref 1))
)))))). 

Definition add :=  App (App (Op Aop) (Y_k 4)) add_fn.


Definition abs sigma x t := swap (App (App (Op Aop) add) (s_op2 sigma x)) t .



Lemma abs_red : 
forall sigma x t u, sf_red (App (abs sigma x t) u) 
                           (App (App (App (Op Aop) (App (App (Op Aop) add) (s_op2 sigma x)))
                                      u) t). 
Proof.
intros; unfold abs, swap; unfold_op. eval_tac. 
eapply2 preserves_app_sf_red. eval_tac. 
Qed. 


Lemma add_closed: maxvar add = 0.
Proof.
unfold add. unfold maxvar; fold maxvar. rewrite Y_k_closed. unfold max. 
unfold add_fn. rewrite ! maxvar_star_opt. 
cbv.  auto. 
Qed. 




Lemma add_red_tag: 
forall sigma_x u M N, sf_red (App (App (App add sigma_x) u) (tag M N)) 
                         (App (App (App (App (Op Aop) (App (App (Op Aop) add) sigma_x)) u) M)
                              (App (App (App (Op Aop) (App (App (Op Aop) add) sigma_x)) u) N)).
Proof.
intros. unfold add at 1. eval_tac. 
eapply transitive_red. eapply2 Y4_fix. 
replace (App (App (Op Aop) (Y_k 4)) add_fn) with add by auto. 
unfold add_fn.
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply2 star_opt_beta3.  auto. 
unfold subst; rewrite ! subst_rec_preserves_extension. 
eapply transitive_red. 
 eapply2 extensions_by_matching.
unfold tag, tag_fix.  unfold_op. 
eapply2 match_app. eapply2 match_app.  
eapply2 match_app. eapply2 match_app. 
eapply2 match_app. eapply2 program_matching. 
unfold program; auto. 
(* 1 *)  
unfold map, app, length, fold_left, subst.
unfold pattern_size; fold pattern_size.
rewrite ! (pattern_size_closed (Y_k _)). 
2: apply Y_k_closed. 
 unfold plus; fold plus. 
repeat (unfold subst_rec; fold subst_rec; insert_Ref_out). 
unfold lift. rewrite ! lift_rec_lift_rec; try omega. unfold plus. 
repeat (rewrite subst_rec_ref; insert_Ref_out; unfold pred). 
unfold lift. 
rewrite ! subst_rec_lift_rec; try omega.
rewrite ! lift_rec_null. auto. 
Qed. 
  


Lemma add_red_var_unequal: 
forall i u sigma j, program i -> program j -> i <> j -> 
sf_red (App (App (App add (s_op2 sigma i)) u) (var j)) (App sigma (var j)).       
Proof.
intros. unfold_op;  unfold add at 1. eval_tac. 
eapply transitive_red. eapply2 Y4_fix. 
replace (App (App (Op Aop) (Y_k 4)) add_fn) with add by auto. 
unfold add_fn.
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply2 star_opt_beta3.  auto. 
unfold subst; rewrite ! subst_rec_preserves_extension. 
eapply transitive_red. eapply2 extensions_by_matchfail.
unfold var, var_fix, var_fn; unfold_op. 
eapply2 matchfail_compound_l. eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. eapply2 matchfail_compound_r.
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. unfold_op; auto. 
 eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_l. 
unfold_op.  
eapply2 matchfail_op. unfold factorable. left; eauto. discriminate.
(* 1 *)  
eapply transitive_red. eapply2 extensions_by_matching.
unfold var, var_fix; unfold_op. 
eapply2 match_app. eapply2 match_app. eapply2 match_app. 
apply program_matching. 
unfold program; split. nf_out.  auto. 
(* 1 *) 
unfold map, app, length, fold_left, subst. 
unfold pattern_size; fold pattern_size.
rewrite ! pattern_size_closed; auto.  unfold plus; fold plus. 
rewrite ! subst_rec_app. rewrite ! subst_rec_op.  
rewrite ! subst_rec_preserves_snd_projection. 
rewrite ! subst_rec_preserves_fst_projection. 
unfold lift. rewrite ! lift_rec_null.
repeat (rewrite subst_rec_ref at 1; insert_Ref_out). 
unfold lift; rewrite ! lift_rec_lift_rec; try omega. unfold plus. 
rewrite ! subst_rec_lift_rec; try omega.
rewrite ! lift_rec_null.
unfold subst_rec; fold subst_rec. 
rewrite ! (subst_rec_closed (Y_k _)); try (rewrite Y_k_closed; omega). 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. auto. 
eapply2 snd_out. auto.   
eapply transitive_red. eapply preserves_app_sf_red. eapply2 fst_out. auto. auto. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red.
eapply2 unequal_programs. auto. auto. 
eval_tac. 
Qed.

Lemma add_red_var_equal: 
forall i u sigma, program i -> 
sf_red (App (App (App add (s_op2 sigma i)) u) (var i)) u.       
Proof.
intros. unfold_op;  unfold add at 1. eval_tac. 
eapply transitive_red. eapply2 Y4_fix. 
replace (App (App (Op Aop) (Y_k 4)) add_fn) with add by auto. 
unfold add_fn.
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply2 star_opt_beta3.  auto. 
unfold subst; rewrite ! subst_rec_preserves_extension. 
eapply transitive_red. eapply2 extensions_by_matchfail.
unfold var, var_fix, var_fn; unfold_op. 
eapply2 matchfail_compound_l. eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. eapply2 matchfail_compound_r.
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. unfold_op; auto. 
 eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_l. 
unfold_op.  
eapply2 matchfail_op. unfold factorable. left; eauto. discriminate.
(* 1 *)  
eapply transitive_red. eapply2 extensions_by_matching.
unfold var, var_fix; unfold_op. 
eapply2 match_app. eapply2 match_app. eapply2 match_app. 
apply program_matching. 
unfold program; split. nf_out.  auto. 
(* 1 *) 
unfold map, app, length, fold_left, subst. 
unfold pattern_size; fold pattern_size.
rewrite ! pattern_size_closed; auto.  unfold plus; fold plus. 
rewrite ! subst_rec_app. rewrite ! subst_rec_op.  
rewrite ! subst_rec_preserves_snd_projection. 
rewrite ! subst_rec_preserves_fst_projection. 
unfold lift. rewrite ! lift_rec_null.
repeat (rewrite subst_rec_ref at 1; insert_Ref_out). 
unfold lift; rewrite ! lift_rec_lift_rec; try omega. unfold plus. 
rewrite ! subst_rec_lift_rec; try omega.
rewrite ! lift_rec_null.
unfold subst_rec; fold subst_rec. 
rewrite ! (subst_rec_closed (Y_k _)); try (rewrite Y_k_closed; omega). 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. auto. 
eapply2 snd_out. auto.   
eapply transitive_red. eapply preserves_app_sf_red. eapply2 fst_out. auto. auto. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red.
eapply2 equal_programs. auto. auto. 
eval_tac. 
Qed.


Lemma subst_rec_preserves_swap: 
forall M N P k, subst_rec (swap M N) P k = swap (subst_rec M P k) (subst_rec N P k).
Proof. intros; unfold swap, subst_rec; auto. Qed. 

Lemma pattern_size_swap: 
forall M N, pattern_size(swap M N) = pattern_size M + pattern_size N. 
Proof. intros; unfold swap, pattern_size; fold pattern_size; omega.  Qed. 


Lemma add_red_abs : 
forall sigma x t sigma_y u, 
  sf_red (App (App (App add sigma_y) u) (abs sigma x t))
         (abs (App (App (App (Op Aop) (App (App (Op Aop) add) sigma_y)) u) sigma) x t). 
Proof.
intros. unfold add at 1. eval_tac. 
eapply transitive_red. eapply2 Y4_fix. 
replace (App (App (Op Aop) (Y_k 4)) add_fn) with add by auto. 
unfold add_fn.
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply2 star_opt_beta3.  auto. 
unfold subst; rewrite ! subst_rec_preserves_extension. 
eapply transitive_red. eapply2 extensions_by_matchfail.
unfold abs, swap; unfold_op; auto. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_op. 
unfold factorable; eauto. discriminate. 
(* 1 *) 
eapply  transitive_red. 
eapply2 extensions_by_matchfail.
unfold abs, swap; unfold_op; auto. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_op. 
unfold factorable; eauto. discriminate. 
(* 1 *) 
eapply  transitive_red. 
eapply2 extensions_by_matchfail.
unfold abs, swap; unfold_op; auto. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_op. 
unfold factorable; eauto. discriminate. 
(* 1 *) 
eapply  transitive_red. 
eapply2 extensions_by_matching.
unfold abs, swap; unfold_op; auto. 
do 20 eapply2 match_app. 
unfold map, app, length, fold_left, subst.  
(* 1 *) 
 unfold abs. rewrite ! subst_rec_preserves_swap. 
rewrite ! pattern_size_swap. 
unfold pattern_size; fold pattern_size. 
unfold lift; rewrite ! lift_rec_null. unfold plus. 
rewrite ! lift_rec_lift_rec; try omega. unfold plus; fold plus. 
repeat (unfold subst_rec; fold subst_rec; insert_Ref_out). 
unfold lift; rewrite ! lift_rec_null. 
rewrite ! lift_rec_lift_rec; try omega. unfold plus. 
rewrite ! subst_rec_lift_rec; try omega. 
rewrite ! lift_rec_null. 
auto. 
Qed.   





Lemma add_fn_normal: normal add_fn. 
Proof. 
unfold add_fn. unfold_op. 
repeat apply star_opt_normal. 
unfold fst_projection, snd_projection, left_projection, right_projection. 
cbv; nf_out; repeat (eapply2 nf_active; nf_out); auto.
Qed. 

  
Lemma add_normal: normal add. 
Proof. 
unfold add. nf_out. apply add_fn_normal. 
Qed. 

Lemma abs_normal: 
forall sigma x t, normal sigma -> normal x -> normal t -> normal (abs sigma x t).  
Proof. 
intros. unfold abs, swap. nf_out. 
eapply2 add_normal. auto. auto. auto.  unfold_op; auto. 
Qed. 

Lemma add_red_add: 
forall sigma_x u sigma2 y v, 
sf_red (App (App (App add sigma_x) u) (App (App (Op Aop) 
(App (App (Op Aop) add) (s_op2 sigma2 y))) v))  
        (App (App (Op Aop) (App (App (Op Aop) add) 
(s_op2 (App (App (App (Op Aop) (App (App (Op Aop) add) sigma_x)) u) sigma2) y)))
        (App (App (App (Op Aop) (App (App (Op Aop) add) sigma_x)) u) v)). 
Proof.
intros. unfold_op;  unfold add at 1. eval_tac. 
eapply transitive_red. eapply2 Y4_fix. 
replace (App (App (Op Aop) (Y_k 4)) add_fn) with add by auto. 
unfold add_fn.
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply2 star_opt_beta3.  auto. 
unfold subst; rewrite ! subst_rec_preserves_extension. 
(* not a tag *) 
eapply transitive_red. apply extensions_by_matchfail.
unfold add, add_fn; unfold_op; auto. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l.
eapply2 matchfail_compound_r. unfold_op; auto. 
unfold_op. eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_op.  unfold factorable. right; auto.  discriminate. 
(* 1  not a var *) 
eapply transitive_red. eapply2 extensions_by_matchfail.
unfold add; unfold_op; auto. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r; unfold_op. auto.   
eapply2 matchfail_compound_l.
eapply2 matchfail_compound_l. unfold_op. 
eapply2 matchfail_op. unfold factorable. left; eauto. discriminate. 
(* 1 *) 
(* 1 add vs add *) 
eapply transitive_red. eapply2 extensions_by_matching.
eapply2 match_app. eapply2 match_app. eapply2 match_app.
eapply2 match_app.  eapply2 match_app.
eapply2 program_matching.  split; auto. 
(* 1 *) 
rewrite ! app_nil_r. 
replace (length nil) with 0 by auto. 
rewrite ! map_lift0. 
unfold map; fold map. 
unfold fold_left; fold fold_left. 
unfold app; fold app. 
unfold_op; unfold pattern_size; fold pattern_size. unfold plus; fold plus.
rewrite ! pattern_size_closed; try (rewrite Y_k_closed; omega). 
unfold plus; fold plus.   
unfold length; fold length. 
rewrite ! subst_rec_app. rewrite ! subst_rec_op. 
rewrite ! (subst_rec_closed (Y_k _)); try (rewrite Y_k_closed; omega).
unfold subst; rewrite ! subst_rec_app.  rewrite ! subst_rec_op. 
rewrite ! (subst_rec_closed (Y_k _)); try (rewrite Y_k_closed; omega).
repeat (rewrite subst_rec_ref; insert_Ref_out). 
 unfold lift; rewrite ! lift_rec_lift_rec; try omega. unfold plus. 
rewrite ! subst_rec_lift_rec; try omega. 
rewrite ! lift_rec_null. 
rewrite ! subst_rec_preserves_snd_projection. 
rewrite ! subst_rec_preserves_fst_projection. 
repeat (unfold subst_rec; fold subst_rec; insert_Ref_out). 
 unfold lift; rewrite ! lift_rec_lift_rec; try omega. unfold plus. 
rewrite ! subst_rec_lift_rec; try omega. 
rewrite ! lift_rec_null.
(* 1 *) 
eapply2 preserves_app_sf_red. unfold_op. 
eapply2 preserves_app_sf_red. eapply2 preserves_app_sf_red. 
eapply2 preserves_app_sf_red. eapply2 preserves_app_sf_red. 
eapply2 preserves_app_sf_red. unfold_op. eapply2 fst_out. eapply2 snd_out. 
Qed. 


Lemma add_red_empty: 
forall sigma x u, 
sf_red (App (App (App add (s_op2 sigma x)) u) i_op) (App sigma i_op) .
Proof.
intros. unfold_op;  unfold add at 1. eval_tac. 
eapply transitive_red. eapply2 Y4_fix. 
replace (App (App (Op Aop) (Y_k 4)) add_fn) with add by auto. 
unfold add_fn.
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply2 star_opt_beta3.  auto. 
unfold subst; rewrite ! subst_rec_preserves_extension. 
eapply transitive_red. eapply2 extensions_by_matchfail.
eapply transitive_red. eapply2 extensions_by_matchfail.
eapply transitive_red. eapply2 extensions_by_matchfail.
eapply transitive_red. eapply2 extensions_by_matchfail.
unfold swap; auto. 
rewrite ! subst_rec_preserves_fst_projection. 
repeat (unfold subst_rec; fold subst_rec; insert_Ref_out).
unfold lift. rewrite ! lift_rec_lift_rec; try omega. unfold plus. 
rewrite ! subst_rec_lift_rec; try omega.  
rewrite ! lift_rec_null. 
eapply transitive_red. eapply preserves_app_sf_red. 
eapply2 fst_out. auto. auto.  
Qed. 



