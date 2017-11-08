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

(* 
Add LoadPath ".." as IntensionalLib.
*) 
Require Import Arith Omega Max Bool List.
Require Import IntensionalLib.SF_calculus.General.  
Require Import IntensionalLib.SF_calculus.SF_Terms.  
Require Import IntensionalLib.SF_calculus.SF_Tactics.  
Require Import IntensionalLib.SF_calculus.SF_reduction.  
Require Import IntensionalLib.SF_calculus.SF_Normal.  
Require Import IntensionalLib.SF_calculus.SF_Closed.  
Require Import IntensionalLib.SF_calculus.Substitution.  
Require Import IntensionalLib.SF_calculus.SF_Eval.  
Require Import IntensionalLib.SF_calculus.Star.  
Require Import IntensionalLib.SF_calculus.Fixpoints.  
Require Import IntensionalLib.SF_calculus.Extensions.  
Require Import IntensionalLib.SF_calculus.Equal.  
Require Import IntensionalLib.Closure_to_SF.Tagging.  

From Bignums Require Import BigN. 


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




(* pairing *) 

Definition left_projection M := App (App (App (Op Fop) M) M) k_op. 
Definition right_projection M := App (App (App (Op Fop) M) M) (App k_op i_op). 
Definition fst_projection M := right_projection(left_projection M). 
Definition snd_projection M := right_projection M.  

Lemma fst_out : forall M N, sf_red (fst_projection (s_op2 M N)) M. 
Proof. 
intros; unfold fst_projection, left_projection, right_projection.  unfold_op. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. auto. eapply succ_red. 
eapply2 f_compound_red. eval_tac. eapply succ_red. 
eapply2 f_compound_red. eval_tac. auto. eapply succ_red. 
eapply2 f_compound_red. eval_tac. eval_tac.  
Qed. 

Lemma snd_out : forall M N, sf_red (snd_projection (s_op2 M N)) N. 
Proof. 
intros; unfold snd_projection, left_projection, right_projection.  unfold_op. 
eapply succ_red. eapply2 f_compound_red. eval_tac. eval_tac. 
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

Definition swap M N := App
  (App (Op Sop)
     (App
        (App (Op Sop)
           (App (App (Op Sop) (App (App (Op Fop) (Op Fop)) (Op Sop)))
              (App (App (Op Sop) (App (App (Op Fop) (Op Fop)) (App (Op Sop) (App (App (Op Fop) (Op Fop)) M))))
                 (App (Op Fop) (Op Fop)))))
        (App (App (Op Fop) (Op Fop)) (App (App (Op Sop) (App (Op Fop) (Op Fop))) (App (Op Fop) (Op Fop))))))
  (App (App (Op Fop) (Op Fop)) N)
.

Lemma swap_val: forall M N, swap M N = 
App (App (Op Sop) (star_opt (app_comb (lift 1 M) (Ref 0)))) (App (App (Op Fop) (Op Fop)) N).
Proof.
intros; unfold swap, app_comb; unfold_op. 
rewrite star_opt_occurs_true. 
2: unfold occurs0; fold occurs0. 2: rewrite ! orb_true_r. 2: cbv; auto.
2: discriminate. 
rewrite star_opt_occurs_true. 
2: unfold occurs0; fold occurs0. 2: rewrite ! orb_true_r. 2: cbv; auto.
2: discriminate. 
rewrite star_opt_occurs_true. 
2: unfold occurs0; fold occurs0. 2: rewrite ! orb_true_r. 2: cbv; auto.
2: discriminate. 
 rewrite star_opt_eta. 2: auto. 
unfold star_opt at 1.
 rewrite star_opt_occurs_false. 
2: simpl; unfold lift; rewrite occurs_lift_rec_zero; auto.
unfold_op; unfold lift, subst, subst_rec; fold subst_rec.
rewrite subst_rec_lift_rec; try omega. 
rewrite lift_rec_null.  
rewrite star_opt_closed; auto. 
Qed.

Lemma subst_rec_preserves_swap: 
forall M N P k, subst_rec (swap M N) P k = swap (subst_rec M P k) (subst_rec N P k).
Proof. intros; unfold swap, subst_rec; auto. Qed. 

Lemma pattern_size_swap: 
forall M N, pattern_size(swap M N) = pattern_size M + pattern_size N. 
Proof. intros; unfold swap, pattern_size; fold pattern_size; omega.  Qed. 

Lemma pattern_size_app_comb: 
forall M N, pattern_size(app_comb M N) = pattern_size M + pattern_size N. 
Proof. intros; unfold app_comb. unfold_op; unfold  pattern_size; fold pattern_size; omega.  Qed. 


Definition add_fn := star_opt (star_opt (star_opt 
(* recursion argument, (sigma,x) u  *) 
(* tag *) 
(extension (app_comb(app_comb(app_comb (Y_k 3) (Ref 2)) (Ref 1)) (Ref 0)) 
        (App (App (app_comb (app_comb (Ref 5) (Ref 4)) (Ref 3)) (Ref 1))
             (App (app_comb (app_comb (Ref 5) (Ref 4)) (Ref 3)) (Ref 0)))
(* var *) 
(extension (app_comb (app_comb(Y_k 3) (Ref 1)) (Ref 0))  (* var y *) 
                     (App (App (App (App equal_comb (Ref 0)) 
                                     (snd_projection (Ref 3))) (* y = x *) 
                               (Ref 2))  (* u *) 
                          (App (fst_projection (Ref 3)) 
                               (app_comb (app_comb(Y_k 3) (Ref 1)) (Ref 0))))
                                          (* sigma (var y) *) 
(* add  *) 
(* | Add i u sigma => App (App (Op Aop) add) (s_op2 (s_op2 (lambda_to_fieska sigma) (ref i)) (lambda_to_fieska u))
*) 
(extension (app_comb (app_comb (app_comb (Y_k 4) (Ref 2)) (Ref 1)) (Ref 0))
  (* add (sigma2, x2) u *) 
   (app_comb (app_comb (app_comb (Y_k 4) (Ref 2))
     (s_op2 (App (app_comb (app_comb (Ref 5) (Ref 4)) (Ref 3)) (fst_projection (Ref 1)))
        (snd_projection (Ref 1))))
     (App (app_comb (app_comb (Ref 5) (Ref 4)) (Ref 3)) (Ref 0)))
(* abs = swap (app_comb add (s_op2 sigma x)) t *) 
(extension (swap (app_comb (Ref 3) (App (App (Op Sop) (Ref 2)) (Ref 1))) (Ref 0))
           (swap (app_comb (Ref 3) (App (App (Op Sop) 
                                             (App (app_comb (app_comb (Ref 6) (Ref 5)) (Ref 4)) (Ref 2))) 
                                   (Ref 1)))
                 (Ref 0))
(* dummy case *) 
(fst_projection (Ref 1))
)))))).

Definition add :=  app_comb(Y_k 4) add_fn.


Definition abs sigma x t := swap (app_comb add (s_op2 sigma x)) t .



Lemma add_closed: maxvar add = 0.
Proof.
unfold add. rewrite maxvar_app_comb. rewrite Y_k_closed. unfold max. 
unfold add_fn. rewrite ! maxvar_star_opt. 
repeat (rewrite maxvar_extension; rewrite ? maxvar_app; rewrite ? maxvar_app_comb).
cbv.  auto. 
Qed. 


Lemma abs_red : 
forall sigma x t u, sf_red (App (abs sigma x t) u) 
                           (App (app_comb (app_comb add (s_op2 sigma x)) u) t). 
Proof.
intros; unfold abs. 
rewrite swap_val. 
eapply succ_red. eapply2 s_red. 
eapply transitive_red. eapply preserves_app_sf_red. eapply2 star_opt_beta. 
eval_tac.
unfold subst, lift. rewrite ! subst_rec_preserves_app_comb.
rewrite subst_rec_lift_rec; try omega. 
unfold subst_rec; insert_Ref_out. 
unfold lift; rewrite ! lift_rec_null. 
 auto. 
Qed. 



Lemma add_red_tag: 
forall sigma_x u M N, sf_red (App (App (App add sigma_x) u) (tag M N)) 
                         (App (App (app_comb (app_comb add sigma_x) u) M)
                              (App (app_comb (app_comb add sigma_x) u) N)).
Proof.
intros. unfold add at 1. 
eapply transitive_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. eapply2 app_comb_red.
auto. auto. 
eapply transitive_red. eapply2 Y4_fix. 
replace (app_comb (Y_k 4) add_fn) with add by auto. 
unfold add_fn.
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply2 star_opt_beta3.  auto. 
unfold subst; rewrite ! subst_rec_preserves_extension. 
eapply transitive_red. 
 eapply2 extensions_by_matching.
unfold tag, tag_fix.  
unfold app_comb; unfold_op. 
eapply2 match_app. eapply2 match_app.  
eapply2 match_app. eapply2 match_app. 
eapply2 match_app. eapply2 match_app. 
eapply2 match_app. eapply2 match_app. 
eapply2 match_app. eapply2 match_app. 
eapply2 match_app. eapply2 match_app. 
eapply2 match_app. eapply2 program_matching. 
unfold program; auto. eapply2 program_matching. 
unfold program; auto. eapply2 program_matching. 
unfold program; auto. eapply2 program_matching. 
unfold program; auto.
(* 1 *)  
unfold map, app, length, fold_left, subst.
unfold subst_rec; fold subst_rec. 
rewrite ! subst_rec_preserves_app_comb. 
rewrite ! pattern_size_app_comb.   
unfold pattern_size; fold pattern_size. 
rewrite pattern_size_closed; auto.  unfold plus; fold plus. 
unfold lift. rewrite ! lift_rec_lift_rec; try omega. unfold plus. 
repeat (rewrite subst_rec_ref; insert_Ref_out; unfold pred). 
unfold lift. rewrite ! lift_rec_lift_rec; try omega. unfold plus. 
repeat (rewrite subst_rec_ref; insert_Ref_out; unfold pred). 
rewrite ! subst_rec_lift_rec; try omega.
rewrite ! lift_rec_null. auto. 
Qed. 
  


Lemma add_red_var_unequal: 
forall i u sigma j, program i -> program j -> i <> j -> 
sf_red (App (App (App add (s_op2 sigma i)) u) (var j)) (App sigma (var j)).       
Proof.
intros. unfold_op;  unfold add at 1. 
eapply transitive_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. eapply2 app_comb_red. 
auto. auto. 
eapply transitive_red. eapply2 Y4_fix. 
replace (app_comb (Y_k 4) add_fn) with add by auto. 
unfold add_fn.
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply2 star_opt_beta3.  auto. 
unfold subst; rewrite ! subst_rec_preserves_extension. 
eapply transitive_red. eapply2 extensions_by_matchfail.
unfold var, var_fix, var_fn, app_comb; unfold_op. 
eapply2 matchfail_compound_l. eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r. unfold Y_k, app_comb; unfold_op. 
eapply2 matchfail_compound_l. eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r. unfold A_k, app_comb; unfold_op. 
eapply2 matchfail_compound_l. eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. eapply2 matchfail_compound_l.
eapply2 matchfail_op. unfold factorable. left; eauto. discriminate.
(* 1 *)  
eapply transitive_red. eapply2 extensions_by_matching.
unfold var, var_fix, app_comb; unfold_op. 
eapply2 match_app. eapply2 match_app. eapply2 match_app. 
eapply2 match_app. eapply2 match_app. eapply2 match_app. 
eapply2 match_app. eapply2 match_app. 
apply program_matching. 
unfold program; split. 
nf_out.  auto. 
apply program_matching. 
unfold program; split. 
nf_out.  auto. 
apply program_matching. 
unfold program; split. 
nf_out.  auto. 
(* 1 *) 
unfold map, app, length, fold_left, subst. 
unfold app_comb; unfold_op. 
unfold pattern_size; fold pattern_size.
rewrite ! pattern_size_closed; auto.  unfold plus; fold plus. 
rewrite ! subst_rec_app. rewrite ! (subst_rec_closed equal_comb). 2: auto. 
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
eval_tac. eval_tac. 
Qed.

Lemma add_red_var_equal: 
forall i u sigma, program i -> 
sf_red (App (App (App add (s_op2 sigma i)) u) (var i)) u.       
Proof.
intros. unfold_op;  unfold add at 1. 
eapply transitive_red. eapply preserves_app_sf_red.  
eapply preserves_app_sf_red. eapply2 app_comb_red. 
auto. auto. 
eapply transitive_red. eapply2 Y4_fix. 
replace (app_comb (Y_k 4) add_fn) with add by auto. 
unfold add_fn.
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply2 star_opt_beta3.  auto. 
unfold subst; rewrite ! subst_rec_preserves_extension. 
eapply transitive_red. eapply2 extensions_by_matchfail.
unfold var, var_fix, var_fn, app_comb; unfold_op. 
eapply2 matchfail_compound_l. eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r. unfold Y_k, app_comb; unfold_op. 
eapply2 matchfail_compound_l. eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r. unfold A_k, app_comb; unfold_op. 
eapply2 matchfail_compound_l. eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. eapply2 matchfail_compound_l.
eapply2 matchfail_op. unfold factorable. left; eauto. discriminate.
(* 1 *)  
eapply transitive_red. eapply2 extensions_by_matching.
unfold var, var_fix, app_comb; unfold_op. 
eapply2 match_app. eapply2 match_app. eapply2 match_app. 
eapply2 match_app. eapply2 match_app. eapply2 match_app. 
eapply2 match_app. eapply2 match_app. 
eapply2 program_matching. 
unfold program; split. nf_out. cbv; auto. 
eapply2 program_matching. 
unfold program; split. nf_out. cbv; auto. 
eapply2 program_matching. 
unfold program; split. nf_out. cbv; auto. 
unfold map, app, length, fold_left, subst. 
unfold app_comb at 3 4 5 6 7 8; unfold_op. 
unfold pattern_size; fold pattern_size.
rewrite ! pattern_size_closed; auto.  unfold plus; fold plus. 
rewrite ! subst_rec_app. rewrite ! (subst_rec_closed equal_comb) at 1. 2: auto. 
2: auto. 2: auto. 2: auto. 2: auto. 
rewrite ! subst_rec_preserves_snd_projection. 
rewrite ! subst_rec_preserves_fst_projection. 
repeat (rewrite subst_rec_ref at 1; insert_Ref_out). unfold lift. 
rewrite ! lift_rec_lift_rec; try omega. unfold plus. 
rewrite ! subst_rec_lift_rec; try omega.
rewrite ! lift_rec_null.
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. auto. eapply2 snd_out. auto. auto. 
(* 1 *) 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red.
eapply2 equal_programs. auto. auto. 
eval_tac.  
Qed.



Lemma add_red_abs : 
forall sigma x t sigma_y u, 
  sf_red (App (App (App add sigma_y) u) (abs sigma x t))
         (abs (App (app_comb (app_comb add sigma_y) u) sigma) x t). 
Proof.
intros. unfold add at 1. 
eapply transitive_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. eapply2 app_comb_red. 
auto. auto. 
eapply transitive_red. eapply2 Y4_fix. 
replace (app_comb (Y_k 4) add_fn) with add by auto. 
unfold add_fn.
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply2 star_opt_beta3.  auto. 
unfold subst; rewrite ! subst_rec_preserves_extension. 
eapply transitive_red. eapply2 extensions_by_matchfail.
unfold abs, swap, app_comb; unfold_op; auto. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_op. 
unfold factorable; eauto. discriminate. 
(* 1 *) 
eapply  transitive_red. 
eapply2 extensions_by_matchfail.
unfold abs, swap, app_comb; unfold_op; auto. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_op. 
unfold factorable; eauto. discriminate. 
(* 1 *) 
eapply  transitive_red. 
eapply2 extensions_by_matchfail.
unfold abs, swap, app_comb; unfold_op; auto. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_op. 
unfold factorable; eauto. discriminate. 
(* 1 *) 
eapply  transitive_red. 
eapply2 extensions_by_matching.
unfold abs, swap, app_comb; unfold_op; auto. 
do 20 eapply2 match_app. 
unfold map, app, length, fold_left, subst.  
(* 1 *) 
 unfold abs. rewrite ! subst_rec_preserves_swap. 
rewrite ! subst_rec_preserves_app_comb. 
rewrite ! pattern_size_swap. 
rewrite ! pattern_size_app_comb. 
unfold pattern_size; fold pattern_size. 
unfold lift; rewrite ! lift_rec_null. unfold plus. 
rewrite ! lift_rec_lift_rec; try omega. unfold plus; fold plus. 
repeat (unfold subst_rec; fold subst_rec; insert_Ref_out). 
rewrite ! subst_rec_preserves_app_comb. 
repeat (unfold subst_rec; fold subst_rec; insert_Ref_out). 
unfold lift; rewrite ! lift_rec_null. 
rewrite ! lift_rec_lift_rec; try omega. unfold plus. 
rewrite ! subst_rec_lift_rec; try omega. 
rewrite ! lift_rec_null. 
auto. 
Qed.   





Ltac nf_out :=
  unfold_op;
  match goal with
    | |- normal ?M =>
      match M with
         | app_comb _ _ => apply app_comb_normal; nf_out
          | App (App (Op _) _) _ => apply nf_compound; [| |auto]; nf_out
          | App (Op _) _ => apply nf_compound; [| |auto]; nf_out
          | _ => try apply nf_op
      end
    | _ => auto
        end.



Lemma add_fn_normal: normal add_fn. 
Proof. 
eapply2 pattern_normal_zero. 
unfold add_fn. replace 0 with (pred (pred (pred 3))) by omega. 
repeat apply pattern_normal_star_opt. unfold pred.
apply extension_pattern_normal. 
eapply2 pnf_break. 3: cbv; omega. 
eapply2 pnf_break. 3: cbv; omega.  3: cbv; omega. 
apply pattern_normal_app_comb. 
apply pattern_normal_app_comb. 
eapply2 pnf_normal.
eapply2 pnf_normal.
eapply2 pnf_normal.
eapply2 pnf_normal.
eapply2 pnf_break. 3: cbv; omega. 
apply pattern_normal_app_comb. 
apply pattern_normal_app_comb. 
eapply2 pnf_normal.
eapply2 pnf_normal.
eapply2 pnf_normal.
eapply2 pnf_normal.
(* 1 *) 
apply extension_pattern_normal. 
eapply2 pnf_break. 3: cbv; auto. 3: cbv; auto. 
eapply2 pnf_break. 3: cbv; auto. 3: cbv; auto. 
eapply2 pnf_break. 3: cbv; auto. 3: cbv; auto. 
eapply2 pnf_break. 
eapply2 pnf_normal. eapply2 equal_comb_normal. 
eapply2 pnf_normal. cbv; omega. 
eapply2 pnf_normal.
unfold snd_projection, right_projection.
eapply2 nf_active. unfold_op; nf_out. 
eapply2 pnf_normal.
unfold fst_projection, right_projection, left_projection.
apply pnf_normal.
 apply nf_active. apply nf_active. nf_out. 
apply nf_active. nf_out.  auto. auto. auto. 
cbv; auto. 
eapply2 nf_active. 
nf_out. 
cbv; auto. 
eapply2 app_comb_normal. 
eapply2 app_comb_normal.
cbv; auto.  
(* 1 *) 
apply extension_pattern_normal.
apply pattern_normal_app_comb. 
apply pattern_normal_app_comb. 
apply pattern_normal_app_comb. 
eapply2 pnf_normal.
eapply2 pnf_normal. 
unfold_op.  
apply pnf_break. 3: cbv; omega. 3: cbv; omega. 
apply pnf_break. 3: cbv; omega. 3: cbv; omega. 
eapply2 pnf_normal. 
apply pnf_break. 3: cbv; omega. 3: cbv; omega. 
eapply2 pnf_normal. 
repeat eapply2 app_comb_normal.
unfold fst_projection, right_projection, left_projection. 
apply pnf_normal. 
apply nf_active. nf_out. 
apply nf_active. nf_out. auto. auto. auto. auto. 
eapply2 nf_active. 
unfold_op; auto. 
cbv; auto. 
unfold snd_projection, right_projection, left_projection.
apply pnf_normal.
eapply2 nf_active. unfold_op; auto.
eapply2 pnf_break. 
eapply2 pnf_normal.
nf_out; auto. 
eapply2 pnf_normal.
cbv; omega. 
(* 1 *) 
apply extension_pattern_normal.
2: apply pnf_normal; unfold fst_projection, left_projection, right_projection.
2: apply nf_active; nf_out; auto.
rewrite pattern_size_swap.    
rewrite swap_val. 
eapply2 pnf_break. 3: cbv; omega. 
2: eapply2 pnf_normal.
eapply2 pnf_break. 3: cbv; omega. 
eapply2 pnf_normal.
rewrite pattern_size_app_comb. unfold pattern_size; fold pattern_size. 
unfold plus; fold plus.
cbv.  
repeat (apply pnf_compound;[| | auto; fail]);
try (eapply2 pnf_normal; fail). 
eapply2 pnf_break. 
2: eapply2 pnf_normal.  
2: cbv;  omega. 
apply pnf_normal; nf_out; auto. 
Qed. 
 


  
Lemma add_normal: normal add. 
Proof. 
unfold add. apply app_comb_normal. auto. apply add_fn_normal. 
Qed. 

Lemma abs_normal: 
forall sigma x t, normal sigma -> normal x -> normal t -> normal (abs sigma x t).  
Proof. 
intros. unfold abs, swap. nf_out. 
eapply2 add_normal. auto. auto. auto. 
Qed. 

Lemma add_red_add: 
forall sigma_x u sigma2 y v, 
sf_red (App (App (App add sigma_x) u) (app_comb (app_comb add (s_op2 sigma2 y)) v))  
        (app_comb (app_comb add (s_op2 (App (app_comb (app_comb add sigma_x) u) sigma2) y)) 
        (App (app_comb (app_comb add sigma_x) u) v)). 
Proof.
intros. unfold_op;  unfold add at 1. 
eapply transitive_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. eapply2 app_comb_red. 
auto. auto. 
eapply transitive_red. eapply2 Y4_fix. 
replace (app_comb (Y_k 4) add_fn) with add by auto. 
unfold add_fn.
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply2 star_opt_beta3.  auto. 
unfold subst; rewrite ! subst_rec_preserves_extension. 
(* not a tag *) 
eapply transitive_red. apply extensions_by_matchfail.
unfold add, add_fn, app_comb; unfold_op; auto. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r. 
unfold Y_k, app_comb; unfold_op. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r. 
unfold A_k, app_comb. unfold_op. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r. 
unfold app_comb; unfold_op; cbv. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_op. unfold factorable. left; eauto. discriminate. 
(* 1  not a var *) 
eapply transitive_red. eapply2 extensions_by_matchfail.
unfold add, app_comb; unfold_op; auto. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l.
unfold_op.  
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_l. 
unfold_op. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. unfold_op. 
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_op. unfold factorable. left; eauto. discriminate. 
(* 1 *) 
(* 1 add vs add *) 
eapply transitive_red. eapply2 extensions_by_matching. 
unfold app_comb; unfold_op. 
apply match_app. auto. auto. 
apply match_app. auto. auto. auto. 
apply match_app. auto. auto. 
apply match_app. auto. auto. auto. 
apply match_app. auto. auto. 
eapply2 program_matching.  split; auto. 
apply match_app. auto. auto. auto. 
apply match_app. auto. auto. auto.  
apply match_app. auto. auto. auto. 
apply match_app. auto. auto. auto.  
apply match_app. auto. auto. auto. 
apply match_app. auto. auto. unfold_op. 
apply match_app. auto. auto. auto. 
eapply2 match_app. 
eapply2 match_app. 
eapply2 program_matching.  split; auto. 
unfold_op; eapply2 program_matching. split; auto. 
eapply2 match_app. 
unfold_op; eapply2 program_matching. split; auto. 
eapply2 match_app. 
unfold_op; eapply2 program_matching. split; auto. 
(* 1 *) 
rewrite ! app_nil_r. 
replace (length (nil : list SF)) with 0%nat by auto. 
assert(forall A B f, map (f: A -> B) (nil: list A) = nil) by auto. 
rewrite ! H. unfold app; fold app. 
rewrite 10? map_lift0 at 1. 
unfold length; fold length. 
unfold map; fold map. 
unfold fold_left.
unfold subst; rewrite ! subst_rec_preserves_app_comb. 
rewrite ! (subst_rec_closed (Y_k _)); try (rewrite Y_k_closed; omega).
unfold app_comb at 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19
20 21 22 23 24 25 26 27 28 29 30 31 32 33 34 35 36 37 38. 
unfold_op; unfold pattern_size; fold pattern_size. unfold plus; fold plus.
rewrite ! pattern_size_closed; try (rewrite Y_k_closed; omega). 
unfold plus; fold plus.   
rewrite ! subst_rec_app. 
repeat (rewrite subst_rec_ref; insert_Ref_out). 
 unfold lift; rewrite ! lift_rec_lift_rec; try omega. unfold plus. 
rewrite ! subst_rec_lift_rec; try omega. 
rewrite ! lift_rec_null. rewrite ! subst_rec_op.  
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
eapply2 preserves_app_sf_red. unfold_op. eapply2 preserves_app_sf_red. 
eapply2 preserves_app_sf_red. eapply2 preserves_app_sf_red. 
eapply2 preserves_app_sf_red. eapply2 preserves_app_sf_red. 
eapply2 preserves_app_sf_red. eapply2 fst_out. eapply2 snd_out. 
Qed. 


Lemma add_red_empty: 
forall sigma x u, 
sf_red (App (App (App add (s_op2 sigma x)) u) i_op) (App sigma i_op) .
Proof.
intros. unfold_op;  unfold add at 1. 
eapply transitive_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. eapply2 app_comb_red. 
auto. auto. 
eapply transitive_red. eapply2 Y4_fix. 
replace (app_comb (Y_k 4) add_fn) with add by auto. 
unfold add_fn.
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply2 star_opt_beta3.  auto. 
unfold subst; rewrite ! subst_rec_preserves_extension. 
eapply transitive_red. eapply2 extensions_by_matchfail.
unfold app_comb; unfold_op; auto. 
eapply2 matchfail_compound_l. 
eapply transitive_red. eapply2 extensions_by_matchfail.
unfold app_comb; unfold_op; auto. 
eapply2 matchfail_compound_l. 
eapply transitive_red. eapply2 extensions_by_matchfail.
unfold app_comb; unfold_op; auto. 
eapply2 matchfail_compound_l. 
eapply transitive_red. eapply2 extensions_by_matchfail.
unfold app_comb; unfold_op; auto. 
eapply2 matchfail_compound_l. 
rewrite ! subst_rec_preserves_fst_projection. 
repeat (unfold subst_rec; fold subst_rec; insert_Ref_out).
unfold lift. rewrite ! lift_rec_lift_rec; try omega. unfold plus. 
rewrite ! subst_rec_lift_rec; try omega.  
rewrite ! lift_rec_null. 
eapply transitive_red. eapply preserves_app_sf_red. 
eapply2 fst_out. auto. auto.  
Qed. 



(* delete 

Definition add_fn := star_opt (star_opt (star_opt (star_opt 
(* recursion argument, sigma, x and u *) 
(* tag *) 
(extension (app_comb(app_comb(app_comb (Y_k 3) (Ref 2)) (Ref 1)) (Ref 0)) 
        (App (App (app_comb (app_comb (app_comb( Ref 6) (Ref 5)) (Ref 4)) (Ref 3)) (Ref 1))
             (App (app_comb (app_comb (app_comb( Ref 6) (Ref 5)) (Ref 4)) (Ref 3)) (Ref 1)))
(* var *) 
(extension (app_comb (app_comb(Y_k 3) (Ref 1)) (Ref 0))  (* var y *) 
                     (App (App (App (App equal_comb (Ref 0)) (Ref 3)) (* y = x *) 
                               (Ref 2))  (* u *) 
                          (App (Ref 2) (app_comb (app_comb(Y_k 3) (Ref 1)) (Ref 0))))
                                          (* sigma (var y) *) 
(* delete 
(* abs *)
(extension (app_comb (app_comb 
(app_comb (app_comb(Y_k 4) (Ref 4)) (Ref 3)) (s_op2 (Ref 2) (Ref 1)))
(Ref 0))
           (app_comb (app_comb (app_comb 
(app_comb (Y_k 4) (Ref 4)) (Ref 3))
                                         (s_op2 (App (app_comb(Ref 6) (Ref 5)) (Ref 2)) (Ref 1)))
                               (Ref 0))
*) 


(* add  *) 
(* | Add i u sigma => App (App (Op Aop) add) (s_op2 (s_op2 (lambda_to_fieska sigma) (ref i)) (lambda_to_fieska u))
*) 
(extension (app_comb(app_comb(app_comb (app_comb (Y_k 5) (Ref 3)) (Ref 2)) (Ref 1)) (Ref 0))
  (* add sigma2 x2 u *) 
   (app_comb (app_comb(app_comb (app_comb (Y_k 5) (Ref 3))
     (App (app_comb(app_comb(app_comb (Ref 7) (Ref 6)) (Ref 5)) (Ref 4)) (Ref 2)))
       (Ref 1)) (Ref 0))
(* abs = swap (add sigma2 x2) t *) 
(extension (app_comb (app_comb (Ref 2) (Ref 1)) (Ref 0))
            (app_comb (app_comb (Ref 2) 
              (App (App (App (App (App (Y_k 5) (Ref 6)) (Ref 5)) (Ref 4)) (Ref 3)) (Ref 1))) (Ref 0))
(* dummy case *) 
i_op
))))))).


Lemma size_add_fn : size add_fn = 46759. 
Proof. 
cbv; auto. Qed. 


(* 
abs (A y ys) sigma_x t u  --> abs ys (S(S sigma_x u) y) t
abs nil sigma_x t u --> act t (S sigma_x u) 
act y sigma --> applysub sigma y 
applysub (S (S sigma x) u) x -> u 
applysub (S (S sigma x) u) y -> applysub sigma y 
applysub nil x ---> x 
*) 



*) 


