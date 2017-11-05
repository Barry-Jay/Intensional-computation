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
Require Import IntensionalLib.SF_calculus.Tagging.  

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

Definition add_fn := star_opt (star_opt (* recursion argument and sigma *) 
(* tag *) 
(extension (app_comb(app_comb(app_comb (Y_k 3) (Ref 2)) 
(Ref 1)) (Ref 0)) 
           (App (App (app_comb(Ref 4) (Ref 3)) (Ref 1))
                (App (app_comb(Ref 4) (Ref 3)) (Ref 0)))
(* var *) 
(extension (app_comb (app_comb(Y_k 3) var_fn) (Ref 0))
                     (App (App (App (App equal_comb (Ref 0)) 
                                    (snd_projection (fst_projection (Ref 1)))) (* x *) 
                               (snd_projection (Ref 1))) (* u *) 
                          (App (fst_projection (fst_projection (Ref 1)))  (* sigma *) 
                               (app_comb (app_comb(Y_k 3) var_fn) (Ref 0))))
(* abs *)
(extension (app_comb (app_comb 
(app_comb (app_comb(Y_k 4) (Ref 4)) (Ref 3)) (s_op2 (Ref 2) (Ref 1)))
(Ref 0))
           (app_comb (app_comb (app_comb 
(app_comb (Y_k 4) (Ref 4)) (Ref 3))
                                         (s_op2 (App (app_comb(Ref 6) (Ref 5)) (Ref 2)) (Ref 1)))
                               (Ref 0))
(* add  *) 
(* | Add i u sigma => App (App (Op Aop) add) (s_op2 (s_op2 (lambda_to_fieska sigma) (ref i)) (lambda_to_fieska u))
*) 
(extension (app_comb(Ref 3) 
                (App (App (Op Sop) (App (App (Op Sop) (Ref 2)) (Ref 1))) (Ref 0)))
           (app_comb(Ref 3) 
                (App (App (Op Sop) 
                (App (App (Op Sop) (App (app_comb(Ref 5) (Ref 4)) (Ref 2))) (Ref 1)))
                (App (app_comb(Ref 5) (Ref 4)) (Ref 0))))
(* Nil *) 
(fst_projection (fst_projection (Ref 0)))))))).  

Definition add :=  app_comb(Y_k 3) add_fn.


Definition abs_fn := star_opt  (* rec'n argument *) 
(extension (App (App s_op (Ref 1)) (Ref 0)) (* y::ys *) 
           (star_opt (star_opt (star_opt (* sigma_x t u *) 
             (app_comb (app_comb (app_comb (Ref 5) (Ref 3)) 
                                 (s_op2 (app_comb add (s_op2 (Ref 2) (Ref 0))) (Ref 4)))
                       (Ref 1)))))
           (App k_op (star_opt (star_opt (star_opt (App (app_comb add 
                                                        (s_op2 (Ref 2) (Ref 0)))
                                                        (Ref 1)))))))
.

Definition abs xs sigma_x t := 
  app_comb (app_comb (app_comb 
  (app_comb(Y_k 4) abs_fn) xs) sigma_x) t. 


Lemma add_closed: maxvar add = 0.
Proof.
unfold add. rewrite maxvar_app_comb. rewrite Y_k_closed. unfold max. 
unfold add_fn. rewrite ! maxvar_star_opt. 
repeat (rewrite maxvar_extension; rewrite ? maxvar_app; rewrite ? maxvar_app_comb).
cbv.  auto. 
Qed. 

Lemma abs_fn_closed: maxvar abs_fn = 0. 
Proof.
unfold abs_fn.  rewrite ! maxvar_star_opt. 
rewrite maxvar_extension.  rewrite ? maxvar_star_opt. rewrite ? maxvar_app_comb.
rewrite ? maxvar_app. rewrite ! maxvar_star_opt. 
unfold_op. unfold pattern_size. 
rewrite ! maxvar_app. rewrite maxvar_app_comb. rewrite add_closed. cbv.  auto. 
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
unfold add_fn. replace 0 with (pred (pred 2)) by omega. 
repeat apply pattern_normal_star_opt. unfold pred.
apply extension_pattern_normal. 
eapply2 pnf_break. 3: cbv; auto. 
eapply2 pnf_break. 3: cbv; auto. 
apply pattern_normal_app_comb. 
eapply2 pnf_normal. eapply2 pnf_normal. eapply2 pnf_normal. 
cbv; auto. 
eapply2 pnf_break. 3: cbv; auto. 
apply pattern_normal_app_comb. eapply2 pnf_normal. eapply2 pnf_normal. 
eapply2 pnf_normal.
(* 1 *) 
apply extension_pattern_normal. 
eapply2 pnf_break. 3: cbv; auto. 
eapply2 pnf_break. 3: cbv; auto. 
eapply2 pnf_break. 3: cbv; auto. 
eapply2 pnf_break. 
eapply2 pnf_normal. eapply2 equal_comb_normal. 
eapply2 pnf_normal.
unfold fst_projection, snd_projection, left_projection, right_projection. 
unfold_op. 
eapply2 pnf_active.
eapply2 pnf_compound. eapply2 pnf_compound.  eapply2 pnf_normal. 
eapply2 pnf_active.
eapply2 pnf_compound. eapply2 pnf_compound.  eapply2 pnf_normal. 
eapply2 pnf_active.
eapply2 pnf_compound. eapply2 pnf_compound.  eapply2 pnf_normal. 
 eapply2 pnf_normal.  eapply2 pnf_normal.  eapply2 pnf_normal. 
eapply2 pnf_active.
eapply2 pnf_compound. eapply2 pnf_compound.  eapply2 pnf_normal. 
 eapply2 pnf_normal.  eapply2 pnf_normal.  eapply2 pnf_normal. 
eapply2 pnf_compound.
eapply2 pnf_normal.   eapply2 pnf_normal.
eapply2 pnf_active.
eapply2 pnf_compound. eapply2 pnf_compound.  eapply2 pnf_normal. 
eapply2 pnf_active.
eapply2 pnf_compound. eapply2 pnf_compound.  eapply2 pnf_normal. 
 eapply2 pnf_normal.  eapply2 pnf_normal.  eapply2 pnf_normal. 
eapply2 pnf_active.
eapply2 pnf_compound. eapply2 pnf_compound.  eapply2 pnf_normal. 
 eapply2 pnf_normal.  eapply2 pnf_normal.  eapply2 pnf_normal. 
 eapply2 pnf_normal. nf_out.   eapply2 pnf_normal. nf_out. 
unfold fst_projection, snd_projection, left_projection, right_projection. 
unfold_op. 
eapply2 pnf_active.
eapply2 pnf_normal.   eapply2 pnf_normal. nf_out.  
unfold fst_projection, snd_projection, left_projection, right_projection. 
unfold_op. 
eapply2 pnf_active. eapply2 pnf_active.
eapply2 pnf_normal. nf_out.  eapply2 nf_active. nf_out. 
eapply2 nf_active. nf_out. eapply2 nf_active. nf_out. 
eapply2 nf_active. nf_out. eapply2 nf_active. nf_out.
eapply2 nf_active. nf_out. eapply2 nf_active. nf_out.
eapply2 nf_active. nf_out. eapply2 nf_active. nf_out.
eapply2 nf_active. nf_out. eapply2 nf_active. nf_out.
eapply2 nf_active. nf_out. eapply2 nf_active. nf_out.
eapply2 nf_active. nf_out. nf_out.
(* 3 *) 
eapply2 pnf_normal. nf_out.  
apply pnf_normal. apply app_comb_normal. apply app_comb_normal. 
auto. auto. auto. 
(* 1 *) 
apply extension_pattern_normal.
apply pattern_normal_app_comb. 
apply pattern_normal_app_comb. 
apply pnf_normal. apply app_comb_normal. apply app_comb_normal. 
auto. auto. auto.
unfold_op. apply pnf_compound.  apply pnf_compound.   eapply2 pnf_normal. 
apply pnf_break. 3: simpl; omega. 
apply pnf_normal. eapply2 app_comb_normal. eapply2 pnf_normal.
cbv; auto. auto. eapply2 pnf_normal. auto. eapply2 pnf_normal. 
(* 1 *) 
apply extension_pattern_normal.
apply pattern_normal_app_comb. eapply2 pnf_normal. 
eapply2 pnf_compound. eapply2 pnf_compound. eapply2 pnf_normal.
eapply2 pnf_compound. eapply2 pnf_compound. eapply2 pnf_normal.
apply pnf_break. apply pnf_normal.  nf_out. auto. auto. 
eapply2 pnf_normal. simpl; omega. simpl; omega. eapply2 pnf_normal. 
eapply2 pnf_break. eapply2 pnf_normal.  unfold app_comb; nf_out.
auto. auto. eapply2 pnf_normal. simpl; omega. 
apply pnf_normal. cbv; nf_out. 
apply nf_active. nf_out. apply nf_active. nf_out. 
apply nf_active. nf_out. apply nf_active. nf_out. auto. auto. nf_out. 
auto. 
apply nf_active; nf_out; auto. nf_out.  auto.
apply nf_active; nf_out; auto. nf_out.  auto.
apply nf_active; nf_out; auto.
apply nf_active; nf_out; auto. 
apply nf_active; nf_out; auto. nf_out. auto. 
Qed. 
  
Lemma add_normal: normal add. 
Proof. 
unfold add. apply app_comb_normal. auto. apply add_fn_normal. 
Qed. 

Lemma abs_fn_normal: normal abs_fn. 
Proof. 
eapply2 pattern_normal_zero. 
unfold abs_fn. replace 0 with (pred 1) by omega. 
apply pattern_normal_star_opt. unfold pred.
apply extension_pattern_normal.
unfold_op; unfold pattern_size.   unfold plus. 
replace 3 with (pred (pred (pred 6))) by auto. 
repeat apply pattern_normal_star_opt. unfold pred.
eapply2 pnf_normal.
repeat apply app_comb_normal; auto. nf_out. 
unfold add.  apply app_comb_normal.  auto. eapply2  add_fn_normal. 
auto. auto. auto. 
apply pnf_normal. unfold_op. 
rewrite star_opt_occurs_true. 
2: unfold app_comb; rewrite ! occurs_app. 
2: replace (occurs0 (Ref 0)) with true by auto.  
2: rewrite (orb_true_r (occurs0 (Op Sop) || occurs0 (Ref 2))).
2: rewrite (orb_true_r (occurs0 k_op)).
2: rewrite ! orb_true_r at 1. 2: rewrite ! orb_true_l at 1; auto. 
2: discriminate.  
apply nf_compound. nf_out. 
repeat apply star_opt_normal. 
apply nf_compound. apply nf_compound. nf_out. 
repeat apply star_opt_normal.
apply app_comb_normal. 
apply add_normal. 
nf_out. auto. auto. auto. cbv; auto. auto. auto. 
Qed. 

 

Delimit Scope bigN_scope with bigN.
Local Open Scope bigN_scope.


Fixpoint size M := 
match M with 
| Ref _ => 2 
| Op _ => 1
| App M1 M2 => (size M2) + (size M1)
end .


Lemma size_var_fn : size var_fn = 1079. 
Proof. cbv; auto. Qed. 

Lemma size_add: size add = 47391.
Proof. cbv; auto. Qed. 

Lemma size_abs_fn: size abs_fn = 95603. 
Proof. cbv; auto. Qed. 


Lemma abs_many_red : 
forall x1 xs sigma_x t u, sf_red (App (abs (App (App s_op x1) xs) sigma_x t) u)
                                      (abs xs (s_op2 (app_comb add (s_op2 sigma_x u)) x1) t).
Proof.
intros; unfold abs, abs_fn, s_op2; unfold_op. 
eapply transitive_red. eapply2 app_comb_red. 
eapply transitive_red. eapply preserves_app_sf_red. eapply app_comb_red. auto. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply app_comb_red. auto. auto.
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. eapply app_comb_red. auto. auto. auto. 
eapply transitive_red. eapply preserves_app_sf_red. eapply Y4_fix. auto.  
eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red.  
eapply preserves_app_sf_red.  eapply preserves_app_sf_red. 
eapply2 star_opt_beta. auto. auto. auto. auto.  
unfold subst. rewrite subst_rec_preserves_extension. 
eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red. 
 eapply preserves_app_sf_red.  
eapply extensions_by_matching. 
eapply match_app; nf_out. auto. auto. auto.  
unfold map, app, length, fold_left, subst.  
do 9 (rewrite subst_rec_preserves_star_opt at 1). 
eapply transitive_red.  eapply2 star_opt_beta3.
unfold pattern_size; fold pattern_size. unfold plus; fold plus. 
unfold subst; rewrite 18? subst_rec_preserves_app_comb at 1. 
repeat (unfold subst_rec; fold subst_rec; insert_Ref_out; unfold pred). 
unfold lift; rewrite lift_rec_lift_rec; try omega. unfold plus.
rewrite ! subst_rec_lift_rec; try omega. rewrite ! lift_rec_null.
rewrite ! subst_rec_preserves_app_comb. 
rewrite 6? (subst_rec_closed add) at 1; try (rewrite add_closed; omega). 
repeat (unfold subst_rec; fold subst_rec; insert_Ref_out; unfold pred).  
unfold lift; rewrite lift_rec_lift_rec; try omega. unfold plus.
rewrite ! subst_rec_lift_rec; try omega. rewrite ! lift_rec_null.
auto. 
Qed. 


Lemma abs_red : 
forall sigma_x t u, sf_red (App (abs s_op sigma_x t) u) 
                           (App (app_comb add (s_op2 sigma_x u)) t). 
Proof.
intros; unfold abs, abs_fn, s_op2; unfold_op. 
eapply transitive_red. eapply2 app_comb_red. 
eapply transitive_red. eapply preserves_app_sf_red. eapply app_comb_red. auto. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply app_comb_red. auto. auto.
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. eapply app_comb_red. auto. auto. auto. 
eapply transitive_red. eapply preserves_app_sf_red. eapply Y4_fix. auto.  
eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red.  
eapply preserves_app_sf_red.  eapply preserves_app_sf_red. 
eapply2 star_opt_beta. auto. auto. auto. auto.  
unfold subst. rewrite subst_rec_preserves_extension. 
eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red. 
 eapply preserves_app_sf_red.  
eapply2 extensions_by_matchfail. auto. auto. auto.  
rewrite ! subst_rec_app; rewrite ! subst_rec_op. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. eapply succ_red. eapply f_op_red. 
rewrite ! subst_rec_preserves_star_opt. auto. auto. auto. auto. auto. 
eapply transitive_red. eapply star_opt_beta3. 
unfold subst. (rewrite 4? subst_rec_app at 1).
rewrite ! subst_rec_preserves_app_comb. 
do 4 (rewrite (subst_rec_closed add) at 1; [| rewrite add_closed; omega]).  
repeat (unfold subst_rec; fold subst_rec; insert_Ref_out;  unfold pred).
unfold lift.  rewrite ? lift_rec_lift_rec; try omega. unfold plus; fold plus. 
rewrite ? subst_rec_lift_rec; try omega.
rewrite ? lift_rec_null; try omega. auto. 
Qed. 



Lemma add_red_tag: 
forall sigma M N, sf_red (App (App add sigma) (tag M N)) 
                         (App (App (app_comb add sigma) M) 
                         (App (app_comb add sigma) N)). 
Proof.
intros. unfold_op;  unfold add at 1. 
eapply transitive_red. eapply preserves_app_sf_red. eapply2 app_comb_red. 
auto. 
eapply transitive_red. eapply2 Y3_fix. 
replace (app_comb (Y_k 3) add_fn) with add by auto. 
unfold add_fn.
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply2 star_opt_beta2.  auto. 
unfold subst; rewrite ! subst_rec_preserves_extension. 
eapply transitive_red. eapply2 extensions_by_matching.
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
unfold map, app, length, fold_left, subst. 
unfold app_comb at 3 4 5; unfold_op. 
unfold pattern_size; fold pattern_size. 
rewrite pattern_size_closed; auto.  unfold plus; fold plus. 
unfold app_comb at 3 4 5; unfold_op. 
unfold pattern_size; fold pattern_size. 
rewrite pattern_size_closed; auto.  unfold plus; fold plus. 
unfold lift; rewrite ! lift_rec_null.
rewrite ! subst_rec_app. rewrite ! subst_rec_preserves_app_comb.  
repeat (rewrite subst_rec_ref; insert_Ref_out; unfold pred). 
unfold lift. rewrite ! lift_rec_lift_rec; try omega. unfold plus. 
rewrite ! subst_rec_lift_rec; try omega.
rewrite ! lift_rec_null.
auto. 
Qed. 
  

Lemma add_red_var_unequal: 
forall i u sigma j, program i -> program j -> i <> j -> 
sf_red (App (App add (s_op2 (s_op2 sigma i) u)) (var j)) (App sigma (var j)).       
Proof.
intros. unfold_op;  unfold add at 1. 
eapply transitive_red. eapply preserves_app_sf_red. eapply2 app_comb_red. 
auto. 
eapply transitive_red. eapply2 Y3_fix. 
replace (app_comb (Y_k 3) add_fn) with add by auto. 
unfold add_fn.
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply2 star_opt_beta2.  auto. 
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
apply program_matching. 
unfold program; split.  
apply nf_compound. nf_out.
apply nf_compound. nf_out.
apply nf_compound.
apply nf_compound. nf_out.
apply nf_compound.
apply nf_compound. nf_out.
apply nf_compound. nf_out. auto. auto. auto. 
apply nf_compound. nf_out. auto. auto. auto. auto. 
nf_out. auto. auto. auto. auto. 
eapply2 program_matching.  unfold program; auto. 
unfold map, app, length, fold_left, subst. 
unfold app_comb at 3 4 5 6; unfold_op. 
unfold pattern_size; fold pattern_size.
rewrite ! pattern_size_closed; auto.  unfold plus; fold plus. 
rewrite ! subst_rec_app. rewrite ! (subst_rec_closed equal_comb). 2: auto. 
rewrite ! subst_rec_preserves_snd_projection. 
rewrite ! subst_rec_preserves_fst_projection. 
repeat (rewrite subst_rec_ref at 1; insert_Ref_out). unfold lift. 
rewrite ! lift_rec_lift_rec; try omega. unfold plus. 
rewrite ! subst_rec_lift_rec; try omega.
rewrite ! lift_rec_null.
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. auto. 
eapply transitive_red. eapply snd_preserves_sf_red. eapply2 fst_out.
eapply2 snd_out.  
eapply transitive_red. eapply snd_out. auto. 
eapply preserves_app_sf_red.
eapply fst_preserves_sf_red. eapply2 fst_out. auto. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red.
eapply2 unequal_programs. auto. 
eapply transitive_red. eapply preserves_app_sf_red. eapply2 fst_out. auto. 
auto. unfold_op.  
eapply transitive_red. eapply preserves_app_sf_red. 
eapply succ_red. eapply2 f_op_red. auto. auto. 
eapply succ_red. eapply2 s_red. 
eapply succ_red. eapply2 f_op_red.
rewrite ! subst_rec_preserves_app_comb. 
repeat (rewrite subst_rec_ref at 1; insert_Ref_out). 
rewrite ! subst_rec_closed; auto.
unfold lift; rewrite lift_rec_null; auto.  
Qed.

Lemma add_red_var_equal: 
forall i u sigma, program i -> 
sf_red (App (App add (s_op2 (s_op2 sigma i) u)) (var i)) u.       
Proof.
intros. unfold_op;  unfold add at 1. 
eapply transitive_red. eapply preserves_app_sf_red. eapply2 app_comb_red. 
auto. 
eapply transitive_red. eapply2 Y3_fix. 
replace (app_comb (Y_k 3) add_fn) with add by auto. 
unfold add_fn.
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply2 star_opt_beta2.  auto. 
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
eapply2 program_matching. 
unfold program; split. nf_out. cbv; auto. 
nf_out. auto. auto. 
eapply2 program_matching.  unfold program; auto. 
unfold map, app, length, fold_left, subst. 
unfold app_comb at 3 4 5 6; unfold_op. 
unfold pattern_size; fold pattern_size.
rewrite ! pattern_size_closed; auto.  unfold plus; fold plus. 
rewrite ! subst_rec_app. rewrite ! (subst_rec_closed equal_comb). 2: auto. 
rewrite ! subst_rec_preserves_snd_projection. 
rewrite ! subst_rec_preserves_fst_projection. 
repeat (rewrite subst_rec_ref at 1; insert_Ref_out). unfold lift. 
rewrite ! lift_rec_lift_rec; try omega. unfold plus. 
rewrite ! subst_rec_lift_rec; try omega.
rewrite ! lift_rec_null.
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. auto. 
eapply transitive_red. eapply snd_preserves_sf_red. eapply2 fst_out.
eapply2 snd_out.  
eapply transitive_red. eapply snd_out. auto. 
eapply preserves_app_sf_red.
eapply fst_preserves_sf_red. eapply2 fst_out. auto. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red.
eapply2 equal_programs. auto. 
eapply transitive_red. eapply preserves_app_sf_red. eapply2 fst_out. auto. 
auto. unfold_op.  
eapply succ_red. eapply2 f_op_red. auto. 
Qed.





Lemma add_red_empty: 
forall sigma x u, 
sf_red (App (App add (s_op2 (s_op2 sigma x) u)) i_op) (App sigma i_op) .
Proof.
intros. unfold_op;  unfold add at 1. 
eapply transitive_red. eapply preserves_app_sf_red. eapply2 app_comb_red. 
auto. 
eapply transitive_red. eapply2 Y3_fix. 
replace (app_comb (Y_k 3) add_fn) with add by auto. 
unfold add_fn.
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply2 star_opt_beta2.  auto. 
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
unfold subst_rec; fold subst_rec. insert_Ref_out.
unfold lift. rewrite lift_rec_lift_rec; try omega. unfold plus. 
rewrite ! subst_rec_lift_rec; try omega.  
rewrite ! lift_rec_null. 
eapply transitive_red. eapply preserves_app_sf_red. 
eapply fst_preserves_sf_red. eapply2 fst_out. auto. 
eapply transitive_red. eapply preserves_app_sf_red. 
eapply2 fst_out. auto. auto. 
Qed. 


Lemma add_red_abs : 
forall xs sigma x t sigma2, 
  sf_red (App (App add sigma2) (abs xs (s_op2 sigma x) t))
         (abs xs (s_op2 (App (app_comb add sigma2) sigma) x) t)
.
Proof.
intros. unfold_op;  unfold add at 1. 
eapply transitive_red. eapply preserves_app_sf_red. eapply2 app_comb_red. 
auto. 
eapply transitive_red. eapply2 Y3_fix. 
replace (app_comb (Y_k 3) add_fn) with add by auto. 
unfold add_fn.
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply2 star_opt_beta2.  auto. 
unfold subst; rewrite ! subst_rec_preserves_extension. 
eapply transitive_red. eapply2 extensions_by_matchfail.
unfold abs, app_comb; unfold_op; auto. 
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
unfold A_k, app_comb; unfold_op.  
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_op. unfold_op; 
unfold factorable; split_all; left; eauto. discriminate.
(* 1 *)  
eapply  transitive_red. 
eapply2 extensions_by_matchfail.
unfold abs, app_comb; unfold_op; auto. 
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
unfold A_k, app_comb; unfold_op.  
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_op. unfold_op; 
unfold factorable; split_all; left; eauto. discriminate.
(* 1 *)  
eapply  transitive_red. 
eapply2 extensions_by_matching.
unfold abs, app_comb; unfold_op; auto. 
do 20 eapply2 match_app. 
eapply2 program_matching. 
unfold map, app, length, fold_left, subst. 
unfold subst. 
rewrite ! subst_rec_preserves_app_comb. 
rewrite ! (subst_rec_closed (Y_k _)). 
unfold lift; rewrite ! lift_rec_null. 
unfold app_comb at 5 6 7 8. 
unfold_op; unfold pattern_size; fold pattern_size. unfold plus; fold plus. 
rewrite pattern_size_closed. 
2: auto.  2: auto. 2: auto.  2: auto. 2: auto.  2: auto. 2: auto.  
unfold app_comb at 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20
21 22 23 24 25 26 27 28 29 30 31 32 33 34. 
unfold_op; unfold pattern_size; fold pattern_size. 
rewrite pattern_size_closed. unfold plus; fold plus. 
repeat (rewrite subst_rec_ref; insert_Ref_out). 
unfold subst_rec; fold subst_rec. insert_Ref_out. 
repeat (rewrite subst_rec_ref; insert_Ref_out). 
unfold lift; rewrite ! lift_rec_lift_rec; try omega. unfold plus; fold plus. 
rewrite ! subst_rec_lift_rec; try omega.
rewrite ! lift_rec_null. auto. 
auto. 
unfold app_comb; unfold_op; unfold pattern_size; fold pattern_size. 
rewrite pattern_size_closed. unfold plus; fold plus. 
rewrite Y_k_closed. omega. 
auto.
unfold app_comb; unfold_op; unfold pattern_size; fold pattern_size. 
rewrite pattern_size_closed. unfold plus; fold plus. 
rewrite Y_k_closed. omega. auto. 
Qed.   

Lemma size_add_fn : size add_fn = 46759. 
Proof. 
cbv; auto. Qed. 

Lemma add_red_add: 
forall i u sigma sigma2, 
sf_red (App (App add sigma) (app_comb add (s_op2 (s_op2 sigma2 i) u)))
        (app_comb add (s_op2 (s_op2 (App (app_comb add sigma) sigma2) i) 
        (App (app_comb add sigma) u))). 
Proof.
intros. unfold_op;  unfold add at 1. 
eapply transitive_red. eapply preserves_app_sf_red. eapply2 app_comb_red. 
auto. 
eapply transitive_red. eapply2 Y3_fix. 
replace (app_comb (Y_k 3) add_fn) with add by auto. 
unfold add_fn.
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply2 star_opt_beta2.  auto. 
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
eapply2 matchfail_compound_r. 
eapply2 program_matching. 
unfold program; split; auto.  
eapply2 matchfail_compound_r. 
assert(matchfail var_fn add_fn \/ exists sigma, matching var_fn add_fn sigma).
apply match_program. auto. 
unfold program; split. apply add_fn_normal. 
unfold add_fn. rewrite ! maxvar_star_opt. 
repeat (rewrite maxvar_extension; rewrite ? maxvar_app; rewrite ? maxvar_app_comb).
cbv.  auto.
inversion H. auto. inversion H0. 

assert(matchfail var_fn add_fn \/ exists sigma, matching var_fn add_fn sigma).
apply match_program. apply var_fn_normal. split. 
apply add_fn_normal.  
unfold add_fn. rewrite ! maxvar_star_opt. 
repeat (rewrite maxvar_extension; rewrite ? maxvar_app; rewrite ? maxvar_app_comb).
cbv.  auto.
inversion H2. auto. 
inversion H3. 
assert(add_fn = var_fn /\ x0 = nil) . 
apply program_matching3. auto.  apply var_fn_closed.
inversion H5. 
assert(size add_fn = size var_fn) by congruence.  
rewrite size_var_fn in H8; rewrite size_add_fn in H8. 
discriminate. 
(* 1 abs vs add *) 
eapply transitive_red. eapply2 extensions_by_matchfail.
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
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_op. unfold factorable. left; eauto. discriminate. 
(* 1 add vs add *) 
eapply transitive_red. eapply2 extensions_by_matching. 
unfold app_comb; unfold_op. 
repeat eapply2 match_app. 
rewrite ! app_nil_r. 
replace (length (nil : list SF)) with 0%nat by auto. 
assert(forall A B f, map (f: A -> B) (nil: list A) = nil) by auto. 
rewrite ! H. unfold app; fold app. 
rewrite 40? map_lift0 at 1. 
unfold length; fold length. 
unfold map; fold map. 
unfold fold_left. 
replace  (0 +
                     pattern_size
                       (app_comb (Ref 3)
                          (App (App (Op Sop) (App (App (Op Sop) (Ref 2)) (Ref 1))) (Ref 0))))%nat
with 4%nat by (cbv; auto). 
unfold subst; rewrite ! subst_rec_preserves_app_comb. 
rewrite ! subst_rec_app. rewrite ! subst_rec_op. 
rewrite ! subst_rec_preserves_app_comb.
repeat (unfold subst_rec; fold subst_rec; insert_Ref_out). 
 unfold lift; rewrite ! lift_rec_lift_rec; try omega. unfold plus. 
rewrite ! subst_rec_lift_rec; try omega. 
rewrite ! lift_rec_null. auto. 
Qed. 

(* 
abs (A y ys) sigma_x t u  --> abs ys (S(S sigma_x u) y) t
abs nil sigma_x t u --> act t (S sigma_x u) 
act y sigma --> applysub sigma y 
applysub (S (S sigma x) u) x -> u 
applysub (S (S sigma x) u) y -> applysub sigma y 
applysub nil x ---> x 
*) 




