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
Require Import IntensionalLib.Closure_to_Fieska.Tagging.


Ltac unfold_op := unfold pair, a_op, i_op, id, k_op, f_op, s_op. 


Lemma pair_normal: forall M N, normal M -> normal N -> normal (pair M N). 
Proof. intros; unfold_op; nf_out. Qed. 

Lemma k_op_normal: forall M, normal M -> normal (App (App (Op Fop) (Op Fop)) M).
Proof. intros;  unfold_op; nf_out. Qed. 

Ltac nf_out2 := 
match goal with 
| |- normal (pair _ _) => apply pair_normal; nf_out2
| |- normal (App (App (Op Fop) (Op Fop)) _) => apply k_op_normal; nf_out2
| _ => nf_out
end. 



(* pairing *) 

Definition left_projection M := App (App (App (Op Fop) M) M) k_op. 
Definition right_projection M := App (App (App (Op Fop) M) M) (App k_op i_op). 
Definition fst_projection M := right_projection(left_projection M). 
Definition snd_projection M := right_projection M.  

Lemma fst_red : forall M N, sf_red (fst_projection (pair M N)) M. 
Proof. 
intros; unfold fst_projection, left_projection, right_projection.  unfold_op. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. auto. eapply succ_red. 
eapply2 f_compound_red. eval_tac. eapply succ_red. 
eapply2 f_compound_red. eval_tac. auto. eapply succ_red. 
eapply2 f_compound_red. eval_tac. 
Qed. 

Lemma snd_red : forall M N, sf_red (snd_projection (pair M N)) N. 
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



Lemma pattern_size_app_comb: 
forall M N, pattern_size(app_comb M N) = pattern_size M + pattern_size N. 
Proof. intros; unfold app_comb. unfold_op; unfold  pattern_size; fold pattern_size; omega.  Qed. 



Definition star_opt_app_comb M N := 
App (App (Op Sop) (App (Op Kop) (App (Op Aop) M))) N.


Lemma star_opt_app_comb_red: 
forall M N P, sf_red (App (star_opt_app_comb M N) P) (app_comb M (App N P)).
Proof.
intros; unfold star_opt_app_comb, app_comb. eval_tac.  eval_tac. 
Qed. 



Definition add_fn := star_opt (star_opt
(* recursion argument, ((sigma,x),u)  *) 
(extension (app_comb (Ref 1) (Ref 0)) 
(* tag *) 
        (App (extension (app_comb (Ref 1) (Ref 0)) 
                        (App (App (App (Ref 5) (Ref 4)) (Ref 1))
                             (App (App (Ref 5) (Ref 4)) (Ref 0)))
(* add *) 
             (extension (App (App (Op Fop) (App (App (Op Fop) (Ref 2)) (Ref 1))) (Ref 0)) 
                        (app_comb (Ref 4) 
                                  (App (App (Op Fop) (App (App (Op Fop) 
                                                               (App (App (Ref 6) (Ref 5)) (Ref 2)))
                                                     (Ref 1)))
                                       (App (App (Ref 6) (Ref 5)) (Ref 0))))
(* var *) 
             (App k_op (App (App (App (App (Op Eop) (Ref 0)) 
                                     (snd_projection (fst_projection (Ref 2)))) (* y = x *) 
                               (snd_projection (Ref 2)))  (* u *) 
                          (App (fst_projection (fst_projection (Ref 2)))
                               (app_comb (Ref 1) (Ref 0)))))
                                          (* sigma (var y) *) 


 )) (Ref 0))

(* abs *) 
(extension (App (App (Op Sop) (star_opt_app_comb (Ref 3)
                         (App (Op Fop) (pair (Ref 2) (Ref 1))))) (App k_op (Ref 0)))
           (App (App (Op Sop) (star_opt_app_comb (Ref 3)
                         (App (Op Fop) (pair (App (App (Ref 5) (Ref 4)) (Ref 2)) (Ref 1))))) (App k_op (Ref 0)))
(* Iop  *) 
(fst_projection (fst_projection (Ref 0))))
)).

Definition add M :=  app_comb (app_comb (app_comb omega3 omega3) add_fn) M.

Definition abs sigma x t := 
App (App (Op Sop)  (star_opt_app_comb (app_comb (app_comb omega3 omega3) add_fn) 
                         (App (Op Fop) (pair sigma x)))) 
    (App k_op t) .

Lemma Y3_to_add: forall sigma, sf_red (App (Y3 add_fn) sigma) (add sigma). 
Proof. 
intros. unfold Y3, app_comb. 
eapply transitive_red.  eapply2 star_opt_beta. 
unfold subst; rewrite ! subst_rec_app. 
rewrite ! (subst_rec_closed omega3). 2: unfold omega3; cbv; auto. 
unfold lift; rewrite subst_rec_lift_rec; try omega.  
unfold subst_rec; fold subst_rec. insert_Ref_out.
unfold lift; rewrite ! lift_rec_null.
unfold add; eapply2 zero_red. 
Qed.


Lemma maxvar_add: forall M, maxvar (add M) = maxvar M.
Proof.
unfold add, app_comb. intros. unfold maxvar; fold maxvar. 
replace (maxvar omega3) with 0 by (unfold omega3; cbv; auto). 
replace (maxvar add_fn) with 0. simpl; omega. 
unfold add_fn. rewrite ! maxvar_star_opt. 
repeat (rewrite maxvar_extension; rewrite ? maxvar_app; rewrite ? maxvar_app_comb).
cbv.  auto. 
Qed. 


Lemma abs_red : 
forall sigma x t u, sf_red (App (abs sigma x t) u) 
                           (App (add (pair (pair sigma x) u)) t). 
Proof.
intros; unfold abs, app_comb. eval_tac.  
eapply transitive_red. eapply preserves_app_sf_red. eapply2 star_opt_app_comb_red. eval_tac.  
eapply2 preserves_app_sf_red. 
Qed. 

Lemma lift_rec_preserves_Y3: forall M n k, lift_rec (Y3 M) n k = Y3 (lift_rec M n k).
Proof. 
intros. unfold Y3, app_comb.  rewrite lift_rec_preserves_star_opt. 
unfold lift, lift_rec; fold lift_rec; rewrite lift_lift_rec; try omega.
rewrite ! (lift_rec_closed omega3).  unfold  lift_rec; fold lift_rec. relocate_lt.  auto. 
unfold omega3; cbv; auto.
Qed.   


Lemma add_red_tag: 
forall sigma M N, sf_red (App (add sigma) (tag M N)) 
                         (App (App (add sigma) M)
                              (App (add sigma) N)).
Proof.
intros. unfold add at 1, app_comb. eval_tac. eval_tac. eval_tac. 
eapply transitive_red. eapply preserves_app_sf_red.  eapply2 omega3_omega3. auto. 
(* 1 *) 
unfold add_fn, app_comb. 
eapply transitive_red. eapply  preserves_app_sf_red.
eapply2 star_opt_beta2. auto.  
unfold subst; rewrite ! subst_rec_preserves_extension. 
(* an app_comb *) 
eapply transitive_red. 
 eapply2 extensions_by_matching.
unfold tag, var, app_comb.  
eapply2 match_app.  
(* 1 *)  
unfold map, app, length, fold_left, subst.
unfold subst_rec; fold subst_rec. 
rewrite ! subst_rec_preserves_extension.
rewrite ! subst_rec_app. 
(* an app_comb *) 
eapply transitive_red. 
 eapply2 extensions_by_matching.
repeat (rewrite ? subst_rec_ref; insert_Ref_out). 
unfold lift; rewrite ! lift_rec_null.
rewrite subst_rec_lift_rec; try omega. 
rewrite ! lift_rec_null. 
eapply2 match_app.  
(* 1 *)  
unfold map, app, length, fold_left, subst.
rewrite ! subst_rec_app. 
unfold pattern_size; fold pattern_size. unfold plus. 
do 6 (rewrite subst_rec_ref at 1; insert_Ref_out; unfold pred). 
unfold lift; rewrite 4? subst_rec_lift_rec; try omega. 
rewrite lift_rec_preserves_Y3. 
(* tidying up *) 
rewrite ! lift_rec_lift_rec; try omega. unfold plus. 
rewrite ! subst_rec_lift_rec; try omega. 
unfold lift; rewrite ! lift_rec_null. 
(* 1 *) 
do 3 (rewrite subst_rec_ref; insert_Ref_out). 
do 7 (rewrite subst_rec_ref at 1; insert_Ref_out). 
(rewrite subst_rec_ref at 1; insert_Ref_out). 
unfold lift; rewrite ! lift_rec_lift_rec; try omega. unfold plus. 
rewrite ! subst_rec_lift_rec; try omega. 
unfold lift; rewrite ! lift_rec_null. 
unfold subst_rec; fold subst_rec. 
(* 1 *) 
replace (star_opt (star_opt
(* recursion argument, ((sigma,x),u)  *) 
(extension (App (App (Op Aop) (Ref 1)) (Ref 0)) 
(* tag *) 
        (App (extension (App (App (Op Aop) (Ref 1)) (Ref 0)) 
                        (App (App (App (Ref 5) (Ref 4)) (Ref 1))
                             (App (App (Ref 5) (Ref 4)) (Ref 0)))
(* add *) 
             (extension (App (App (Op Fop) (App (App (Op Fop) (Ref 2)) (Ref 1))) (Ref 0)) 
                        (App (App (Op Aop) (Ref 4))
                                  (App (App (Op Fop) (App (App (Op Fop) 
                                                               (App (App (Ref 6) (Ref 5)) (Ref 2)))
                                                     (Ref 1)))
                                       (App (App (Ref 6) (Ref 5)) (Ref 0))))
(* var *) 
             (App k_op (App (App (App (App (Op Eop) (Ref 0)) 
                                     (snd_projection (fst_projection (Ref 2)))) (* y = x *) 
                               (snd_projection (Ref 2)))  (* u *) 
                          (App (fst_projection (fst_projection (Ref 2)))
                               (App (App (Op Aop) (Ref 1)) (Ref 0)))))
                                          (* sigma (var y) *) 


 )) (Ref 0))

(* abs *) 
(extension (App (App (Op Sop) (star_opt_app_comb (Ref 3)
                         (App (Op Fop) (pair (Ref 2) (Ref 1))))) (App k_op (Ref 0)))
           (App (App (Op Sop) (star_opt_app_comb (Ref 3)
                         (App (Op Fop) (pair (App (App (Ref 5) (Ref 4)) (Ref 2)) (Ref 1))))) (App k_op (Ref 0)))
(* Iop  *) 
(fst_projection (fst_projection (Ref 0))))
)))
with add_fn by auto. 
apply preserves_app_sf_red;
apply preserves_app_sf_red; 
try (eapply2 zero_red; fail);  
apply Y3_to_add. 
Qed. 




Lemma add_red_var_unequal: 
forall i u sigma j, program i -> program j -> i <> j -> 
matchfail (app_comb (Ref 1) (Ref 0)) j -> 
matchfail  (App (App (Op Fop) (App (App (Op Fop) (Ref 2)) (Ref 1))) (Ref 0)) j -> 
sf_red (App (add (pair (pair sigma i) u)) (var j)) (App sigma (var j)).       
Proof.
intros. unfold_op;  unfold add at 1, app_comb. eval_tac. eval_tac. eval_tac.  
eapply transitive_red. eapply preserves_app_sf_red. eapply2 omega3_omega3. auto. 
(* 1 *)
unfold add_fn, app_comb.
eapply transitive_red. 
eapply preserves_app_sf_red.  eapply2 star_opt_beta2. auto. 
unfold subst; rewrite ! subst_rec_preserves_extension. 
eapply transitive_red. eapply2 extensions_by_matching.
unfold var, var_fn, app_comb; unfold_op. 
 eapply2 match_app.   
(* 1 *)  
unfold map, app, length, fold_left, subst.
unfold subst_rec; fold subst_rec. 
rewrite ! subst_rec_preserves_extension.
rewrite ! subst_rec_app. 
(* not an app_comb *) 
eapply transitive_red. 
 eapply2 extensions_by_matchfail.
repeat (rewrite ? subst_rec_ref; insert_Ref_out). 
unfold lift; rewrite ! lift_rec_null.
rewrite subst_rec_lift_rec; try omega. 
rewrite ! lift_rec_null. auto. 
(* not a pair *) 
eapply transitive_red. 
 eapply2 extensions_by_matchfail.
repeat (rewrite ? subst_rec_ref; insert_Ref_out). 
unfold lift; rewrite ! lift_rec_null.
rewrite subst_rec_lift_rec; try omega. 
rewrite ! lift_rec_null. auto. 
(* 1 *) 
rewrite ! (subst_rec_closed k_op); unfold_op; auto.
rewrite ! (subst_rec_closed (Op Eop)); auto. 
unfold pattern_size; fold pattern_size. unfold plus. 
do 3 (rewrite subst_rec_ref at 1; insert_Ref_out; unfold pred). 
unfold lift; rewrite lift_rec_null;
rewrite 4? subst_rec_lift_rec; try omega. 
rewrite ! lift_rec_null. 
rewrite ! subst_rec_preserves_snd_projection. 
rewrite ! subst_rec_preserves_fst_projection. 
do 3 (rewrite subst_rec_ref at 1; insert_Ref_out). 
unfold lift; rewrite ! lift_rec_lift_rec; try omega. unfold plus. 
rewrite ! subst_rec_lift_rec; try omega.
rewrite ! lift_rec_null. eval_tac. 
(* 1 *) 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. auto.
eapply snd_preserves_sf_red. eapply2 fst_red. eapply2 snd_red. 
eapply preserves_app_sf_red.
eapply transitive_red. 
eapply fst_preserves_sf_red. eapply2 fst_red. eapply2 fst_red. auto. 
(* 1 *) 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. eapply2 zero_red. eapply2 snd_red. auto. eapply2 zero_red. 
(* 1 *)  
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply2 unequal_programs. auto. eapply2 zero_red.  eval_tac.
apply preserves_app_sf_red. auto.  
insert_Ref_out. 
unfold lift; rewrite ! lift_rec_null. 
rewrite ! subst_rec_lift_rec; try omega. 
rewrite ! lift_rec_null. eapply2 zero_red. 
Qed. 


Lemma add_red_var_equal: 
forall i u sigma, program i -> 
matchfail (app_comb (Ref 1) (Ref 0)) i -> 
matchfail  (App (App (Op Fop) (App (App (Op Fop) (Ref 2)) (Ref 1))) (Ref 0)) i -> 
sf_red (App (add (pair (pair sigma i) u)) (var i)) u.    
Proof.
intros. unfold_op;  unfold add at 1, app_comb. eval_tac. eval_tac. eval_tac. 
eapply transitive_red. eapply preserves_app_sf_red. eapply2 omega3_omega3. auto. 
(* 1 *)
unfold add_fn, app_comb.
eapply transitive_red. 
eapply preserves_app_sf_red.  eapply2 star_opt_beta2. auto. 
unfold subst; rewrite ! subst_rec_preserves_extension. 
eapply transitive_red. eapply2 extensions_by_matching.
unfold var, var_fn, app_comb; unfold_op. 
 eapply2 match_app.  
(* 1 *)  
unfold map, app, length, fold_left, subst.
unfold subst_rec; fold subst_rec. 
rewrite ! subst_rec_preserves_extension.
rewrite ! subst_rec_app. 
(* not an app_comb *) 
eapply transitive_red. 
 eapply2 extensions_by_matchfail.
repeat (rewrite ? subst_rec_ref; insert_Ref_out). 
unfold lift; rewrite ! lift_rec_null.
rewrite subst_rec_lift_rec; try omega. 
rewrite ! lift_rec_null. auto. 
(* not a pair *) 
eapply transitive_red. 
 eapply2 extensions_by_matchfail.
repeat (rewrite ? subst_rec_ref; insert_Ref_out). 
unfold lift; rewrite ! lift_rec_null.
rewrite subst_rec_lift_rec; try omega. 
rewrite ! lift_rec_null. auto. 
(* 1 *) 
rewrite ! (subst_rec_closed k_op); unfold_op; auto. 
unfold pattern_size; fold pattern_size. unfold plus. 
do 3 (rewrite subst_rec_ref at 1; insert_Ref_out; unfold pred). 
unfold lift; rewrite lift_rec_null;
rewrite 4? subst_rec_lift_rec; try omega. 
rewrite ! lift_rec_null. 
rewrite subst_rec_lift_rec; try omega. 
rewrite ! lift_rec_null. 
rewrite ! subst_rec_preserves_snd_projection. 
rewrite ! subst_rec_preserves_fst_projection. 
do 3 (rewrite subst_rec_ref at 1; insert_Ref_out). 
unfold lift; rewrite ! lift_rec_lift_rec; try omega. unfold plus. 
rewrite ! subst_rec_lift_rec; try omega.
rewrite ! lift_rec_null.
unfold subst_rec; fold subst_rec. eval_tac.  
(* 1 *) 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. eapply2 zero_red. 
eapply snd_preserves_sf_red. eapply2 fst_red. eapply2 snd_red. 
eapply preserves_app_sf_red.
eapply transitive_red. 
eapply fst_preserves_sf_red. eapply2 fst_red. eapply2 fst_red. auto. 
(* 1 *) 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. eapply2 zero_red. eapply2 snd_red. auto. eapply2 zero_red. 
(* 1 *) 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply2 equal_programs. auto. eapply2 zero_red.  eval_tac. 
Qed. 




Lemma add_red_abs : 
forall sigma x t sigma2, 
  sf_red (App (add sigma2) (abs sigma x t))
         (abs (App (add sigma2) sigma) x t). 
Proof.
intros. unfold add at 1, app_comb. eval_tac. eval_tac. eval_tac. 
eapply transitive_red. eapply preserves_app_sf_red. eapply2 omega3_omega3. auto. 
(* 1 *)
unfold add_fn, app_comb.
eapply transitive_red. 
eapply preserves_app_sf_red.  eapply2 star_opt_beta2. auto. 
unfold subst; rewrite ! subst_rec_preserves_extension. 
eapply transitive_red. eapply2 extensions_by_matchfail.
(* abs not an app_comb *) 
unfold abs, star_opt_app_comb, app_comb; unfold_op. 
eapply2 matchfail_compound_l.   
eapply2 matchfail_compound_l.
eapply2 matchfail_op. unfold factorable; eauto. discriminate. 
(* an abs *) 
eapply transitive_red. eapply2 extensions_by_matching. 
unfold abs, star_opt_app_comb, pair; unfold_op. 
eapply2 match_app.  eapply2 match_app.  
eapply2 match_app. eapply2 match_app. 
eapply2 match_app.  
unfold map, app, length, fold_left, subst.  
(* 1 *) 
unfold star_opt_app_comb. 
unfold_op; unfold pattern_size; fold pattern_size. unfold plus; fold plus. 
rewrite !  subst_rec_app. rewrite !  subst_rec_op.
unfold lift; rewrite ! lift_rec_null. 
do 12 (rewrite subst_rec_ref at 1; insert_Ref_out). 
unfold lift; rewrite ! lift_rec_lift_rec; try omega. 
unfold plus. 
rewrite ! subst_rec_lift_rec; try omega. 
rewrite ! lift_rec_null. 
repeat (rewrite subst_rec_ref at 1; insert_Ref_out). 
unfold lift; rewrite ! lift_rec_lift_rec; try omega. 
unfold plus. 
rewrite ! subst_rec_lift_rec; try omega. 
rewrite ! lift_rec_null. 
unfold abs, app_comb. 
auto. 
Qed.   





Ltac nf_out :=
  unfold_op;
  match goal with
    | |- normal ?M =>
      match M with
         | App (App (Op _) _) _ => apply nf_compound; [| |auto]; nf_out
          | App (Op _) _ => apply nf_compound; [| |auto]; nf_out
          | _ => try apply nf_op
      end
    | _ => auto
        end.



Lemma add_fn_normal: normal add_fn. 
Proof. 
unfold add_fn. unfold_op. 
repeat apply star_opt_normal. 
unfold fst_projection, snd_projection, left_projection, right_projection. 
cbv; nf_out; repeat (eapply2 nf_active; nf_out); auto.
Qed. 

  


  
Lemma add_normal: forall f, normal f -> normal (add f). 
Proof. 
unfold add, app_comb. intros. 
apply nf_compound. 2: auto. 2: auto. 
apply nf_compound. auto. 2: auto. 
apply nf_compound. 2: eapply2 add_fn_normal. 2: auto. 
apply nf_compound. auto. 2: auto. 
apply nf_compound. 
apply nf_compound. auto. 2: auto. 
eapply2 omega3_program. eapply2 omega3_program. auto.  
Qed. 

Lemma abs_normal: 
forall sigma x t, normal sigma -> normal x -> normal t -> normal (abs sigma x t).  
Proof. 
intros. unfold abs, star_opt_app_comb, app_comb. unfold_op. 
apply nf_compound. 2: nf_out; auto. 2: auto. 
apply nf_compound. auto. 2: auto. 
apply nf_compound. 2: nf_out; auto. 2: auto. 
apply nf_compound. auto. 2: auto. 
apply nf_compound. auto. 2: auto. 
apply nf_compound. auto. 2: auto. 
apply nf_compound. 2: eapply2 add_fn_normal. 2: auto. 
apply nf_compound. auto. 2: auto. 
apply nf_compound. 
apply nf_compound. auto. 2: auto. 
eapply2 omega3_program. eapply2 omega3_program. auto. 
Qed. 



Lemma add_red_add: 
forall sigma sigma2 y v, 
sf_red (App (add sigma) (add (pair (pair sigma2 y) v)))  
        (add (pair (pair (App (add sigma) sigma2) y) 
                   (App (add sigma) v))). 
Proof.
intros. unfold add at 1, app_comb. eval_tac. eval_tac. eval_tac. 
eapply transitive_red. eapply preserves_app_sf_red.  eapply2 omega3_omega3. auto. 
(* 1 *) 
unfold add_fn, app_comb. 
eapply transitive_red. eapply  preserves_app_sf_red.
eapply2 star_opt_beta2. auto.  
unfold subst; rewrite ! subst_rec_preserves_extension. 
(* an app_comb *) 
eapply transitive_red. 
 eapply2 extensions_by_matching.
unfold add.  
unfold app_comb; unfold_op. eapply2 match_app.  
(* 1 *)  
unfold map, app, length, fold_left, subst.
unfold subst_rec; fold subst_rec. 
rewrite ! subst_rec_preserves_extension.
rewrite ! subst_rec_app. 
insert_Ref_out. 
(* not a tag *) 
eapply transitive_red. apply extensions_by_matchfail.
repeat (rewrite subst_rec_ref; insert_Ref_out).  
unfold lift; rewrite ! lift_rec_null.
rewrite subst_rec_lift_rec; try omega. 
rewrite lift_rec_null. 
unfold app_comb. unfold_op.  
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_op. left; eauto. discriminate. 
(* 1  not a var *) 
unfold pattern_size; fold pattern_size. unfold plus; fold plus. 
do 12 (rewrite subst_rec_ref at 1; insert_Ref_out). 
unfold lift; rewrite ! lift_rec_null. 
eapply transitive_red. eapply extensions_by_matching.
repeat (rewrite subst_rec_ref at 1; insert_Ref_out). 
unfold lift; rewrite lift_rec_null. rewrite subst_rec_lift_rec; try omega. 
rewrite lift_rec_null. 
repeat eapply2 match_app. 
unfold map, app, length, fold_left, subst.
(* 1 *)  
unfold subst_rec; fold subst_rec. 
rewrite ! lift_rec_lift_rec; try omega.  unfold plus. 
rewrite ! subst_rec_lift_rec; try omega. 
rewrite ! lift_rec_null. 
unfold add. apply preserves_app_sf_red. 
eapply2 zero_red. 
unfold lift; rewrite ! lift_rec_lift_rec; try omega. unfold plus. 
 apply preserves_app_sf_red.  apply preserves_app_sf_red.  auto. 
(* 2 *) 
 apply preserves_app_sf_red.  apply preserves_app_sf_red.  auto. 
repeat (rewrite subst_rec_ref at 1; insert_Ref_out). 
rewrite ! lift_rec_null.  insert_Ref_out. 
repeat (rewrite subst_rec_ref at 1; insert_Ref_out). 
unfold lift; rewrite lift_rec_null. 
eapply2 zero_red. 
 insert_Ref_out. 
repeat (rewrite subst_rec_ref at 1; insert_Ref_out). 
unfold lift; rewrite lift_rec_null. 
rewrite subst_rec_lift_rec; try omega. rewrite lift_rec_null; auto. 
(* 1 *)
 insert_Ref_out. 
 apply preserves_app_sf_red.  apply preserves_app_sf_red.  
unfold lift; rewrite lift_rec_null. 
(rewrite subst_rec_ref at 1; insert_Ref_out). 
unfold lift; rewrite ! subst_rec_lift_rec; try omega. 
rewrite lift_rec_null. 
eapply2 zero_red. 
unfold lift; rewrite ! lift_rec_lift_rec; try omega. unfold plus. 
rewrite ! subst_rec_lift_rec; try omega. 
rewrite ! lift_rec_null.  auto. 
repeat (rewrite subst_rec_ref at 1; insert_Ref_out). 
unfold lift; rewrite ! lift_rec_lift_rec; try omega.  unfold plus. 
rewrite ! subst_rec_lift_rec; try omega. 
rewrite lift_rec_null. auto.  
Qed. 




Lemma add_red_empty: 
forall sigma, 
sf_red (App (add sigma) i_op) (App (fst_projection (fst_projection sigma)) i_op) .
Proof.
intros. unfold add at 1, app_comb. eval_tac. eval_tac. eval_tac. 
eapply transitive_red. eapply preserves_app_sf_red. eapply2 omega3_omega3. auto. 
(* 1 *)
unfold add_fn, app_comb.
eapply transitive_red. 
eapply preserves_app_sf_red.  eapply2 star_opt_beta2. auto. 
unfold subst; rewrite ! subst_rec_preserves_extension. 
eapply transitive_red. eapply2 extensions_by_matchfail.
eapply transitive_red. eapply2 extensions_by_matchfail. 
(* 1 *) 
rewrite ! subst_rec_preserves_fst_projection. 
 repeat (unfold subst_rec; fold subst_rec; insert_Ref_out).  
unfold lift; rewrite ! lift_rec_lift_rec; try omega. unfold plus. 
rewrite ! subst_rec_lift_rec; try omega. rewrite ! lift_rec_null.  auto. 
Qed. 




