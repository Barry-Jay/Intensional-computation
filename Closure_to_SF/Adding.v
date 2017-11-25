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

(*  install Bignums !!!
From Bignums Require Import BigN. 
*) 

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
eapply2 f_compound_red. eval_tac. eval_tac.  
Qed. 

Lemma snd_red : forall M N, sf_red (snd_projection (pair M N)) N. 
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

Definition star_opt_app_comb M N := 
App
  (App (Op Sop)
     (App (App (Op Sop) (App (App (Op Fop) (Op Fop)) (Op Sop)))
        (App (App (Op Sop) (App (App (Op Fop) (Op Fop)) (App (Op Sop) (App (App (Op Fop) (Op Fop)) M))))
           (App (App (Op Sop) (App (App (Op Fop) (Op Fop)) (App (Op Fop) (Op Fop)))) N))))
  (App (App (Op Fop) (Op Fop)) (App (App (Op Sop) (App (Op Fop) (Op Fop))) (App (Op Fop) (Op Fop)))) .

Lemma star_opt_app_comb_val: 
forall M N, occurs0 N = true -> N <> Ref 0 -> star_opt (app_comb (lift 1 M) N) = star_opt_app_comb M (star_opt N). 
Proof.
intros; unfold app_comb, lift; unfold_op. 
rewrite star_opt_occurs_true. 2 : simpl; rewrite H; rewrite orb_true_r at 1; cbv; auto. 2: discriminate. 
rewrite star_opt_occurs_true. 2 : simpl; rewrite H; rewrite orb_true_r at 1; cbv; auto. 2: discriminate. 
unfold star_opt at 1.
rewrite star_opt_occurs_true. 2 : simpl; rewrite H; rewrite orb_true_r at 1; cbv; auto. 2: discriminate. 
 rewrite star_opt_occurs_false. 2: unfold occurs0; fold occurs0; simpl.  
2: rewrite occurs_lift_rec_zero; auto. 
rewrite star_opt_occurs_true. 2 : simpl; rewrite H; auto. 2: auto.  
rewrite star_opt_closed; auto.  
rewrite (star_opt_closed (App (App (Op Sop) (App (Op Fop) (Op Fop))) (App (Op Fop) (Op Fop)))); auto.  
unfold_op; unfold subst, subst_rec; fold subst_rec. 
rewrite subst_rec_lift_rec; try omega. 
rewrite lift_rec_null. auto. 
Qed. 


Lemma star_opt_app_comb_red: 
forall M N P, sf_red (App (star_opt_app_comb M N) P) (app_comb M (App N P)).
Proof.
intros; unfold star_opt_app_comb, app_comb. eval_tac.  eval_tac.  eval_tac.  
 eapply2 preserves_app_sf_red.  eapply2 preserves_app_sf_red. eval_tac.  eval_tac. 
 eapply2 preserves_app_sf_red. eval_tac. eval_tac. eval_tac. 
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
             (App k_op (App (App (App (App equal_comb (Ref 0)) 
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
intros. unfold Y3. 
eapply transitive_red.  eapply2 star_opt_beta. 
unfold subst; rewrite ! subst_rec_preserves_app_comb. 
unfold lift; rewrite ! subst_rec_lift_rec; try omega.
rewrite ! lift_rec_null. 
rewrite ! (subst_rec_closed omega3). 2: unfold omega3; cbv; auto. 
unfold subst_rec; fold subst_rec. insert_Ref_out. 
unfold lift; rewrite lift_rec_null.
unfold add, add_fn; eapply2 zero_red. 
Qed.


Lemma maxvar_add: forall M, maxvar (add M) = maxvar M.
Proof.
unfold add. intros. rewrite ! maxvar_app_comb. 
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
intros; unfold abs. eval_tac.  
eapply transitive_red. eapply preserves_app_sf_red. eapply2 star_opt_app_comb_red. eval_tac.  
eapply2 preserves_app_sf_red. 
Qed. 

Lemma lift_rec_preserves_Y3: forall M n k, lift_rec (Y3 M) n k = Y3 (lift_rec M n k).
Proof. 
intros. unfold Y3.  rewrite lift_rec_preserves_star_opt. 
rewrite ! lift_rec_preserves_app_comb.
unfold lift; rewrite lift_lift_rec; try omega.
rewrite ! (lift_rec_closed omega3).  unfold  lift_rec; fold lift_rec. relocate_lt.  auto. 
unfold omega3; cbv; auto.
Qed.   


Lemma add_red_tag: 
forall sigma M N, sf_red (App (add sigma) (tag M N)) 
                         (App (App (add sigma) M)
                              (App (add sigma) N)).
Proof.
intros. unfold add at 1. 
eapply transitive_red. eapply2 app_comb_red.
eapply transitive_red. eapply preserves_app_sf_red. eapply2 app_comb_red. auto. 
eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red. 
eapply2 app_comb_red. auto. auto. 
eapply transitive_red. eapply preserves_app_sf_red.  eapply2 omega3_omega3. auto. 
(* 1 *) 
unfold add_fn. 
eapply transitive_red. eapply  preserves_app_sf_red.
eapply2 star_opt_beta2. auto.  
unfold subst; rewrite ! subst_rec_preserves_extension. 
(* an app_comb *) 
eapply transitive_red. 
 eapply2 extensions_by_matching.
unfold tag, var.  
unfold app_comb; unfold_op. eapply2 match_app.  
eapply2 match_app. eapply2 match_app. 
eapply2 match_app. eapply2 match_app. 
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
unfold app_comb; unfold_op. eapply2 match_app.  
eapply2 match_app. eapply2 match_app. 
eapply2 match_app. eapply2 match_app. 
(* 1 *)  
unfold map, app, length, fold_left, subst.
rewrite ! subst_rec_app. 
rewrite ! pattern_size_app_comb.   
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
             (App k_op (App (App (App (App equal_comb (Ref 0)) 
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
))
)
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
intros. unfold_op;  unfold add at 1. 
eapply transitive_red. eapply2 app_comb_red. 
eapply transitive_red. eapply preserves_app_sf_red. 
eapply2 app_comb_red. auto.   
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply2 app_comb_red. auto. auto.
eapply transitive_red. eapply preserves_app_sf_red. eapply2 omega3_omega3. auto. 
(* 1 *)
unfold add_fn.
eapply transitive_red. 
eapply preserves_app_sf_red.  eapply2 star_opt_beta2. auto. 
unfold subst; rewrite ! subst_rec_preserves_extension. 
eapply transitive_red. eapply2 extensions_by_matching.
unfold var, var_fn, app_comb; unfold_op. 
 eapply2 match_app.  
eapply2 match_app. eapply2 match_app. 
eapply2 match_app. eapply2 match_app. 
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
eapply succ_red. eapply2 f_op_red. 
rewrite ! (subst_rec_closed equal_comb); auto.
rewrite ! pattern_size_app_comb.   
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
eapply2 unequal_programs. auto. eapply2 zero_red.  eval_tac. eval_tac. 
eapply preserves_app_sf_red. auto.  
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
intros. unfold_op;  unfold add at 1. 
eapply transitive_red. eapply2 app_comb_red. 
eapply transitive_red. eapply preserves_app_sf_red. 
eapply2 app_comb_red. auto.   
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply2 app_comb_red. auto. auto.
eapply transitive_red. eapply preserves_app_sf_red. eapply2 omega3_omega3. auto. 
(* 1 *)
unfold add_fn.
eapply transitive_red. 
eapply preserves_app_sf_red.  eapply2 star_opt_beta2. auto. 
unfold subst; rewrite ! subst_rec_preserves_extension. 
eapply transitive_red. eapply2 extensions_by_matching.
unfold var, var_fn, app_comb; unfold_op. 
 eapply2 match_app.  
eapply2 match_app. eapply2 match_app. 
eapply2 match_app. eapply2 match_app. 
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
eapply succ_red. eapply2 f_op_red. 
rewrite ! (subst_rec_closed equal_comb); auto.
rewrite ! pattern_size_app_comb.   
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
intros. unfold add at 1. 
eapply transitive_red. eapply2 app_comb_red. 
eapply transitive_red. eapply preserves_app_sf_red. 
eapply2 app_comb_red. auto.   
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply2 app_comb_red. auto. auto.
eapply transitive_red. eapply preserves_app_sf_red. eapply2 omega3_omega3. auto. 
(* 1 *)
unfold add_fn.
eapply transitive_red. 
eapply preserves_app_sf_red.  eapply2 star_opt_beta2. auto. 
unfold subst; rewrite ! subst_rec_preserves_extension. 
eapply transitive_red. eapply2 extensions_by_matchfail.
(* abs not an app_comb *) 
unfold abs, star_opt_app_comb, app_comb; unfold_op. 
eapply2 matchfail_compound_l.   
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_l.   
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_l.   
eapply2 matchfail_compound_l.
eapply2 matchfail_op. unfold factorable; eauto. discriminate. 
(* an abs *) 
eapply transitive_red. eapply2 extensions_by_matching. 
unfold abs, star_opt_app_comb, pair. 
eapply2 match_app.  eapply2 match_app.  
eapply2 match_app. eapply2 match_app. 
eapply2 match_app. eapply2 match_app.
eapply2 match_app.  eapply2 match_app.  
eapply2 match_app. eapply2 match_app. 
eapply2 match_app. eapply2 match_app.
eapply2 program_matching. split; auto. 
repeat eapply2 match_app.  
eapply2 program_matching. split; auto. 
unfold_op. repeat eapply2 match_app.  
unfold map, app, length, fold_left, subst.  
(* 1 *) 
unfold star_opt_app_comb; unfold_op; unfold pattern_size; fold pattern_size.
unfold plus. 
rewrite 12?  subst_rec_app.
rewrite 12?  subst_rec_op.
rewrite 12?  subst_rec_app.
rewrite 12?  subst_rec_op.
rewrite 12?  subst_rec_app.
rewrite 12?  subst_rec_op.
rewrite 12?  subst_rec_app.
rewrite 12?  subst_rec_op.
rewrite 12?  subst_rec_app.
rewrite 12?  subst_rec_op.
rewrite 12?  subst_rec_app.
rewrite 12?  subst_rec_op.
rewrite 12?  subst_rec_app.
rewrite 12?  subst_rec_op.
rewrite 12?  subst_rec_app.
rewrite 12?  subst_rec_op.
unfold lift; rewrite ! lift_rec_null. 
repeat (rewrite subst_rec_ref; insert_Ref_out). 
rewrite 12?  subst_rec_app.
rewrite 12?  subst_rec_op.
rewrite 12?  subst_rec_app.
rewrite 12?  subst_rec_op.
rewrite 12?  subst_rec_app.
rewrite 12?  subst_rec_op.
rewrite 12?  subst_rec_app.
do 12 (rewrite subst_rec_ref at 1; insert_Ref_out). 
unfold lift; rewrite ! lift_rec_lift_rec; try omega. 
unfold plus. 
rewrite ! subst_rec_lift_rec; try omega. 
rewrite ! lift_rec_null. 
rewrite 12?  subst_rec_app.
rewrite 12?  subst_rec_op.
rewrite 12?  subst_rec_app.
rewrite 12?  subst_rec_op.
rewrite 12?  subst_rec_app.
rewrite 12?  subst_rec_op.
rewrite 12?  subst_rec_app.
rewrite 12?  subst_rec_op.
repeat (rewrite subst_rec_ref; insert_Ref_out). 
unfold lift; rewrite ! lift_rec_lift_rec; try omega. 
unfold plus. 
rewrite ! subst_rec_lift_rec; try omega. 
rewrite ! lift_rec_null. 
unfold abs. 
apply preserves_app_sf_red. apply preserves_app_sf_red. auto. 2: eapply2 zero_red. 
apply preserves_app_sf_red. apply preserves_app_sf_red. auto. 2: eapply2 zero_red.
apply preserves_app_sf_red. eapply2 zero_red. 
apply preserves_app_sf_red. eapply2 zero_red. 
apply preserves_app_sf_red. eapply2 zero_red. 
apply preserves_app_sf_red. auto.
apply preserves_app_sf_red. 2: auto.
apply preserves_app_sf_red. auto. 
apply preserves_app_sf_red. 2: auto. 
(* 1 *) 
replace ((star_opt
           (star_opt
              (extension (app_comb (Ref 1) (Ref 0))
                 (App
                    (extension (app_comb (Ref 1) (Ref 0))
                       (App (App (App (Ref 5) (Ref 4)) (Ref 1)) (App (App (Ref 5) (Ref 4)) (Ref 0)))
                       (extension (App (App (Op Fop) (App (App (Op Fop) (Ref 2)) (Ref 1))) (Ref 0))
                          (app_comb (Ref 4)
                             (App
                                (App (Op Fop)
                                   (App (App (Op Fop) (App (App (Ref 6) (Ref 5)) (Ref 2))) (Ref 1)))
                                (App (App (Ref 6) (Ref 5)) (Ref 0))))
                          (App (App (Op Fop) (Op Fop))
                             (App
                                (App
                                   (App (App equal_comb (Ref 0))
                                      (snd_projection (fst_projection (Ref 2))))
                                   (snd_projection (Ref 2)))
                                (App (fst_projection (fst_projection (Ref 2)))
                                   (app_comb (Ref 1) (Ref 0))))))) (Ref 0))
                 (extension
                    (App
                       (App (Op Sop)
                          (App
                             (App (Op Sop)
                                (App (App (Op Sop) (App (App (Op Fop) (Op Fop)) (Op Sop)))
                                   (App
                                      (App (Op Sop)
                                         (App (App (Op Fop) (Op Fop))
                                            (App (Op Sop) (App (App (Op Fop) (Op Fop)) (Ref 3)))))
                                      (App
                                         (App (Op Sop)
                                            (App (App (Op Fop) (Op Fop)) (App (Op Fop) (Op Fop))))
                                         (App (Op Fop) (App (App (Op Fop) (Ref 2)) (Ref 1)))))))
                             (App (App (Op Fop) (Op Fop))
                                (App (App (Op Sop) (App (Op Fop) (Op Fop))) (App (Op Fop) (Op Fop))))))
                       (App (App (Op Fop) (Op Fop)) (Ref 0)))
                    (App
                       (App (Op Sop)
                          (App
                             (App (Op Sop)
                                (App (App (Op Sop) (App (App (Op Fop) (Op Fop)) (Op Sop)))
                                   (App
                                      (App (Op Sop)
                                         (App (App (Op Fop) (Op Fop))
                                            (App (Op Sop) (App (App (Op Fop) (Op Fop)) (Ref 3)))))
                                      (App
                                         (App (Op Sop)
                                            (App (App (Op Fop) (Op Fop)) (App (Op Fop) (Op Fop))))
                                         (App (Op Fop)
                                            (App (App (Op Fop) (App (App (Ref 5) (Ref 4)) (Ref 2)))
                                               (Ref 1)))))))
                             (App (App (Op Fop) (Op Fop))
                                (App (App (Op Sop) (App (Op Fop) (Op Fop))) (App (Op Fop) (Op Fop))))))
                       (App (App (Op Fop) (Op Fop)) (Ref 0)))
                    (fst_projection (fst_projection (Ref 0))))))))

with add_fn by auto. 
eapply2 Y3_to_add. 
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
eapply2 pnf_break. 3: cbv; omega. 
eapply2 pnf_break. 3: cbv; omega.  3: cbv; eapply2 pnf_normal.
eapply2 pnf_normal. cbv.  nf_out; eapply2 nf_active.  
replace (pattern_size (app_comb (Ref 1) (Ref 0)) + 2) with 4 by (cbv; auto). 
eapply2 pnf_break.
eapply2 pnf_normal. unfold_op; auto. 
2: cbv; auto. 
(* 2 *) 
apply extension_pattern_normal. 
eapply2 pattern_normal_app_comb. 
eapply2 pnf_normal.
eapply2 pnf_normal. nf_out. eapply2 nf_active. auto. eapply2 nf_active. 
eapply2 pnf_break. 3: cbv; auto. 
unfold_op; eapply2 pnf_normal. 
eapply2 pnf_break. 3: cbv; auto. 
eapply2 pnf_break. 3: cbv; auto.
eapply2 pnf_break. 3: cbv; auto.
eapply2 pnf_break.  
eapply2 pnf_normal. 
eapply2 equal_comb_normal. 
eapply2 pnf_normal. 
unfold snd_projection, fst_projection, left_projection, right_projection.
eapply2 pnf_normal. repeat (nf_out; eapply2 nf_active).
eapply2 pnf_normal. 
unfold snd_projection, fst_projection, left_projection, right_projection.
repeat (nf_out; eapply2 nf_active).
eapply2 pnf_normal. 
unfold app_comb, snd_projection, fst_projection, left_projection, right_projection.
repeat (nf_out; eapply2 nf_active). nf_out. auto. auto. 
(* 1 *) 
eapply2 pnf_normal. eapply2 extension_normal. unfold star_opt_app_comb; nf_out. 
auto. eapply2 nf_active. auto. auto; nf_out. nf_out. 
unfold fst_projection, left_projection, right_projection; nf_out. 
eapply2 nf_active. repeat (nf_out; eapply2 nf_active). 
nf_out. 
Qed. 
 


  
Lemma add_normal: forall f, normal f -> normal (add f). 
Proof. 
unfold add. intros.  apply app_comb_normal. 2: auto. 
apply app_comb_normal. 2: apply add_fn_normal. 
apply app_comb_normal; eapply2 omega3_program. 
Qed. 

Lemma abs_normal: 
forall sigma x t, normal sigma -> normal x -> normal t -> normal (abs sigma x t).  
Proof. 
intros. unfold abs, star_opt_app_comb. unfold_op. 
apply nf_compound. 2: nf_out; auto. 2: auto. 
apply nf_compound. auto. 2: auto. 
apply nf_compound. 2: nf_out; auto. 2: auto. 
apply nf_compound. auto. 2: auto. 
apply nf_compound. auto. 2: auto. 
apply nf_compound. 2: nf_out; auto. 2: auto. 
apply nf_compound. auto. 2: auto. 
apply nf_compound. auto. 2: auto. 
apply nf_compound. auto. 2: auto. 
apply nf_compound. auto. 2: auto.
apply app_comb_normal. 2: apply add_fn_normal. 
apply app_comb_normal; eapply2 omega3_program. 
Qed. 



Lemma add_red_add: 
forall sigma sigma2 y v, 
sf_red (App (add sigma) (add (pair (pair sigma2 y) v)))  
        (add (pair (pair (App (add sigma) sigma2) y) 
                   (App (add sigma) v))). 
Proof.
intros. unfold add at 1. 
eapply transitive_red. eapply2 app_comb_red.
eapply transitive_red. eapply preserves_app_sf_red. eapply2 app_comb_red. auto. 
eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red. 
eapply2 app_comb_red. auto. auto. 
eapply transitive_red. eapply preserves_app_sf_red.  eapply2 omega3_omega3. auto. 
(* 1 *) 
unfold add_fn. 
eapply transitive_red. eapply  preserves_app_sf_red.
eapply2 star_opt_beta2. auto.  
unfold subst; rewrite ! subst_rec_preserves_extension. 
(* an app_comb *) 
eapply transitive_red. 
 eapply2 extensions_by_matching.
unfold add.  
unfold app_comb; unfold_op. eapply2 match_app.  
eapply2 match_app. eapply2 match_app. 
eapply2 match_app. eapply2 match_app. 
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
rewrite ! subst_rec_preserves_app_comb.
rewrite ! pattern_size_app_comb. 
unfold pattern_size; fold pattern_size. unfold plus; fold plus. 
repeat (rewrite subst_rec_ref; insert_Ref_out). 
unfold lift; rewrite ! lift_rec_null. 
eapply transitive_red. eapply extensions_by_matching.
rewrite subst_rec_lift_rec; try omega. 
rewrite lift_rec_null. 
repeat eapply2 match_app. 
unfold map, app, length, fold_left, subst.  
rewrite ! subst_rec_preserves_app_comb. 
rewrite ! subst_rec_lift_rec; try omega. 
rewrite ! lift_rec_null. 
rewrite ! subst_rec_app. rewrite ! subst_rec_op.
do 12 (rewrite subst_rec_ref at 1; insert_Ref_out). 
do 12 (rewrite subst_rec_ref at 1; insert_Ref_out). 
unfold lift; rewrite ! lift_rec_lift_rec; try omega. unfold plus. 
rewrite ! subst_rec_lift_rec; try omega. 
rewrite ! lift_rec_null. 
unfold add. apply preserves_app_sf_red. 
apply preserves_app_sf_red. auto. 2: auto. 
apply preserves_app_sf_red. auto. 
unfold pair; apply preserves_app_sf_red. auto. 
  apply preserves_app_sf_red. 
 apply preserves_app_sf_red. auto. 
 apply preserves_app_sf_red. 2: auto. 
 apply preserves_app_sf_red. auto. 
 apply preserves_app_sf_red. 2: auto. 
(* 2 *) 
unfold Y3. eapply transitive_red. eapply2 star_opt_beta. 
unfold subst. rewrite ! subst_rec_preserves_app_comb. 
rewrite ! (subst_rec_closed omega3). 2: cbv; auto. 
unfold lift; rewrite subst_rec_lift_rec; try omega.
unfold subst_rec. insert_Ref_out. 
unfold lift; rewrite ! lift_rec_null. 
unfold add_fn; auto.
(* 1 *) 
 apply preserves_app_sf_red. 2: auto. 
unfold Y3. eapply transitive_red. eapply2 star_opt_beta. 
unfold subst. rewrite ! subst_rec_preserves_app_comb. 
rewrite ! (subst_rec_closed omega3). 2: cbv; auto. 
unfold lift; rewrite subst_rec_lift_rec; try omega.
unfold subst_rec. insert_Ref_out. 
unfold lift; rewrite ! lift_rec_null. 
unfold add_fn; auto.
Qed. 




Lemma add_red_empty: 
forall sigma, 
sf_red (App (add sigma) i_op) (App (fst_projection (fst_projection sigma)) i_op) .
Proof.
intros. unfold add at 1. 
eapply transitive_red. eapply2 app_comb_red. 
eapply transitive_red. eapply preserves_app_sf_red. 
eapply2 app_comb_red. auto.   
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply2 app_comb_red. auto. auto.
eapply transitive_red. eapply preserves_app_sf_red. eapply2 omega3_omega3. auto. 
(* 1 *)
unfold add_fn.
eapply transitive_red. 
eapply preserves_app_sf_red.  eapply2 star_opt_beta2. auto. 
unfold subst; rewrite ! subst_rec_preserves_extension. 
eapply transitive_red. eapply2 extensions_by_matchfail.
(* Iop not an app_comb *) 
unfold app_comb; unfold_op.
eapply2 matchfail_compound_l.   
(* Iop not an abs *) 
eapply transitive_red. eapply2 extensions_by_matchfail. 
eapply2 matchfail_compound_l.   
eapply2 matchfail_compound_r.    unfold_op; auto. 
unfold star_opt_app_comb. 
eapply2 matchfail_compound_l.   
eapply2 matchfail_compound_op.
(* 1 *) 
rewrite ! subst_rec_preserves_fst_projection. 
 repeat (unfold subst_rec; fold subst_rec; insert_Ref_out).  
unfold lift; rewrite ! lift_rec_lift_rec; try omega. unfold plus. 
rewrite ! subst_rec_lift_rec; try omega. rewrite ! lift_rec_null.  auto. 
Qed. 

