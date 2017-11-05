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
(*                        Optimization                                *)
(*                                                                    *)
(*                          Barry Jay                                 *)
(*                                                                    *)
(**********************************************************************)


Require Import Arith Omega Max Bool List.

Require Import IntensionalLib.Closure_calculus.Closure_calculus.

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
Require Import IntensionalLib.Fieska_calculus.Adding.

Require Import IntensionalLib.Closure_to_Fieska.Abstraction_to_Combination.



Definition update p s := 
App (Y_k 2) (star_opt (
extension p s (star_opt (App (App (App (Op Fop) (Ref 0)) (Ref 0))
               (star_opt (star_opt (App (App (Ref 3) (Ref 1)) (App (Ref 3) (Ref 0))))))))). 

Lemma update_op: forall p s o, matchfail p (Op o) -> sf_red (App (update p s) (Op o)) (Op o). 
Proof. 
split_all. unfold update. 
eapply transitive_red. eapply2 Y2_fix. 
eapply transitive_red. eapply preserves_app_sf_red. eapply2 star_opt_beta. auto. 
unfold subst; rewrite subst_rec_preserves_extension. 
eapply transitive_red. eapply2 extensions_by_matchfail. 
rewrite subst_rec_preserves_star_opt. 
eapply transitive_red. eapply2 star_opt_beta. 
unfold subst, subst_rec; fold subst_rec.  insert_Ref_out. 
rewrite ! subst_rec_preserves_star_opt. 
unfold subst, subst_rec; fold subst_rec.  insert_Ref_out. 
unfold subst, subst_rec; fold subst_rec.  insert_Ref_out. unfold lift. 
rewrite subst_rec_lift_rec; try omega. rewrite ! lift_rec_null. 
eval_tac. 
Qed.

Lemma update_compound: 
forall p s M N, matchfail p (App M N) -> compound (App M N) -> 
sf_red (App (update p s) (App M N)) (App (App (update p s) M) (App (update p s) N)).
Proof. 
split_all. unfold update at 1. 
eapply transitive_red. eapply2 Y2_fix. 
eapply transitive_red. eapply preserves_app_sf_red. eapply2 star_opt_beta. auto. 
unfold subst; rewrite subst_rec_preserves_extension. 
eapply transitive_red. eapply2 extensions_by_matchfail. 
rewrite subst_rec_preserves_star_opt. 
eapply transitive_red. eapply2 star_opt_beta. 
unfold subst, subst_rec; fold subst_rec.  insert_Ref_out. 
rewrite ! subst_rec_preserves_star_opt. 
unfold subst, subst_rec; fold subst_rec.  insert_Ref_out. unfold lift. 
rewrite subst_rec_lift_rec; try omega. rewrite ! lift_rec_null. 
eapply succ_red. eapply2 f_compound_red. unfold left_component, right_component. 
eapply transitive_red. eapply preserves_app_sf_red. eapply2 star_opt_beta. auto. 
unfold subst. rewrite ! subst_rec_preserves_star_opt. 
eapply transitive_red. eapply2 star_opt_beta. 
unfold subst, subst_rec; fold subst_rec.  insert_Ref_out. 
rewrite !  subst_rec_lift_rec; try omega. rewrite ! lift_rec_null. 
unfold a_op. 
eapply transitive_red. eapply preserves_app_sf_red. eapply succ_red. eapply2 a_red. 
unfold subst, subst_rec; fold subst_rec. insert_Ref_out. unfold lift. 
rewrite subst_rec_lift_rec; try omega. rewrite ! lift_rec_null. 
auto. 
eapply transitive_red. eapply succ_red. eapply2 a_red. 
unfold subst, subst_rec; fold subst_rec. insert_Ref_out. 
unfold subst, subst_rec; fold subst_rec. insert_Ref_out. unfold lift. 
rewrite ! lift_rec_null. 
auto.  auto. 
eapply2 preserves_app_sf_red. 
Qed.


Lemma tag_preserves_sf_red: 
forall x x' t t', sf_red x x' -> sf_red t t' -> sf_red (tag x t) (tag x' t'). 
Proof. intros. unfold tag; repeat eapply2 preserves_app_sf_red. Qed. 

(* restore the optimizations 

(* x + 0 --> x 

To perform this update, it is necessary to ensure that the pattern for x+0 is in nomal form. 
*) 




Definition  my_plus_zero_r := 
update (lambda_to_fieska (my_plus_0_nf (Closure_calculus.Ref 0))) (Ref 0).


Lemma my_plus_zero_r_basic0 : 
forall M, 
sf_red (App my_plus_zero_r (lambda_to_fieska (Closure_calculus.App 
  (Closure_calculus.App my_plus M) zero))) 
                           (lambda_to_fieska M). 
Proof. 
intros.
eapply transitive_red.  eapply preserves_app_sf_red. auto. 
eapply lambda_to_fieska_preserves_seq_red. eapply2 my_plus_0_val. 
unfold my_plus_0_nf, my_plus_zero_r, lambda_to_fieska; fold lambda_to_fieska. 
unfold update. 
eapply transitive_red. eapply2 Y2_fix. 
eapply transitive_red. eapply preserves_app_sf_red. eapply2 star_opt_beta. auto. 
unfold subst; rewrite subst_rec_preserves_extension.

 
eapply transitive_red. eapply2 extensions_by_matching.
unfold my_plus_0_nf, my_plus_zero_r, lambda_to_fieska; fold lambda_to_fieska. 
unfold my_plus_0_nf.  
eapply2 match_app. 
unfold var. 
2: eapply2 program_matching.  
2: unfold scott, tt, Closure_calculus.abs, a_op, lambda_to_fieska; fold lambda_to_fieska; unfold program; split. 
3: cbv; split_all. 
2:unfold_op;  eapply2 abs_normal; split_all; unfold a_op; unfold_op.  
2: eapply2 nf_compound. 2: eapply2 nf_compound. 2: eapply2 var_normal; auto. 
2: eapply2 var_normal; auto.  2: eapply2 var_normal; auto. 
(* 2 *) 
eapply2 match_app. 
eapply2 match_app. 
eapply2 program_matching. 
unfold program; split. nf_out. cbv; auto. 
eapply2 match_app. 
eapply2 match_app.
eapply2 match_app. 
eapply2 program_matching; split_all. 
eapply2 match_app. 
eapply2 match_app. 
eapply2 match_app. 
eapply2 program_matching; split_all. 
(* 2 *) 
apply program_matching.
unfold abs, program; split. nf_out.
eapply2 abs_fn_normal. unfold_op; nf_out.
unfold_op; nf_out.
eapply2 var_normal. 
eapply2 var_normal. unfold_op; auto. 
cbv; auto. 
(* 2 *) 
apply program_matching.
unfold abs, program; split. nf_out.
eapply2 abs_fn_normal. unfold_op; nf_out.
eapply2 var_normal. 
unfold_op; nf_out.
unfold add; nf_out. 
unfold_op; nf_out. 
eapply2 var_normal.
eapply2 abs_normal. 
eapply2 var_normal.
repeat eapply2 tag_normal. 
eapply2 var_normal.
eapply2 var_normal.
eapply2 var_normal.
eapply2 var_normal.
eapply2 var_normal.
nf_out. 
eapply2 var_normal. 
eapply2 abs_normal. 
nf_out. 
eapply2 var_normal. 
eapply2 var_normal.
eapply2 var_normal. 
repeat eapply2 tag_normal; try (eapply2 var_normal). 
eapply2 var_normal. 
eapply2 abs_normal.  nf_out. 
eapply2 var_normal. 
eapply2 var_normal.
repeat eapply2 tag_normal; try (eapply2 var_normal).
eapply2 abs_normal. 
eapply2 var_normal. 
eapply2 var_normal.
eapply2 abs_normal. nf_out. 
eapply2 var_normal. 
eapply2 var_normal.
eapply2 abs_normal. nf_out. 
eapply2 var_normal. 
eapply2 var_normal.
eapply2 tag_normal. 
eapply2 var_normal. 
eapply2 var_normal. nf_out. 
eapply2 var_normal.
repeat eapply2 tag_normal; try (eapply2 var_normal).
nf_out. 
eapply2 var_normal. 
eapply2 var_normal.
eapply2 var_normal.
eapply2 abs_fn_normal. nf_out.  
eapply2 var_normal. unfold_op; nf_out. 
unfold add; nf_out. 
unfold_op; nf_out. 
eapply2 var_normal.
repeat eapply2 tag_normal. 
eapply2 var_normal.
eapply2 var_normal.
eapply2 var_normal.
eapply2 var_normal.
eapply2 tag_normal.
eapply2 var_normal. 
unfold_op; nf_out. 
eapply2 var_normal.
unfold_op; nf_out. 
cbv.  auto. 
(* 1 *)
replace (length nil) with 0 by auto.  
rewrite ! map_lift0. rewrite ! app_nil_r.  rewrite ! app_nil_l.  
unfold fold_left, plus, subst, subst_rec; fold subst_rec. 
assert(pattern_size my_plus_zero_pattern = 1) by (cbv; auto). 
rewrite H. 
insert_Ref_out. 
unfold subst_rec; fold subst_rec.  insert_Ref_out. unfold lift; rewrite lift_rec_null. auto. 
Qed. 

Lemma my_plus_zero_r_basic : 
forall M, Closure_calculus.status M = Dynamic -> 
sf_red (App my_plus_zero_r (lambda_to_fieska (Closure_calculus.App (Closure_calculus.App my_plus M) (scott 0))) )
(lambda_to_fieska M). 
Proof. 
intros. eapply transitive_red. eapply preserves_app_sf_red. auto. 
eapply lambda_to_fieska_preserves_seq_red. eapply2 my_plus_dynamic_nf.
 eapply2 my_plus_zero_r_basic0.  
Qed. 

Lemma lambda_to_fieska_app: forall M N, lambda_to_fieska (Closure_calculus.App M N) = App (lambda_to_fieska M) (lambda_to_fieska N). 
Proof. split_all. Qed. 

 Lemma my_plus_zero_r_basic2 : 
forall M, Closure_calculus.status M = Dynamic -> 
sf_red (App my_plus_zero_r (App my_plus_zero_r 
            (lambda_to_fieska (Closure_calculus.App (Closure_calculus.App my_plus 
                                           (Closure_calculus.App (Closure_calculus.App my_plus M) (scott 0)))
                                (scott 0)))))
         (lambda_to_fieska M).
Proof. 
intros.
eapply transitive_red. eapply preserves_app_sf_red. auto.  eapply preserves_app_sf_red. auto. 
eapply lambda_to_fieska_preserves_seq_red. eapply preserves_app_seq_red. eapply preserves_app_seq_red. auto. 
eapply2 my_plus_dynamic_nf. auto. 
(* 1 *)
eapply transitive_red. eapply preserves_app_sf_red. auto. eapply2  my_plus_zero_r_basic. 
eapply2  my_plus_zero_r_basic0. 
Qed. 


Lemma matching_decidable: forall P M, normal P -> normal M -> maxvar M = 0 ->
matchfail P M \/ exists sigma, matching P M sigma. 
 Proof. 
induction P; split_all. 
(* 3 *) 
right; eauto. 
(* 2 *) 
assert (M = Op o \/ M<> Op o) by repeat (decide equality). 
inversion H2; subst; auto. right; eauto. 
left; eapply2 matchfail_op. unfold factorable; split_all. 
generalize H0 H1; case M; split_all. left; eauto. 
inversion H4; auto. assert(maxvar (App f f0) <>0) by eapply2 active_not_closed.  
simpl in *; noway. 
(* 1 *) 
inversion H; split_all; subst. 
generalize H0 H1 ; clear H0 H1; case M; split_all. 
assert(compound (App f f0)). inversion H0; subst; auto. 
assert(maxvar (App f f0) <>0) by eapply2 active_not_closed.  simpl in *; noway. 
assert(matchfail P1 f \/
         (exists sigma : list Fieska, matching P1 f sigma)).
eapply2 IHP1. inversion H0; auto. max_out. 
inversion H3; subst. left; eapply2 matchfail_active_l. 
split_all. 
assert(matchfail P2 f0 \/
         (exists sigma : list Fieska, matching P2 f0 sigma)).
eapply2 IHP2. inversion H0; auto. max_out. 
inversion H7; subst. left; eapply2 matchfail_active_r. 
split_all. right; eauto. 
(* 1 *) 
generalize H0 H1 ; clear H0 H1; case M; split_all. 
assert(compound (App f f0)). inversion H0; subst; auto. 
assert(maxvar (App f f0) <>0) by eapply2 active_not_closed.  simpl in *; noway. 
assert(matchfail P1 f \/
         (exists sigma : list Fieska, matching P1 f sigma)).
eapply2 IHP1. inversion H0; auto. max_out. 
inversion H3; subst. left; eapply2 matchfail_compound_l. 
split_all. 
assert(matchfail P2 f0 \/
         (exists sigma : list Fieska, matching P2 f0 sigma)).
eapply2 IHP2. inversion H0; auto. max_out. 
inversion H7; subst. left; eapply2 matchfail_compound_r. 
split_all. right; eauto. 
Qed. 


Lemma matchfail_small: forall P M, normal P -> normal M -> size M < size P -> maxvar M = 0 ->
matchfail P M. 
Proof. 
induction P; intros; assert(size M >0) by eapply2 size_positive; simpl in *; try noway. 
generalize H0 H1 H2 H3; clear H0 H1 H2 H3; case M; intros; simpl in *; split_all; try noway.
inversion H. eapply2 matchfail_active_op. eapply2 matchfail_compound_op. 
assert(size f < size P1 \/ size f0< size P2) by omega. 
assert(compound (App f f0)). inversion H0; auto. assert(maxvar (App f f0) <>0) by eapply2 active_not_closed.  simpl in *; noway. 
inversion H4; inversion H. 
eapply2 matchfail_active_l. eapply2 IHP1. inversion H0; auto.  max_out. 
eapply2 matchfail_compound_l. eapply2 IHP1. inversion H0; auto.  max_out. subst. 
assert(matchfail P1 f \/ exists sigma, matching P1 f sigma).  eapply2 matching_decidable. 
inversion H0; auto. max_out. 
inversion H7; split_all. eapply2 matchfail_active_r. 
eapply2 IHP2. inversion H0; auto.  max_out. 
assert(matchfail P1 f \/ exists sigma, matching P1 f sigma).  eapply2 matching_decidable. 
inversion H0; auto. max_out. 
inversion H12; split_all. eapply2 matchfail_compound_r. 
eapply2 IHP2. inversion H0; auto.  max_out. 
Qed. 


Lemma my_plus_zero_pattern_normal: normal my_plus_zero_pattern. 
Proof. 
unfold my_plus_zero_pattern.  repeat apply tag_normal. auto.  
eapply2 abs_normal. unfold refs; split_all. unfold_op; auto. 
eapply2 var_normal. unfold ref; auto.  unfold_op; auto. 
eapply2 var_normal. unfold ref; auto.  unfold_op; auto. 
 unfold_op; auto. 
eapply2 abs_normal. unfold refs; split_all. unfold_op; auto. repeat eapply2 nf_compound. 
unfold_op; auto. 
eapply2 var_normal. unfold ref; auto.  unfold_op; auto. 
eapply2 abs_normal. unfold refs; split_all. unfold_op; auto. repeat eapply2 nf_compound. 
unfold_op; auto. 
eapply2 var_normal. unfold ref; auto.  unfold_op; auto. 
repeat apply tag_normal. 
eapply2 var_normal. unfold ref; auto.  unfold_op; auto. 
eapply2 var_normal. unfold ref; auto.  unfold_op; auto. 
unfold add;  unfold_op; auto.  unfold_op; repeat (eapply2 nf_compound; unfold_op); auto.
unfold ref; auto.  unfold_op; auto. 
unfold add;  unfold_op; auto.  unfold_op; apply nf_compound. apply nf_compound. auto. 
apply nf_compound. apply nf_compound. auto. auto. auto. 
eapply2 var_normal. unfold ref; auto.  unfold_op; auto. auto. auto. 
eapply2 lambda_to_fieska_preserves_normal. eapply2 my_plus_nf_normal. auto. 
eapply2 abs_normal. unfold refs; split_all. unfold_op; auto. apply nf_compound.  apply nf_compound. 
auto. eapply2 var_normal. auto. auto. auto. 
eapply2 var_normal. unfold ref; auto.  unfold_op; auto. 
eapply2 var_normal. unfold ref; auto.  unfold_op; auto. 
unfold_op; auto. 
Qed. 


Hint Resolve my_plus_zero_pattern_normal. 

Lemma update_small: forall M P s, normal P -> normal M -> size M < size P -> maxvar M = 0 ->
sf_red (App (update P s) M) M. 
Proof. 
induction M; split_all.
(* 2 *) 
 eapply2 update_op. eapply2 matchfail_small. 
(* 1 *) 
eapply transitive_red. eapply2 update_compound. eapply2 matchfail_small. 
inversion H0; auto. assert(maxvar (App M1 M2) <> 0) by eapply2 active_not_closed. 
simpl in *; noway. 
eapply2 preserves_app_sf_red. eapply2 IHM1. inversion H0; auto. omega. max_out. 
eapply2 IHM2. inversion H0; auto. omega. max_out. 
Qed. 



 Lemma my_plus_zero_r_basic3 : 
forall M N, Closure_calculus.status M = Dynamic -> Closure_calculus.status N = Dynamic -> 
sf_red (App my_plus_zero_r 
            (s_op2 (lambda_to_fieska (Closure_calculus.App (Closure_calculus.App my_plus M) (scott 0)))
                   (lambda_to_fieska (Closure_calculus.App (Closure_calculus.App my_plus N) (scott 0)))))
         (s_op2 (lambda_to_fieska M) (lambda_to_fieska N)). 
Proof. 
intros.
eapply transitive_red. unfold my_plus_zero_r. 
eapply2 update_compound. 
eapply2 matchfail_compound_l.  eapply2 matchfail_compound_l. 
eapply2 matchfail_op.  unfold_op; unfold factorable; split_all. 
left; eauto. discriminate. 
eapply transitive_red. eapply preserves_app_sf_red. 
eapply2 update_compound. 
eapply2 matchfail_compound_l.  eapply2 matchfail_compound_op. 
eapply2 my_plus_zero_r_basic. 
eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red. 
eapply2 update_op.  eapply2 matchfail_compound_op. 
eapply2 my_plus_zero_r_basic. auto. auto. 
Qed.

Lemma size_my_plus_zero_pattern : 3252 < size my_plus_zero_pattern. 
Proof.
unfold my_plus_zero_pattern. 
unfold tag at 1. rewrite size_app. 
assert(size (abs (refs (0 :: nil)) (s_op2 i_op (var (ref 1))) (var (ref 1))) > 3252). 
cbv. omega. omega. 
Qed. 


 Lemma my_plus_zero_r_basic4 : 
sf_red (App my_plus_zero_r 
            (lambda_to_fieska (Abs 2 nil Closure_calculus.Iop (Tag (Tag (Closure_calculus.Ref 2) 
                                        (Closure_calculus.App (Closure_calculus.App my_plus (Closure_calculus.Ref 1)) (scott 0)))
                                   (Closure_calculus.App (Closure_calculus.App my_plus (Closure_calculus.Ref 0)) (scott 0))
                               ))))
         (lambda_to_fieska (Abs 2 nil Closure_calculus.Iop (Tag (Tag (Closure_calculus.Ref 2) (Closure_calculus.Ref 1)) (Closure_calculus.Ref 0)))). 
Proof. 
intros.
eapply transitive_red. unfold my_plus_zero_r,  lambda_to_fieska; fold lambda_to_fieska; 
unfold abs, refs, ref. 
eapply2 update_compound. 
eapply2 matchfail_compound_l.  eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l.  eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l.  eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l.  unfold A_k; auto. 
eapply2 matchfail_compound_r. 
unfold a_op; eapply2 program_matching; split_all. 
eapply2 matchfail_compound_l.  unfold A_k; auto. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_op.  unfold_op; unfold factorable; split_all. left; eauto. discriminate. 
(* 1 *) 
eapply transitive_red. eapply preserves_app_sf_red. 
eapply2 update_compound. 
eapply2 matchfail_compound_l.
(* 2 *) 
eapply2 update_compound. 
eapply2 matchfail_compound_l.  eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r. eapply2 program_matching; split_all. 
eapply2 matchfail_compound_l.  eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r.  eapply2 program_matching; split_all. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. eapply2 matchfail_compound_l.
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l.   unfold A_k; auto. 
eapply2 matchfail_compound_r. unfold_op; auto. 
eapply2 matchfail_compound_l.  unfold A_k; auto. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_op.  unfold_op; unfold factorable; split_all. left; eauto. discriminate. 
(* 1 *) 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply2 update_op. eapply2 matchfail_compound_op.  
(* 3 *) 
apply update_small.  auto.  nf_out. apply abs_fn_normal.  unfold_op; nf_out. 
eapply2 var_normal. 
replace (size (App
     (App (Op Aop)
        (App (App (Op Aop) (App (App (Op Aop) (Y_k 4)) abs_fn)) s_op))
     (s_op2 i_op (var (App s_op (App s_op s_op))))))  with 3250 by (cbv; auto). 
assert(3252 < size my_plus_zero_pattern) by eapply2 size_my_plus_zero_pattern. omega. 
cbv. omega. 
(* 2 *) 
eapply transitive_red. eapply preserves_app_sf_red. apply update_compound. 
eapply2 matchfail_compound_l.  auto. 
replace (App (App (lambda_to_fieska my_plus) (var s_op)) (lambda_to_fieska (scott 0)))
with (lambda_to_fieska (Closure_calculus.App (Closure_calculus.App my_plus (Closure_calculus.Ref 0)) (scott 0))) by auto. 
eapply2 my_plus_zero_r_basic. 
(* 2 *) 
eapply preserves_app_sf_red. eapply preserves_app_sf_red.
(* 4 *) 
eapply2 update_op. eapply2 matchfail_compound_op. 2: auto. 
(* 2 *) 
eapply2 update_compound. 
eapply2 matchfail_compound_l.  
eapply2 matchfail_compound_r.  eapply2 matchfail_compound_l.  
eapply2 matchfail_compound_r. eapply2 matchfail_compound_l.  unfold A_k; auto. 
eapply2 matchfail_compound_r.  unfold a_op; eapply2 program_matching; split_all. 
eapply2 matchfail_compound_l.  unfold A_k; auto. 
eapply2 matchfail_compound_l.  eapply2 matchfail_op.  
unfold_op; unfold factorable; split_all. left; eauto. discriminate. 
(* 1 *) 
eapply2 preserves_app_sf_red. eapply2 preserves_app_sf_red.
eapply2 preserves_app_sf_red. eapply2 preserves_app_sf_red.
(* 3 *) 
eapply2 update_small. unfold a_op; nf_out. 
eapply lt_trans. cbv. auto. 
assert(3252 < size my_plus_zero_pattern) by apply size_my_plus_zero_pattern. 
omega. 
(* 1 *) 
eapply transitive_red. apply update_compound. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r.  eapply2 matchfail_compound_r.
  unfold a_op; eapply2 program_matching; split_all. 
eapply2 matchfail_compound_l.  
eapply2 matchfail_compound_r.  eapply2 matchfail_compound_l.  
eapply2 matchfail_compound_r.  eapply2 matchfail_compound_l.  unfold A_k; auto. 
eapply2 matchfail_compound_r.  unfold a_op; eapply2 program_matching; split_all. 
eapply2 matchfail_compound_l.  unfold A_k; auto. 
eapply2 matchfail_compound_l. 
unfold_op; unfold factorable; split_all. 
 eapply2 matchfail_op. unfold_op; unfold factorable; split_all. left; eauto. discriminate. 
unfold a_op; auto. 
(* 1 *) 
eapply transitive_red. eapply preserves_app_sf_red. 
(* 3 *) 
eapply2 update_small. unfold a_op; nf_out. eapply2 var_normal. 
eapply lt_trans. cbv. auto. 
assert(3252 < size my_plus_zero_pattern) by apply size_my_plus_zero_pattern. 
omega. 
(* 2 *) 
replace (App (App (lambda_to_fieska my_plus) (var (App s_op s_op))) (lambda_to_fieska (scott 0)))
with (lambda_to_fieska (Closure_calculus.App (Closure_calculus.App my_plus (Closure_calculus.Ref 1)) (scott 0))) by auto. 
eapply2 my_plus_zero_r_basic. 
(* 1 *) 
unfold lambda_to_fieska. eapply2 zero_red.  
Qed. 


*) 


