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
(*                        SF-Calculus                                 *)
(*                                                                    *)
(* is implemented in Coq by adapting the implementation of            *) 
(* Lambda Calculus from Project Coq                                   *)
(* 2015                                                               *)
(**********************************************************************)

(**********************************************************************)
(*                       Fixpoints.v                                  *)
(*                                                                    *)
(*                        Barry Jay                                   *)
(*                                                                    *)
(**********************************************************************)

Require Import Arith Omega List Max.
Require Import IntensionalLib.SF_calculus.Test.  
Require Import IntensionalLib.SF_calculus.General.  
Require Import IntensionalLib.Wave_as_SF.SF_Terms.  
Require Import IntensionalLib.Wave_as_SF.SF_Tactics.  
Require Import IntensionalLib.Wave_as_SF.SF_reduction.  
Require Import IntensionalLib.Wave_as_SF.SF_Normal.  
Require Import IntensionalLib.Wave_as_SF.SF_Closed.  
Require Import IntensionalLib.Wave_as_SF.Substitution.  
Require Import IntensionalLib.Wave_as_SF.SF_Eval.  
Require Import IntensionalLib.Wave_as_SF.Star.  


Lemma maxvar_op: forall o, maxvar (Op o) = 0.  Proof. split_all. Qed. 


(* delayed application *) 

Definition app_comb M N := 

App (App (Op Node) (App (Op Node) i_op))
    (App (App (Op Node) (App (Op Node) (App k_op N))) (App k_op M)).

Lemma app_comb_red : forall M N P, sf_red (App (app_comb M N) P) (App (App M N) P).
Proof.
unfold app_comb; unfold_op; split_all. 
eapply succ_red. eapply2 s_red. 
eapply succ_red.  eapply app_sf_red.   
 eapply2 s_red.  eapply2 s_red. all: auto. 
eapply succ_red. eapply app_sf_red.   
 eapply app_sf_red. eapply2 k_red. all: auto.
eapply2 preserves_app_sf_red.
eapply2 preserves_app_sf_red. eval_tac. eval_tac.   
Qed. 


Lemma lift_rec_preserves_app_comb: 
forall M1 M2 n k, lift_rec (app_comb M1 M2) n k = app_comb (lift_rec M1 n k) (lift_rec M2 n k).
Proof. intros; unfold app_comb; unfold_op; split_all. Qed. 

Lemma subst_rec_preserves_app_comb: 
forall i M N k, subst_rec (app_comb i M) N k = app_comb (subst_rec i N k) (subst_rec M N k). 
Proof. intros; unfold app_comb; unfold_op; split_all.  Qed. 

Lemma app_comb_normal: forall i M, normal i -> normal M -> normal (app_comb i M). 
Proof. intros; unfold app_comb; unfold_op. repeat eapply2 nf_compound. Qed. 

Lemma maxvar_app_comb : forall M N,  maxvar (app_comb M N) = max(maxvar M) (maxvar N).
Proof. intros; unfold app_comb. unfold_op; split_all. rewrite max_swap. auto. Qed.


Lemma rank_app_comb: forall M N, rank (app_comb M N) > rank (App M N).
Proof. intros; unfold app_comb; split_all. omega. Qed.


Lemma program_app_comb2 : forall M N, program (app_comb M N) -> program M /\ program N.
Proof.
  unfold app_comb; unfold_op; intros. inversion H. simpl in H1.  max_out.
assert(normal M /\ normal N). clear - H0. 
  inversion H0. inversion H4. clear - H3.  inversion H3; subst. inversion H4.
clear - H1 H2. inversion H1; inversion H2; subst. 
inversion H10. inversion H5. inversion H10. split; auto. 
clear - H4. inversion H4. inversion H3. inversion H2. auto. auto. 
inversion H1; split; unfold program; auto. 
Qed.




Lemma app_comb_preserves_sf_red: 
forall M M' N N', 
sf_red M M' -> sf_red N N' -> 
sf_red (app_comb M N) (app_comb M' N'). 
Proof.  intros; unfold app_comb. repeat eapply2 preserves_app_sf_red.  Qed. 

Definition a_op := star_opt (star_opt (app_comb (Ref 1) (Ref 0))). 

Ltac unfold_op := unfold a_op, app_comb, i_op, k_op, node. 



Lemma a_op2_red: forall M N, sf_red (App (App a_op M) N) (app_comb M N). 
Proof.
unfold a_op; intros. eapply transitive_red. eapply2 star_opt_beta2. 
unfold subst. repeat rewrite subst_rec_preserves_app_comb. 
unfold subst_rec; fold subst_rec. insert_Ref_out. 
unfold subst_rec; fold subst_rec. insert_Ref_out. unfold lift. 
repeat rewrite lift_rec_null. 
rewrite subst_rec_lift_rec; try omega. 
repeat rewrite lift_rec_null. 
auto.
Qed. 

Lemma a_op_red: forall M N P, sf_red (App (App (App a_op M) N) P) (App (App M N) P).
Proof.
unfold a_op; intros. eapply transitive_red. eapply preserves_app_sf_red. 
eapply2 star_opt_beta2. auto. 
unfold subst. repeat rewrite subst_rec_preserves_app_comb. 
eapply transitive_red. eapply2 app_comb_red. 
unfold subst_rec; fold subst_rec. insert_Ref_out. 
unfold subst_rec; fold subst_rec. insert_Ref_out. unfold lift.  
repeat rewrite lift_rec_null. 
rewrite subst_rec_lift_rec; try omega. 
repeat rewrite lift_rec_null. 
auto.
Qed. 

Fixpoint A_k k := 
match k with 
| 0 => i_op 
| 1 => i_op 
| 2 => a_op 
| S k1 => star_opt (star_opt (App (A_k k1) (app_comb (Ref 1) (Ref 0))))
end.

Lemma A_k_closed: forall k, k < 7 -> maxvar (A_k k) = 0. 
Proof.
induction k; split_all. 
induction k; split_all.
induction k; split_all. 
induction k; split_all. 
induction k; split_all. 
induction k; split_all. 
induction k; split_all. 
noway.  
Qed. 

Lemma A_k_normal : forall k, k<5 -> normal (A_k k).
Proof.
induction k; split_all; unfold_op; auto. 
induction k; split_all; unfold_op; auto.  
induction k; split_all; unfold_op; auto. 
repeat apply nf_compound; unfold_op; auto.
induction k; split_all;
repeat apply nf_compound; unfold_op; auto. 
induction k; split_all;
repeat apply nf_compound; unfold_op; auto.
omega. 
Qed.

 Lemma A_5_normal : normal (A_k 5).
Proof.
split_all; unfold_op; auto. 
repeat apply nf_compound; unfold_op; auto.
Qed.

 
Lemma A_6_normal : normal (A_k 6).
Proof.
split_all; unfold_op; auto. 
repeat apply nf_compound; unfold_op; auto.
Qed.


Hint Resolve A_k_closed A_k_normal.



Ltac nf_out :=
  unfold a_op; unfold_op;
  match goal with
    | |- normal ?M =>
      match M with
        | star_opt _ => apply star_opt_normal; nf_out
        | app_comb _ _ => apply app_comb_normal; nf_out
        | App (App (Op _) _) _ => apply nf_compound; [| |auto]; nf_out
        | App (Op _) _ => apply nf_compound; [| |auto]; nf_out
        | lift _ _ => unfold lift; nf_out
        | lift_rec _ _ _ => eapply2 lift_rec_preserves_normal; nf_out
        | _ => split_all
      end
    | _ => auto
        end.


(* fixpoints that wait *) 


(* Y2 *) 

Definition omega2 := 
star_opt(star_opt (App (Ref 0) (app_comb (app_comb (Ref 1) (Ref 1)) (Ref 0)))).

Definition Y2 f := app_comb (app_comb omega2 omega2) f.

Lemma Y2_program: forall f, program f -> program (Y2 f).
Proof.
  unfold Y2, omega2; split_all; unfold program; split; 
unfold subst, subst_rec; fold subst_rec; nf_out; try eapply2 H. 
unfold subst, subst_rec; fold subst_rec; nf_out; try eapply2 H. 
unfold maxvar; fold maxvar. simpl. nf_out. simpl. 
  rewrite max_zero; eapply2 H. 
Qed.

Lemma omega2_omega2 : 
forall f, sf_red (App (App omega2 omega2) f) (App f (Y2 f)).
Proof.
unfold omega2 at 1. intros. 
eapply transitive_red. eapply2 star_opt_beta2. 
unfold subst, subst_rec; fold subst_rec. 
insert_Ref_out. unfold lift.  rewrite lift_rec_null.  
rewrite subst_rec_lift_rec; try omega.  
rewrite lift_rec_null. eapply2 preserves_app_sf_red. 
rewrite ! subst_rec_preserves_app_comb. 
repeat (rewrite subst_rec_ref; insert_Ref_out).  
unfold lift. rewrite ! lift_rec_null.  
rewrite subst_rec_lift_rec; try omega.  rewrite lift_rec_null. unfold Y2. auto. 
Qed. 

Lemma Y2_fix_f: forall M N, 
sf_red (App (Y2 M) N) (App (App M (Y2 M)) N).
Proof.
unfold Y2 at 1.  intros. 
eapply transitive_red. eapply2 app_comb_red. 
eapply transitive_red. eapply preserves_app_sf_red. eapply2 app_comb_red. auto. 
eapply transitive_red. eapply preserves_app_sf_red. eapply2 omega2_omega2. auto. auto. 
Qed. 

(* Y3 *) 

Definition omega3 := 
star_opt(star_opt (star_opt (App (App (Ref 1) 
  (star_opt (app_comb (app_comb (app_comb (Ref 3) (Ref 3)) (Ref 2)) (Ref 0)))) 
                                    (Ref 0)))).

Definition Y3 f := star_opt (app_comb (app_comb (app_comb omega3 omega3) (lift 1 f)) (Ref 0)).

Lemma omega3_program: program omega3. 
Proof. 
split; auto. unfold omega3; nf_out.  eapply2 nf_active.  eapply2 nf_active. 
unfold subst, subst_rec; fold subst_rec; nf_out; try eapply2 H; cbv; auto. 
Qed.  


Lemma Y3_program: forall f, program f -> program (Y3 f).
Proof.
intros.  unfold Y3; split; auto.  
nf_out; try eapply2 omega3_program.   eapply2 H. 
(* 1 *) 
rewrite maxvar_star_opt. rewrite ! maxvar_app_comb. 
replace (maxvar omega3) with 0 by eapply2 omega3_program. simpl. 
replace (maxvar (lift 1 f)) with 0. 
auto.  unfold lift; rewrite lift_rec_closed.  
assert(maxvar f = 0) by eapply2 H; auto. 
eapply2 H. 
Qed.

Lemma omega3_omega3 : 
forall f M, sf_red (App (App (App omega3 omega3) f) M) (App (App f (Y3 f)) M).
Proof.
unfold omega3 at 1. intros. 
eapply transitive_red. eapply2 star_opt_beta3. 
unfold subst; rewrite ! subst_rec_app.  
rewrite ! subst_rec_preserves_star_opt.
rewrite ! subst_rec_preserves_app_comb.
repeat (rewrite ! subst_rec_ref; insert_Ref_out). 
unfold lift; rewrite ! lift_rec_lift_rec; try omega. unfold plus. 
rewrite ! subst_rec_lift_rec; try omega. rewrite ! lift_rec_null. 
rewrite ! (lift_rec_closed omega3).  
unfold Y3.  auto. 
unfold omega3; cbv; auto. 
Qed. 



Lemma Y3_fix_f: forall M N P, 
sf_red (App (App (Y3 M) N) P) (App (App (App M (Y3 M)) N) P).
Proof.
unfold Y3 at 1.  intros. 
eapply transitive_red. eapply preserves_app_sf_red. eapply star_opt_beta. auto. 
unfold subst, subst_rec; fold subst_rec. 
rewrite ! subst_rec_preserves_app_comb. 
rewrite ! (subst_rec_closed omega3). 
2: unfold omega3; cbv; omega. 
unfold lift; rewrite subst_rec_lift_rec; try omega. 
unfold subst_rec; fold subst_rec. insert_Ref_out. unfold lift. 
rewrite ! lift_rec_null.
eapply transitive_red. eapply2 app_comb_red. 
eapply transitive_red. eapply preserves_app_sf_red. eapply2 app_comb_red. auto.  
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. eapply2 app_comb_red.
auto. auto. 
eapply transitive_red. eapply preserves_app_sf_red. eapply2 omega3_omega3. auto. auto. 
Qed. 

(* 

Definition omega_k k := 
star_opt(star_opt (App (Ref 0) (app_comb (app_comb (app_comb (A_k (S k)) (Ref 1)) (Ref 1)) 
                                    (Ref 0)))).

Definition Y_k k := app_comb (app_comb (A_k (S k)) (omega_k k)) (omega_k k). 

Lemma omega_k_normal: forall k, k<4 -> normal (omega_k k).
Proof.  
intros; unfold omega_k. repeat eapply2 star_opt_normal.
eapply2 nf_active.  repeat eapply2 app_comb_normal. 
eapply2 A_k_normal. omega.
Qed. 

(* 
Lemma omega_4_normal: normal (omega_k 4).
Proof.  
intros; unfold omega_k. repeat eapply2 star_opt_normal.
eapply2 nf_active.  repeat eapply2 app_comb_normal. 
eapply2 A_5_normal. 
Qed. 

*) 
Hint Resolve A_k_closed A_k_normal omega_k_normal. 



Lemma omega_omega : 
forall k M, k<4 -> sf_red (App (App (omega_k k) (omega_k k)) M) (App M (app_comb (Y_k k) M)).
Proof.
unfold omega_k at 1. intros. 
eapply transitive_red. eapply2 star_opt_beta2. 
unfold subst, subst_rec; fold subst_rec. 
insert_Ref_out. unfold lift.  rewrite lift_rec_null.  
rewrite subst_rec_lift_rec; try omega.  
rewrite lift_rec_null. eapply2 preserves_app_sf_red. 
repeat rewrite subst_rec_preserves_app_comb. 
repeat rewrite (subst_rec_closed (A_k (S k))); try (rewrite A_k_closed; omega). 
rewrite ! subst_rec_ref; insert_Ref_out. unfold pred. 
rewrite ! subst_rec_ref; insert_Ref_out.
unfold lift. rewrite ! lift_rec_null.  
rewrite subst_rec_lift_rec; try omega.  rewrite lift_rec_null. unfold Y_k. auto. 
Qed. 

Lemma Y_k_program: forall k, k<4 -> program (Y_k k).
Proof.
intros. unfold program. split. 
  unfold Y_k. repeat eapply2 app_comb_normal. eapply2 A_k_normal. omega.
 unfold Y_k. rewrite !  maxvar_app_comb. 
rewrite A_k_closed; try omega.  
unfold omega_k. 
rewrite ! maxvar_star_opt. unfold maxvar; fold maxvar. 
rewrite ! maxvar_app_comb. 
rewrite ! A_k_closed; try omega. simpl. auto. 
Qed. 
  
Lemma Y_k_normal: forall k, k<4 -> normal (Y_k k). Proof. eapply2 Y_k_program. Qed. 
Lemma Y_k_closed: forall k, k<4 -> maxvar (Y_k k) = 0. Proof. eapply2 Y_k_program. Qed. 


(* restore ? 

Lemma Y2_fix: forall M N, 
sf_red (App (App (Y_k 2) M) N) (App (App M (app_comb (Y_k 2) M)) N).
Proof.
unfold Y_k at 1.  intros. 
eapply transitive_red. eapply preserves_app_sf_red. eapply2 app_comb_red. auto. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply2 app_comb_red. auto. auto. 
unfold A_k; fold A_k.
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply2 star_opt_beta2. auto. auto. 
unfold subst



rewrite ! ( 
app_comb_red. auto. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply2 app_comb_red. auto. auto. 




 unfold_op.  eval_tac. eval_tac. eval_tac. eval_tac. 
  eval_tac. eval_tac. eval_tac. eval_tac.   eval_tac. eval_tac. eval_tac. eval_tac. 
  eval_tac. eval_tac. eval_tac. eval_tac.   eval_tac. eval_tac. eval_tac. eval_tac. 
  eval_tac. eval_tac. eval_tac. eval_tac.   eval_tac. eval_tac. eval_tac. eval_tac. 
  eval_tac. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red.  eapply succ_red. eapply2 f_op_red. auto. 
eval_tac. eval_tac. eval_tac. 
eapply transitive_red. eapply preserves_app_sf_red. eapply omega_omega. eval_tac. 
  eval_tac. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply succ_red. eapply2 f_op_red. auto. auto. auto. auto. auto. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply succ_red. eapply2 f_op_red. auto. auto. auto.
eapply2 preserves_app_sf_red. eapply2 preserves_app_sf_red. unfold_op. 
eapply2 preserves_app_sf_red. eapply2 preserves_app_sf_red. 
eapply2 preserves_app_sf_red. eapply2 preserves_app_sf_red. 
eval_tac. eval_tac. 
Qed. 

Lemma Y3_fix: forall M N P, 
sf_red (App (App (App (Y_k 3) M) N) P) (App (App (App M (app_comb (Y_k 3) M)) N) P).
Proof.
unfold Y_k at 1.  intros. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply2 app_comb_red. auto. auto.  
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. eapply2 app_comb_red. auto. auto. auto. 
unfold A_k; fold A_k. unfold_op.  eval_tac. eval_tac. eval_tac. eval_tac. 
  eval_tac. eval_tac. eval_tac. eval_tac.   eval_tac. eval_tac. eval_tac. eval_tac. 
  eval_tac. eval_tac. eval_tac. eval_tac.   eval_tac. eval_tac. eval_tac. eval_tac. 
  eval_tac. eval_tac. eval_tac. eval_tac.   eval_tac. eval_tac. eval_tac. eval_tac. 
  eval_tac. eval_tac. eval_tac. eval_tac.   eval_tac. eval_tac. eval_tac. eval_tac. 
  eval_tac. eval_tac. eval_tac. eval_tac.   eval_tac. eval_tac. eval_tac. eval_tac. 
  eval_tac. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red.  eapply preserves_app_sf_red.  
eapply succ_red. eapply2 f_op_red. auto. 
eval_tac. eval_tac. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply succ_red. eapply2 f_op_red. auto.  auto. 
eval_tac. eval_tac. eval_tac. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply omega_omega.  eval_tac.   eval_tac. eval_tac.  
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply succ_red. eapply2 f_op_red. auto. auto. eval_tac.  auto. auto. auto. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red.
 eapply preserves_app_sf_red. 
eapply succ_red. eapply2 f_op_red. auto. auto. auto. auto. 
eapply2 preserves_app_sf_red. eapply2 preserves_app_sf_red. eapply2 preserves_app_sf_red. 
unfold_op. 
eapply2 preserves_app_sf_red. eapply2 preserves_app_sf_red. 
eapply2 preserves_app_sf_red. eapply2 preserves_app_sf_red. 
eval_tac. eval_tac. 
Qed. 

*) 


Lemma Y4_fix: forall M N P Q, 
sf_red (App (App (App (App (Y_k 4) M) N) P) Q) (App (App (App (App M (app_comb (Y_k 4) M)) N) P) Q).
Proof.
unfold Y_k at 1.  intros. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. eapply2 app_comb_red. auto. auto.  auto.
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. eapply preserves_app_sf_red. eapply2 app_comb_red.
 auto. auto. auto. auto.  
unfold A_k; fold A_k. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red.  eapply preserves_app_sf_red. 
eapply2 star_opt_beta2. auto. auto. auto. auto. 
unfold subst; rewrite ! subst_rec_app. 
rewrite ! subst_rec_preserves_star_opt.
rewrite ! subst_rec_app. 
rewrite ! subst_rec_preserves_star_opt.
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply2 star_opt_beta2. auto. auto. auto. 
unfold subst; rewrite ! subst_rec_app. 
rewrite ! subst_rec_preserves_star_opt.
rewrite ! subst_rec_app.
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply2 star_opt_beta2. auto. auto.
unfold subst; rewrite ! subst_rec_app.
rewrite ! (subst_rec_closed a_op). 
all: cycle 1. 
unfold_op. split_all.
rewrite ! subst_rec_preserves_app_comb.
rewrite ! subst_rec_ref; insert_Ref_out. 
rewrite ! subst_rec_ref; insert_Ref_out. 
rewrite ! subst_rec_ref; insert_Ref_out. 
rewrite ! subst_rec_ref; insert_Ref_out. 
rewrite ! subst_rec_ref; insert_Ref_out. 
rewrite ! subst_rec_ref; insert_Ref_out. 
unfold lift; rewrite ! lift_rec_null.
rewrite ! subst_rec_lift_rec; try omega. 
rewrite ! lift_rec_null.
eapply transitive_red. 
eapply a_op_red.
eapply2 preserves_app_sf_red. 
eapply transitive_red. eapply2 app_comb_red.  
eapply2 preserves_app_sf_red. 
eapply transitive_red. eapply2 app_comb_red.  
eapply2 preserves_app_sf_red. 
eapply transitive_red. eapply2 app_comb_red.  
unfold omega_k at 1. 
eapply transitive_red. eapply2 star_opt_beta2. 
unfold subst; rewrite ! subst_rec_app.
rewrite ! subst_rec_ref; insert_Ref_out.
rewrite ! subst_rec_preserves_app_comb.  
 rewrite ! subst_rec_ref; insert_Ref_out. 
 rewrite ! subst_rec_ref; insert_Ref_out. 
unfold lift; rewrite ! lift_rec_null. 
rewrite ! subst_rec_lift_rec; try omega. 
rewrite lift_rec_null. 
rewrite ! subst_rec_closed. 
eapply2 zero_red.
rewrite A_k_closed. 
 omega. omega. 
rewrite ! subst_rec_closed. 
rewrite A_k_closed. 
 omega. omega.
rewrite A_k_closed. 
 omega. omega.
Qed. 

*) 

Fixpoint size M := 
match M with 
| Ref _ => 1 
| Op _ => 1
| App M1 M2 => S(size M2 + size M1)
end . 


Lemma size_Y2: size (Y2 (Op Node)) = 481.
  Proof. cbv. auto. Qed. 

(* 
Notation "A ~ B" := (App A B) (at level 79, left associativity). 
Notation S := (Op Sop).
Notation K := (App (Op Fop) (Op Fop)).
Notation I := (App (App (Op Sop) (App (Op Fop) (Op Fop))) (App (Op Fop) (Op Fop))). 

Print Y2_comb_val.


Lemma Y2_val: Y_k 2 = Y2_comb_val.
Proof.  cbv. auto. Qed.

Definition a_op_val := 
 (S ~
    (S ~ (K ~ S) ~
     (S ~ (K ~ (S ~ (K ~ S))) ~
      (S ~ (S ~ (K ~ S) ~ (S ~ (K ~ K) ~ (S ~ (K ~ S) ~ (S ~ (K ~ K) ~ I)))) ~
         (K ~ (S ~ (K ~ K) ~ I))))) ~ (K ~ (K ~ I))).

Lemma a_op_value : a_op  = a_op_val.
Proof. cbv. auto. Qed.

Lemma a_op_size : size a_op_val = 113. 
Proof. cbv. auto. Qed. 
     
  *) 