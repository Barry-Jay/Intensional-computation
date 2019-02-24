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
(*                      Tree-Calculus                                 *)
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
Require Import IntensionalLib.Tree_calculus.Tree_Terms.  
Require Import IntensionalLib.Tree_calculus.Tree_Tactics.  
Require Import IntensionalLib.Tree_calculus.Tree_reduction.  
Require Import IntensionalLib.Tree_calculus.Tree_Normal.  
Require Import IntensionalLib.Tree_calculus.Tree_Closed.  
Require Import IntensionalLib.Tree_calculus.Substitution.  
Require Import IntensionalLib.Tree_calculus.Tree_Eval.  
Require Import IntensionalLib.Tree_calculus.Star.  
Require Import IntensionalLib.Tree_calculus.Wait.  


(* fixpoints that wait *) 

(* delete ? 

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

*) 

Definition omega_k k := 
star_opt(star_opt (App (Ref 0) (app_comb (app_comb (app_comb (A_k (S k)) (Ref 1)) (Ref 1)) 
                                    (Ref 0)))).

Definition Y_k k := app_comb (app_comb (A_k (S k)) (omega_k k)) (omega_k k). 

Lemma omega_k_normal: forall k, k<5 -> normal (omega_k k).
Proof.  
intros; unfold omega_k. repeat eapply2 star_opt_normal.
eapply2 nf_active.  repeat eapply2 app_comb_normal. 
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
forall k M, k<5 -> sf_red (App (App (omega_k k) (omega_k k)) M) (App M (app_comb (Y_k k) M)).
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

Lemma Y_k_program: forall k, k<5 -> program (Y_k k).
Proof.
intros. unfold program. split. 
  unfold Y_k. repeat eapply2 app_comb_normal. 
 unfold Y_k. rewrite !  maxvar_app_comb. 
rewrite A_k_closed; try omega.  
unfold omega_k. 
rewrite ! maxvar_star_opt. unfold maxvar; fold maxvar. 
rewrite ! maxvar_app_comb. 
rewrite ! A_k_closed; try omega. simpl. auto. 
Qed. 
  
Lemma Y_k_normal: forall k, k<5 -> normal (Y_k k). Proof. eapply2 Y_k_program. Qed. 
Lemma Y_k_closed: forall k, k<5 -> maxvar (Y_k k) = 0. Proof. eapply2 Y_k_program. Qed. 




Lemma Y2_fix: forall M N, 
sf_red (App (App (Y_k 2) M) N) (App (App M (app_comb (Y_k 2) M)) N).
Proof.
unfold Y_k at 1.  intros. 
eapply transitive_red. eapply preserves_app_sf_red. eapply2 app_comb_red. auto. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply2 app_comb_red. auto. auto. 
unfold A_k; fold A_k.
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply2 star_beta2. auto. auto. 
unfold subst; rewrite ! subst_rec_preserves_app_comb. 
rewrite ! subst_rec_ref. insert_Ref_out. 
rewrite ! subst_rec_ref. insert_Ref_out. 
unfold lift; rewrite ! lift_rec_null. 
rewrite ! subst_rec_lift_rec; try omega.
rewrite ! (subst_rec_closed a_op).
2: unfold_op; auto. 
rewrite ! lift_rec_null.
eapply transitive_red. 
eapply preserves_app_sf_red.
eapply2 app_comb_red. auto. 
eapply transitive_red. 
eapply2 a_op_red.
eapply transitive_red. 
eapply preserves_app_sf_red.
eapply2 app_comb_red. auto. 
eapply2 preserves_app_sf_red.
eapply2 omega_omega. 
Qed. 
 

Lemma Y3_fix: forall M N P, 
sf_red (App (App (App (Y_k 3) M) N) P) (App (App (App M (app_comb (Y_k 3) M)) N) P).
Proof.
unfold Y_k at 1.  intros. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. eapply2 app_comb_red. auto. auto.  
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply2 app_comb_red. auto. auto. auto.  
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red.
eapply2 A3_red.  all: auto. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. eapply2 app_comb_red. all: auto. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. eapply2 A3_red. all: auto. 
eapply transitive_red. eapply preserves_app_sf_red. eapply2 app_comb_red. auto. 
unfold A_k. eapply transitive_red. eapply preserves_app_sf_red. eapply2 a_op2_red. auto.  
eapply transitive_red. eapply2 app_comb_red. 
eapply transitive_red. eapply preserves_app_sf_red. eapply2 app_comb_red. auto.  
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. eapply2 app_comb_red. all: auto. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red.
eapply2 omega_omega. all: auto.  
Qed. 
 



Lemma Y4_fix: forall M N P Q, 
sf_red (App (App (App (App (Y_k 4) M) N) P) Q) (App (App (App (App M (app_comb (Y_k 4) M)) N) P) Q).
Proof.
unfold Y_k at 1.  intros. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. eapply2 app_comb_red. all: auto. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. eapply preserves_app_sf_red. eapply2 app_comb_red. all: auto. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red.  eapply preserves_app_sf_red. 
eapply2 A3_red.  all:auto. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply2 app_comb_red.  all:auto. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply2 A3_red.  all:auto. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply2 app_comb_red. auto. auto. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply2 A3_red.  all:auto. 
eapply transitive_red. eapply preserves_app_sf_red. eapply2 app_comb_red. all: auto.
unfold A_k.  
eapply transitive_red. eapply preserves_app_sf_red. eapply2 a_op2_red. auto.  
eapply transitive_red. eapply2 app_comb_red. 
eapply transitive_red. eapply preserves_app_sf_red.
 eapply2 app_comb_red. auto. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply2 app_comb_red. all: auto. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. eapply2 app_comb_red. all: auto. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. eapply2 omega_omega.  all: auto. 
Qed. 


Fixpoint size M := 
match M with 
| Ref _ => 1 
| Op _ => 1
| App M1 M2 => S(size M2 + size M1)
end . 


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

