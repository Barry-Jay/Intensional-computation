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
(* 021101301 USA                                                     *)
(**********************************************************************)

(**********************************************************************)
(*                    Abstraction.v                                   *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)


Require Import Omega Max Bool List.
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
Require Import IntensionalLib.Wave_as_SF.Wait.  
Require Import IntensionalLib.Wave_as_SF.Fixpoints.  
Require Import IntensionalLib.Wave_as_SF.Wave_Factor.  
Require Import IntensionalLib.Wave_as_SF.Wave_Factor2.  
Require Import IntensionalLib.Wave_as_SF.Equal.  
Require Import IntensionalLib.Wave_as_SF.Extensions.  
Require Import IntensionalLib.Wave_as_SF.Wait2.  

 
Definition h_fn := 
star_opt (star_opt (star_opt (star_opt 
(App (App (Ref 3) (App (App (Ref 3) (Ref 2)) (Ref 1))) (Ref 0))))).

Definition h_op := app_comb (Y_k 4) h_fn .

Lemma h_red: forall M N P, sf_red (App (App (App h_op M) N) P) (App (App h_op (App (App h_op M) N)) P).
Proof.
intros. unfold h_op at 1. 
eapply transitive_red.
eapply preserves_app_sf_red. eapply preserves_app_sf_red. eapply2 app_comb_red. all: auto. 
eapply transitive_red.    
eapply2 Y4_fix.
unfold h_fn at 1. 
eapply transitive_red.
eapply preserves_app_sf_red. 
eapply2 star_opt_beta3. auto. 
unfold subst. 
rewrite ! subst_rec_preserves_star_opt. 
eapply transitive_red. 
eapply2 star_opt_beta.  
unfold subst; 
unfold subst_rec; fold subst_rec. 
insert_Ref_out. 
unfold subst_rec; fold subst_rec. 
insert_Ref_out. 
unfold lift; rewrite ! lift_rec_lift_rec; try omega. unfold plus.
rewrite ! subst_rec_lift_rec; try omega. 
unfold subst_rec; fold subst_rec. 
insert_Ref_out. 
unfold subst_rec; fold subst_rec. 
insert_Ref_out.
unfold lift; rewrite ! subst_rec_lift_rec; try omega. 
rewrite ! lift_rec_null. 
eapply2 zero_red.
Qed. 

  
  
Definition j_op := app_comb (Y_k 2) h_op. 

Lemma j_red: forall M, sf_red (App j_op M) (App (App h_op j_op) M).
Proof. 
intros. unfold j_op at 1. 
eapply transitive_red. eapply2 app_comb_red. 
eapply transitive_red. eapply2 Y2_fix. 
eapply2 zero_red. 
Qed. 


Definition r_op := app_comb (Y_k 3) (app_comb compose h_op).

Lemma r_red : forall M N, sf_red (App (App r_op M) N) (App (App h_op (App r_op M)) N).
Proof. 
intros. unfold r_op at 1. 
eapply transitive_red. eapply preserves_app_sf_red. eapply2 app_comb_red. auto.  
eapply transitive_red. eapply2 Y3_fix. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red.  
eapply2 app_comb_red. all: auto.  
eapply transitive_red. eapply preserves_app_sf_red. eapply2 compose_composes. auto. 
 eapply2 zero_red.
Qed. 

Lemma r_aux: 
forall M N , sf_red (App (App (Y_k 3) M) N) (app_comb (app_comb (app_comb (omega_k 3) (omega_k 3)) M) N) . 
Proof. 
intros; unfold Y_k.
eapply transitive_red. eapply preserves_app_sf_red.
eapply2 app_comb_red. auto.    
eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red.
eapply2 app_comb_red. all: auto.
eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red.
eapply2 A3_red. all: auto.
eapply transitive_red. eapply preserves_app_sf_red.
eapply2 app_comb_red. auto.    
eapply transitive_red. eapply preserves_app_sf_red. 
eapply2 A3_red. all: auto.
eapply transitive_red. 
eapply2 app_comb_red. 
unfold A_k.    
eapply2 a_op2_red.
Qed.  

Definition ab_fn b' := star_opt (star_opt (star_opt (App (App (App b' (Ref 0)) (Ref 2)) (Ref 1)))). 
(* b' is presumed closed *) 
Definition ab_op b' := app_comb (A_k 3) (ab_fn b').

Lemma a_aux: forall b' M N, sf_red (App (App (ab_op b') M) N) 
  (app_comb (app_comb (ab_fn b') M) N). 
Proof. 
intros.  unfold a_op. 
eapply transitive_red. eapply preserves_app_sf_red.
eapply2 app_comb_red. auto.    
eapply transitive_red. eapply preserves_app_sf_red.  
eapply2 A3_red. all: auto.
eapply transitive_red. 
eapply2 app_comb_red.     
unfold A_k. eapply transitive_red.
eapply2 a_op2_red. all: auto.
Qed.  

Lemma Y4_aux : forall M N P, sf_red (App (App (app_comb (Y_k 4) M) N) P) 
(app_comb (app_comb (app_comb (app_comb (omega_k 4) (omega_k 4)) M) N) P).
Proof. 
intros.  
eapply transitive_red. eapply preserves_app_sf_red.
eapply2 app_comb_red. auto.
unfold Y_k; fold Y_k.     
eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red.
eapply2 app_comb_red. all: auto.
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red.
eapply preserves_app_sf_red.
eapply2 app_comb_red. all: auto.
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red.
eapply preserves_app_sf_red.
eapply2 A3_red. all: auto.
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red.
eapply2 app_comb_red. all: auto.
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red.
eapply2 A3_red. all: auto.
eapply transitive_red. eapply preserves_app_sf_red. 
eapply2 app_comb_red. all: auto.
eapply transitive_red. eapply preserves_app_sf_red. 
eapply2 A3_red. all: auto.
eapply transitive_red. 
eapply2 app_comb_red.
unfold A_k. 
eapply2 a_op2_red.  
Qed. 
    
    


Lemma pattern_size_app_comb: forall M N, pattern_size (app_comb M N) = pattern_size N + pattern_size M. 
Proof. intros. unfold app_comb. simpl. auto. Qed. 

Lemma omega_k_closed: forall k, maxvar(omega_k k) = 0. 
Proof. 
induction k; split_all. 
unfold omega_k; fold omega_k. 
rewrite ! maxvar_star_opt. 
rewrite maxvar_app. 
rewrite ! maxvar_app_comb. 
rewrite A_k_closed.
simpl. auto.
Qed.
 
Definition b_fn := 
star_opt (star_opt (star_opt (
extension (app_comb (app_comb (app_comb (app_comb (omega_k 4) (omega_k 4)) h_fn) (Ref 0)) (Ref 1))
          (App (App (App (App (Ref 4) (Ref 3)) (Ref 2)) (Ref 0))   (* H (Ref 0) (Ref 1) *)
               (App (App (App (Ref 4) (Ref 3)) (Ref 2)) (Ref 1))) (
extension (app_comb (app_comb (app_comb (app_comb (omega_k 4) (omega_k 4)) (Ref 0)) (Ref 1)) (Ref 2)) (
          (App (App (app_comb (app_comb (app_comb (A_k 5) (omega_k 4)) (omega_k 4)) (Ref 0))
               (App (App (App (Ref 5) (Ref 4)) (Ref 3)) (Ref 1)))   (* B (Ref 0) (Ref 1) *)
               (App (App (App (Ref 5) (Ref 4)) (Ref 3)) (Ref 2))) ) (
extension (app_comb (app_comb (app_comb (omega_k 3) (omega_k 3)) (Ref 0)) (Ref 1)) (* R (Ref 1) *) 
          (App (Ref 2) (Ref 1)) (
extension (app_comb (Y_k 2) (Ref 0)) (* J *) 
          (Ref 2)  ( 
extension (app_comb (app_comb (Ref 0) (Ref 1)) (Ref 2))  (* A B' (Ref 1) (Ref 2) *) 
                                                                 (* use (Ref 3) not (Ref 0) because ab_op binds three times *) 

          (App (App (app_comb (A_k 3) (Ref 0)) (App (App (App (Ref 5) (Ref 4)) (Ref 3)) (Ref 1))) (Ref 2)) 
                     (* abs_op, as defined below *) 

(* wrong 
extension (app_comb a_op (app_comb (app_comb (Ref 0) (Ref 1)) (Ref 2))) (* A (Ref 1) (Ref 2) *) 
          (app_comb a_op (app_comb (app_comb (Ref 0) (App (App (App (Ref 5) (Ref 4)) (Ref 3)) (Ref 1))) (Ref 2))) 
*)
i_op)))))))
.

Definition b_op := app_comb (Y_k 4) b_fn .

Definition abs_op := ab_op b_op. 

(* do a lemma here that confirms the matching wrt A *) 

Lemma maxvar_ref: forall n, maxvar (Ref n) = S n. Proof. split_all.  Qed. 



Lemma b_op_closed: maxvar b_op = 0.
Proof. 
unfold b_op. 
rewrite maxvar_app_comb. 
rewrite Y_k_closed. 2: omega. unfold max. 
unfold b_fn. 
rewrite ! maxvar_star_opt.
rewrite ! maxvar_extension. 
unfold pattern_size; fold pattern_size. 
rewrite ! maxvar_app. rewrite ! maxvar_ref.  
rewrite ! maxvar_app_comb.
rewrite ! (omega_k_closed). 
rewrite ! pattern_size_app_comb. 
rewrite A_k_closed. 
rewrite  (pattern_size_closed (omega_k _)) at 1.  
rewrite  (pattern_size_closed (omega_k _)) at 1.  
rewrite  (pattern_size_closed (omega_k _)) at 1.  
rewrite  (pattern_size_closed (omega_k _)) at 1.  
rewrite  (pattern_size_closed (omega_k _)) at 1.  
rewrite  (pattern_size_closed (omega_k _)) at 1.  
rewrite  (pattern_size_closed (h_fn)).  
rewrite  (pattern_size_closed (Y_k _)) at 1.
unfold pattern_size; fold pattern_size. unfold plus; fold plus.  
 all : (try (rewrite omega_k_closed; auto)). 2: eapply2 Y_k_closed. 
2: simpl; auto. 
replace (pattern_size (ab_fn (Ref 3))) with 1. 
replace (maxvar (Y_k 4)) with 0. 
cbv. auto.
rewrite Y_k_closed. auto. omega.   
unfold ab_fn. 
unfold star_opt at 3. unfold occurs0. rewrite ! orb_false_l. 
rewrite ! orb_true_l.
unfold_op; unfold subst, subst_rec. insert_Ref_out. 
rewrite star_opt_occurs_true.
cbv. auto. cbv. auto. congruence.  
Qed. 


 
Lemma abs2_red : forall M N, sf_red (App (App abs_op M) N) (app_comb (app_comb (ab_fn b_op) M) N).
Proof. 
intros. unfold abs_op, ab_op, ab_fn.
eapply transitive_red.  eapply preserves_app_sf_red. 
 eapply2 app_comb_red. auto. 
eapply transitive_red. eapply preserves_app_sf_red. eapply2 A3_red. auto. 
eapply transitive_red. eapply2 app_comb_red. unfold A_k. 
eapply transitive_red. eapply2 a_op2_red. auto. 
Qed. 
    

Lemma abs_red : forall M N P, sf_red (App (App (App abs_op M) N) P) (App (App (App b_op P) M) N).
Proof. 
intros. unfold abs_op, ab_op.
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red.
eapply2 app_comb_red. all: auto.
eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red. 
eapply2 A3_red. all: auto.
eapply transitive_red.  eapply preserves_app_sf_red. 
eapply2 app_comb_red. auto. 
unfold A_k. eapply transitive_red. eapply preserves_app_sf_red. 
eapply2 a_op2_red. auto. 
eapply transitive_red. eapply2 app_comb_red.
eapply transitive_red. eapply preserves_app_sf_red. 
eapply2 app_comb_red. auto.
unfold ab_fn.  eapply transitive_red.
eapply2 star_opt_beta3. 
unfold subst, subst_rec, lift; fold subst_rec. 
insert_Ref_out. 
unfold lift; rewrite ! lift_rec_null. 
unfold subst, subst_rec, lift; fold subst_rec. 
insert_Ref_out. 
unfold lift; rewrite ! lift_rec_null. 
rewrite ! subst_rec_lift_rec; try omega. 
unfold subst, subst_rec, lift; fold subst_rec. 
insert_Ref_out. 
unfold lift; rewrite ! lift_rec_null. 
replace (subst_rec b_op (lift_rec P 0 2) 0) with b_op.
2: rewrite (subst_rec_closed b_op). 2: auto.
2: rewrite b_op_closed; omega.  
replace (subst_rec b_op (lift_rec N 0 1) 0) with b_op.
2: rewrite (subst_rec_closed b_op). 2: auto.
2: rewrite b_op_closed; omega.  
replace (subst_rec b_op M 0) with b_op.
2: rewrite (subst_rec_closed b_op). 2: auto.
2: rewrite b_op_closed; omega.   auto.
Qed.


Lemma Fop_closed: maxvar Fop = 0.
Proof. 
unfold Fop.   unfold is_leaf, is_stem, is_fork, swap. 
unfold tree_test; unfold_op. 
rewrite ! maxvar_star_opt.
rewrite ! maxvar_app.
rewrite ! maxvar_star_opt.
rewrite ! maxvar_app.
cbv. auto. 
Qed. 
