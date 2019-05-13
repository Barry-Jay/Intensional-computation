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
Require Import IntensionalLib.Tree_calculus.Tree_Terms.  
Require Import IntensionalLib.Tree_calculus.Tree_Tactics.  
Require Import IntensionalLib.Tree_calculus.Tree_reduction.  
Require Import IntensionalLib.Tree_calculus.Tree_Normal.  
Require Import IntensionalLib.Tree_calculus.Tree_Closed.  
Require Import IntensionalLib.Tree_calculus.Substitution.  
Require Import IntensionalLib.Tree_calculus.Tree_Eval.  
Require Import IntensionalLib.Tree_calculus.Star.  
Require Import IntensionalLib.Tree_calculus.Wait.  
Require Import IntensionalLib.Tree_calculus.Fixpoints.  
Require Import IntensionalLib.Tree_calculus.Wave_Factor.  
Require Import IntensionalLib.Tree_calculus.Wave_Factor2.  
Require Import IntensionalLib.Tree_calculus.Equal.  
Require Import IntensionalLib.Tree_calculus.Case.  
Require Import IntensionalLib.Tree_calculus.Extensions.  
Require Import IntensionalLib.Tree_calculus.Wait2.  

 

Definition h_fn := 
star_opt (star_opt (star_opt (star_opt 
(App (App (Ref 3) (App (App (Ref 3) (Ref 2)) (Ref 1))) (Ref 0))))).

Lemma h_fn_program: program h_fn. 
Proof.
unfold h_fn; split.
repeat eapply2 star_opt_normal.
repeat eapply2 maxvar_star_opt.
Qed. 
  


Lemma h_fn_not_omega: forall k, h_fn <> omega_k k. 
Proof.
  intros. 
  unfold omega_k.
  rewrite star_opt_occurs_true.
  2: unfold app_comb; unfold_op; unfold occurs, eqnat, plus. 
  2: rewrite occurs_closed; auto. 2: discriminate.
  unfold star_opt at 3.
  unfold app_comb at 1.
  rewrite (star_opt_occurs_true (App (Op Node) (App (Op Node) i_op))).
  2: rewrite ! occurs_app. 
  2: replace (occurs 0 (Ref 0)) with 1 by (cbv; auto); omega.
  2: discriminate.
  rewrite (star_opt_closed (App (Op Node) (App (Op Node) i_op))). 
  2: cbv; auto. 
  rewrite (star_opt_occurs_true (App (Op Node) (App (Op Node) (App k_op (Ref 0))))).
  2: rewrite ! occurs_app. 
  2: replace (occurs 0 (Ref 0)) with 1 by (cbv; auto); omega.
  2: discriminate.
  rewrite (star_opt_occurs_true (Op Node)). 
  2: cbv; auto. 
  2: discriminate.
  rewrite (star_opt_occurs_true (Op Node)). 
  2: cbv; auto. 
  2: discriminate.
  rewrite (star_opt_eta k_op). 
  2: cbv; auto. 
  rewrite (star_opt_closed (Op Node)); auto. subst_tac.
  rewrite (star_opt_occurs_false (App (App (Op Node) (Op Node))
                                      (app_comb (app_comb (A_k (S k)) (Ref 1)) (Ref 1)))).
  2: unfold app_comb; rewrite ! occurs_app.
  2: rewrite (occurs_closed 0 (A_k (S k))).
  2: cbv; auto.   
  2: rewrite A_k_closed; auto.   subst_tac.
  rewrite ! subst_rec_preserves_app_comb.
  rewrite subst_rec_closed.
  2: rewrite A_k_closed; auto. subst_tac. 
  rewrite star_opt_occurs_true. 
  2: unfold app_comb; unfold_op; rewrite ! occurs_app. 
  2: rewrite (occurs_closed 0 (A_k _)).  2: cbv;auto. 2: apply A_k_closed.
  2: discriminate.
  unfold h_fn.
  unfold star_opt at 4. unfold occurs, eqnat, plus. subst_tac. 
  unfold star_opt at 3. unfold occurs, eqnat, plus. subst_tac. 
  unfold star_opt at 2. unfold occurs, eqnat, plus. subst_tac. 
  unfold star_opt at 1. unfold occurs, eqnat, plus. subst_tac. 
  discriminate.
Qed. 

 
Definition h_op := app_comb (Y_k 2) h_fn .

Lemma h_red: forall M N P, sf_red (App (App (App h_op M) N) P) (App (App h_op (App (App h_op M) N)) P).
Proof.
intros. unfold h_op at 1. 
eapply transitive_red.
eapply preserves_app_sf_red. eapply preserves_app_sf_red. eapply2 app_comb_red. all: auto. 
eapply transitive_red.    
eapply2 Y2_fix.
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

  
  
Definition j_op := app_comb (Y_k 0) h_op. 

Lemma j_red: forall M, sf_red (App j_op M) (App (App h_op j_op) M).
Proof. 
intros. unfold j_op at 1. 
eapply transitive_red. eapply2 app_comb_red. 
eapply transitive_red. eapply2 Y0_fix. 
eapply2 zero_red. 
Qed. 


Definition r_op := app_comb (Y_k 1) (app_comb compose h_op).

Lemma r_red : forall M N, sf_red (App (App r_op M) N) (App (App h_op (App r_op M)) N).
Proof. 
intros. unfold r_op at 1. 
eapply transitive_red. eapply preserves_app_sf_red. eapply2 app_comb_red. auto.  
eapply transitive_red. eapply2 Y1_fix. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red.  
eapply2 app_comb_red. all: auto.  
eapply transitive_red. eapply preserves_app_sf_red. eapply2 compose_composes. auto. 
 eapply2 zero_red.
Qed. 

Lemma r_aux: 
forall M N , sf_red (App (App (Y_k 1) M) N) (app_comb (app_comb (app_comb (omega_k 1) (omega_k 1)) M) N) . 
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

Lemma subst_rec_preserves_swap: forall M N k, subst_rec (swap M) N k = swap (subst_rec M N k).
Proof. unfold swap; simpl. intros; auto. Qed. 

Definition ab_fn b' := 
  star_opt (star_opt (star_opt (App (App (App b' (Ref 0)) (Ref 2)) (Ref 1)))). 
(* b' is presumed closed *)
Definition ab_op ab' := 
star_opt (star_opt (app_comb2 (app_comb (app_comb (A_k 1) ab') (Ref 1)) (Ref 0))).

Lemma a_aux: forall b' M N, maxvar b' = 0 -> sf_red (App (App (ab_op (ab_fn b')) M) N) 
 (app_comb2 (app_comb (app_comb (A_k 1) (ab_fn b')) M) N).
Proof. 
intros. 
eapply transitive_red.
unfold ab_op. eapply2 star_opt_beta2.
unfold subst; rewrite ! subst_rec_preserves_app_comb2.
rewrite ! subst_rec_preserves_app_comb.
rewrite ! (subst_rec_closed (A_k 1)).
2: rewrite A_k_closed; omega.
rewrite ! (subst_rec_closed (ab_fn b')).
all: cycle 1. 
unfold ab_fn. rewrite ! maxvar_star_opt.  simpl; auto.
rewrite H; auto. 
unfold ab_fn. rewrite ! maxvar_star_opt.  simpl; auto.
rewrite H; auto.
rewrite ! subst_rec_ref.  insert_Ref_out. 
unfold lift. rewrite lift_rec_null.
rewrite subst_rec_lift_rec; try omega. 
rewrite ! subst_rec_ref.  insert_Ref_out. 
unfold lift; rewrite ! lift_rec_null.
  auto. 
Qed.  

Definition ab1 b' P := 
  (App
     (App (Op Node)
        (App (Op Node)
           (App
              (App (Op Node)
                 (App (Op Node)
                    (App
                       (App (Op Node)
                          (App (Op Node)
                             (App
                                (App (Op Node)
                                   (App (Op Node)
                                      (App k_op
                                         (App
                                            (App (Op Node)
                                               (App (Op Node) (Op Node)))
                                            (App (Op Node) (Op Node))))))
                                (App
                                   (App (Op Node)
                                      (App (Op Node)
                                         (App
                                            (App (Op Node)
                                               (App (Op Node)
                                                  (App (Op Node) (Op Node))))
                                            (App k_op (Op Node)))))
                                   (App k_op (Op Node))))))
                       (App k_op (App (Op Node) (Op Node))))))
              (App k_op
                 (App (Op Node)
                    (App (Op Node)
                       (App (App (Op Node) (Op Node))
                          (App
                             (App (Op Node)
                                (App (Op Node)
                                   (App
                                      (App (Op Node)
                                         (App (Op Node) (Op Node)))
                                      (App (Op Node) (Op Node)))))
                             (App
                                (App (Op Node)
                                   (App (Op Node)
                                      (App (App (Op Node) (Op Node)) P)))
                                (App (App (Op Node) (Op Node))
                                   (App
                                      (App (Op Node)
                                         (App (Op Node)
                                            (App
                                               (App (Op Node)
                                                  (App (Op Node) (Op Node)))
                                               (App (Op Node) (Op Node)))))
                                      (App
                                         (App (Op Node)
                                            (App (Op Node)
                                               (App (App (Op Node) (Op Node))
                                                  b')))
                                         (App (App (Op Node) (Op Node))
                                            (A_k 1))))))))))))))
     (star_opt
        (App (Op Node)
           (App (Op Node)
              (App (App (Op Node) (App (Op Node) (Op Node)))
                 (App (Op Node) (Op Node)))))))
.

Lemma a1_aux : forall b' P, maxvar b' = 0 -> sf_red (App (ab_op b') P) (ab1 b' P).
Proof.
intros. 
unfold ab_op.
eapply transitive_red. 
eapply2 star_opt_beta.
unfold subst; rewrite subst_rec_preserves_star_opt.
rewrite subst_rec_preserves_app_comb2. 
rewrite ! subst_rec_preserves_app_comb.
rewrite ! subst_rec_ref. insert_Ref_out. 
rewrite ! subst_rec_closed.
2: rewrite H; auto. 
2: rewrite A_k_closed; auto.  
unfold app_comb2, flip.
unfold app_comb at 1. 
rewrite star_opt_occurs_true.
all: cycle 1. 
rewrite ! occurs_app. 
replace (occurs 0 (Ref 0)) with 1 by auto. 
omega. 
discriminate. 
rewrite star_opt_occurs_true.
all: cycle 1. 
rewrite ! occurs_app. 
replace (occurs 0 (Ref 0)) with 1 by auto.
omega.
discriminate.
rewrite star_opt_occurs_true.
all: cycle 1. 
rewrite ! occurs_app. 
replace (occurs 0 (Ref 0)) with 1 by auto.
omega.
discriminate.
rewrite star_opt_occurs_true.
all: cycle 1. 
rewrite ! occurs_app. 
replace (occurs 0 (Ref 0)) with 1 by auto.
omega.
discriminate.
rewrite star_opt_closed. 2: cbv; auto. 
rewrite star_opt_occurs_true.
all: cycle 1. 
rewrite ! occurs_app. 
replace (occurs 0 (Ref 0)) with 1 by auto.
omega.
discriminate.
rewrite star_opt_occurs_true.
all: cycle 1. 
rewrite ! occurs_app. 
replace (occurs 0 (Ref 0)) with 1 by auto.
omega.
discriminate.
rewrite star_opt_eta. 2: cbv; auto.
rewrite (star_opt_occurs_false (App (Op Node)
                      (App (Op Node)
                           (App k_op (app_comb (app_comb (A_k 1) b') (lift 1 P)))))).
2: unfold_op; simpl. 2: unfold lift; rewrite occurs_lift_rec_zero.
2: rewrite occurs_closed; auto. subst_tac.
rewrite ! star_opt_closed. subst_tac.
all: cycle 1.
cbv; auto.
cbv; auto.
auto.
(* 1 *)
subst_tac. rewrite ! subst_rec_preserves_app_comb.
rewrite subst_rec_closed.
2: rewrite A_k_closed; auto.
rewrite subst_rec_closed.
2: rewrite H; auto.
unfold lift;  subst_tac.
unfold ab1.
rewrite star_opt_closed.
2: cbv; auto.
unfold app_comb; unfold_op.  
apply zero_red.
Qed. 



Definition b_fn := 
star_opt (star_opt (star_opt (
extension (app_comb (app_comb (app_comb (app_comb (omega_k 2) (omega_k 2)) h_fn) (Ref 0)) (Ref 1))
          (App (App (App (App (Ref 4) (Ref 3)) (Ref 2)) (Ref 0))   (* H (Ref 0) (Ref 1) *)
               (App (App (App (Ref 4) (Ref 3)) (Ref 2)) (Ref 1))) (
extension (app_comb (app_comb (app_comb (app_comb (omega_k 2) (omega_k 2)) (Ref 0)) (Ref 1)) (Ref 2)) (
          (App (App (app_comb (app_comb (app_comb (A_k 3) (omega_k 2)) (omega_k 2)) (Ref 0))
               (App (App (App (Ref 5) (Ref 4)) (Ref 3)) (Ref 1)))   (* B (Ref 0) (Ref 1) *)
               (App (App (App (Ref 5) (Ref 4)) (Ref 3)) (Ref 2))) ) (
extension (app_comb (app_comb (app_comb (omega_k 1) (omega_k 1)) (Ref 0)) (Ref 1)) (* R (Ref 1) *) 
          (App (Ref 2) (Ref 1)) (
extension (app_comb (Y_k 0) (Ref 0)) (* J *) 
          (Ref 2)  ( 
extension (app_comb2 (app_comb (app_comb (A_k 1) (Ref 0)) (Ref 1)) (Ref 2))  (* A B' (Ref 1) (Ref 2) *) 
                                       (* use (Ref 3) not (Ref 1) because ab_op binds two times *) 
          (App (App (ab_op (Ref 3))
                    (App (App (App (Ref 5) (Ref 4)) (Ref 3)) (Ref 2))) 
               (Ref 0)) (
                     (* abs_op, as defined below *) 
extension (ab1 (Ref 0) (Ref 1)) 
          (App (App (App (App (Ref 4) (Ref 3)) (Ref 2)) (ab_op (Ref 2)))
               (App (App (App (Ref 4) (Ref 3)) (Ref 2)) (Ref 1))) (
                                       (* use (Ref 2) not (Ref 0) because ab_op binds two times *) 
extension (app_comb a_op (app_comb (app_comb (app_comb (omega_k 2) (omega_k 2)) (Ref 0)) (Ref 1)))
          (App 

(App (App (App (Ref 4) (Ref 3)) (Ref 2)) 
(app_comb (app_comb (app_comb (A_k 3) (omega_k 2)) (omega_k 2)) (Ref 0)))

(App (App (App (Ref 4) (Ref 3)) (Ref 2)) 
 (Ref 1)))
             (* for compounds H x and B x *) 
i_op)))))))))
.


Definition b_op := app_comb (Y_k 2) b_fn .

Definition abs_op := ab_op (ab_fn b_op). 

 

Lemma maxvar_ab_fn: forall M, maxvar (ab_fn M) = pred (pred (pred (maxvar M))). 
Proof. 
intro; unfold ab_fn. 
rewrite ! maxvar_star_opt. 
rewrite ! maxvar_app. rewrite ! maxvar_ref. rewrite ! max_pred. simpl. 
rewrite ! max_zero. auto. 
Qed. 




Lemma maxvar_ab_op: forall M, maxvar (ab_op M) = pred (pred (maxvar M)).
Proof. 
intros; unfold ab_op. rewrite ! maxvar_star_opt.
rewrite maxvar_app_comb2.
rewrite ! maxvar_app_comb.
rewrite A_k_closed.
rewrite ! maxvar_ref.
simpl. rewrite ! max_pred. simpl.  rewrite ! max_zero. auto. 
Qed. 

Lemma maxvar_ab1: forall b' P, maxvar (ab1 b' P) = max (maxvar P) (maxvar b').
Proof.
intros. unfold ab1. unfold_op. 
rewrite ! maxvar_app.
rewrite ! maxvar_op.  simpl. 
rewrite ! max_zero.   auto. 
Qed. 

Lemma pattern_size_ab1: forall b' P, pattern_size (ab1 b' P) = pattern_size P + pattern_size b'.
Proof.
intros. cbv. fold plus. rewrite ! plus_0_r. auto.  
Qed. 



Lemma pattern_size_app_comb2 : 
forall M N, pattern_size (app_comb2 M N) = pattern_size M + pattern_size N. 
Proof. 
intros. unfold app_comb2. rewrite pattern_size_app_comb. 
unfold flip. unfold_op. simpl. omega. 
Qed. 



Lemma b_fn_closed: maxvar b_fn = 0.
Proof.
unfold b_fn. 
rewrite ! maxvar_star_opt.
rewrite ! maxvar_extension.
rewrite pattern_size_ab1.  
rewrite pattern_size_app_comb2. 
rewrite ! pattern_size_app_comb. 
rewrite ! pattern_size_ref. 
rewrite ! pattern_size_closed.
2: cbv; auto. 
2: eapply2 A_k_closed.
2: eapply2 Y_k_closed. 
2: eapply2 omega_k_closed. 
2: eapply2 omega_k_closed.
2: eapply2 h_fn_program.
(* 1 *) 
rewrite ! maxvar_app. 
rewrite ! maxvar_ref.
rewrite ! maxvar_app_comb. 
rewrite ! A_k_closed.
rewrite ! omega_k_closed. 
unfold ab_op. 
rewrite ! maxvar_star_opt.
rewrite maxvar_app_comb2.
rewrite ! maxvar_app_comb.  
rewrite A_k_closed. auto. 
Qed. 


Lemma b_op_closed: maxvar b_op = 0.
Proof. 
unfold b_op. 
rewrite maxvar_app_comb. 
rewrite Y_k_closed. unfold max. 
eapply2 b_fn_closed.
Qed.


 
Lemma abs2_red : forall M N, sf_red (App (App abs_op M) N) 
(app_comb2
     (app_comb
        (app_comb (A_k 1)
           (star_opt
              (star_opt
                 (star_opt (App (App (App b_op (Ref 0)) (Ref 2)) (Ref 1))))))
        M) N).
Proof. 
intros. unfold abs_op, ab_op, ab_fn.
eapply transitive_red. eapply2 star_opt_beta2.
unfold subst; rewrite ! subst_rec_preserves_app_comb2. rewrite ! subst_rec_preserves_app_comb.
rewrite ! subst_rec_preserves_star_opt.
rewrite ! subst_rec_app.  
rewrite ! subst_rec_ref. insert_Ref_out.   
rewrite ! subst_rec_ref. insert_Ref_out.   
unfold lift; rewrite ! lift_rec_null. 
rewrite subst_rec_lift_rec; try omega.
rewrite lift_rec_null. 
rewrite ! subst_rec_closed. 
2: rewrite b_op_closed; auto.
2: rewrite subst_rec_closed; rewrite b_op_closed; try omega. 
2: rewrite A_k_closed; omega. 
2: rewrite subst_rec_closed; rewrite A_k_closed; try omega.
auto. 
Qed. 

Lemma abs_red : forall M N P, sf_red (App (App (App abs_op M) N) P) (App (App (App b_op P) M) N).
Proof. 
intros. 
eapply transitive_red. eapply preserves_app_sf_red. eapply2 abs2_red. auto. 
eapply transitive_red. eapply2 app_comb2_red. 
eapply transitive_red. eapply preserves_app_sf_red. 
eapply2 app_comb_red. auto.  
eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red. 
eapply2 app_comb_red. auto. auto.  
eapply transitive_red.
eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red.  
eapply2 A3_red. all: auto.
eapply transitive_red.  eapply preserves_app_sf_red. 
eapply2 app_comb_red. auto. 
unfold A_k. eapply transitive_red. eapply preserves_app_sf_red. 
eapply2 a_op2_red. auto. 
eapply transitive_red. eapply2 app_comb_red.
eapply transitive_red. eapply preserves_app_sf_red. 
eapply2 app_comb_red. auto.
eapply transitive_red. eapply2 star_opt_beta3. 
unfold subst, subst_rec; fold subst_rec. 
insert_Ref_out. 
rewrite ! subst_rec_ref; insert_Ref_out. 
unfold lift; rewrite ! lift_rec_null.
rewrite ! subst_rec_lift_rec; try omega.
rewrite subst_rec_ref; insert_Ref_out. 
rewrite ! lift_rec_null.
rewrite ! subst_rec_closed. 
2: rewrite b_op_closed; auto. 
2: rewrite ! subst_rec_closed; rewrite b_op_closed; auto.
2: rewrite ! subst_rec_closed. 
2: rewrite b_op_closed; auto.
2: rewrite b_op_closed; auto.
2: rewrite ! subst_rec_closed. 
2: rewrite b_op_closed; auto.
2: rewrite b_op_closed; auto.
unfold lift; rewrite lift_rec_null.
auto. 
Qed. 
 
