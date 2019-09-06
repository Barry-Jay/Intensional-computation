
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

Require Import Bool Arith Omega List Max.
Require Import IntensionalLib.SF_calculus.Test.  
Require Import IntensionalLib.SF_calculus.General.  
Require Import IntensionalLib.SF_calculus.SF_Terms.  
Require Import IntensionalLib.SF_calculus.SF_Tactics.  
Require Import IntensionalLib.SF_calculus.SF_reduction.  
Require Import IntensionalLib.SF_calculus.SF_Normal.  
Require Import IntensionalLib.SF_calculus.SF_Closed.  
Require Import IntensionalLib.SF_calculus.Substitution.  
Require Import IntensionalLib.SF_calculus.SF_Eval.  
Require Import IntensionalLib.SF_calculus.Star.  


Lemma maxvar_op: forall o, maxvar (Op o) = 0.  Proof. split_all. Qed. 


(* delayed application *) 

Definition app_comb M N := 
App (App s_op (App (App s_op (App k_op M)) (App k_op N))) i_op. 

Lemma app_comb_red : forall M N P, sf_red (App (app_comb M N) P) (App (App M N) P).
Proof.
unfold app_comb; unfold_op; split_all. 
eapply succ_red. eapply2 s_red. 
eapply succ_red. eapply app_sf_red. eapply2 s_red.  eapply2 s_red. 
eapply succ_red. eapply app_sf_red. eapply app_sf_red. eapply2 f_op_red.  eapply2 f_op_red.  
eapply2 f_op_red.  
auto. 
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
Proof. intros; unfold app_comb. unfold_op; split_all. rewrite max_zero. auto. Qed.


Lemma rank_app_comb: forall M N, rank (app_comb M N) > rank (App M N).
Proof. intros; unfold app_comb; split_all. omega. Qed.

Lemma program_app_comb2 : forall M N, program (app_comb M N) -> program M /\ program N.
Proof.
  unfold app_comb; unfold_op; intros. inversion H. simpl in H1. max_out. max_out.
  inversion H0; inversion H6; inversion H12; inversion H16; inversion H22; inversion H17; 
  unfold program; repeat split; split_all. 
Qed.




Lemma app_comb_preserves_sf_red: 
forall M M' N N', 
sf_red M M' -> sf_red N N' -> 
sf_red (app_comb M N) (app_comb M' N'). 
Proof.  intros; unfold app_comb. repeat eapply2 preserves_app_sf_red.  Qed.

Definition a_op := App
    (App (Op Sop)
       (App (App (Op Sop) (App (App (Op Fop) (Op Fop)) (Op Sop)))
          (App
             (App (Op Sop)
                (App (App (Op Fop) (Op Fop)) (App (Op Sop) (App (App (Op Fop) (Op Fop)) (Op Sop)))))
             (App
                (App (Op Sop)
                   (App (App (Op Sop) (App (App (Op Fop) (Op Fop)) (Op Sop)))
                      (App (App (Op Sop) (App (App (Op Fop) (Op Fop)) (App (Op Fop) (Op Fop))))
                         (App (App (Op Sop) (App (App (Op Fop) (Op Fop)) (Op Sop)))
                            (App (Op Fop) (Op Fop))))))
                (App (App (Op Fop) (Op Fop)) (App (Op Fop) (Op Fop)))))))
    (App (App (Op Fop) (Op Fop))
         (App (App (Op Fop) (Op Fop)) (App (App (Op Sop) (App (Op Fop) (Op Fop))) (App (Op Fop) (Op Fop))))).


Lemma a_op_val: a_op = star_opt (star_opt (app_comb (Ref 1) (Ref 0))).
Proof.  unfold a_op, app_comb; unfold_op; simpl; unfold_op; unfold subst; simpl; auto. Qed. 
  

Ltac unfold_op := unfold a_op, app_comb, i_op, k_op, s_op, f_op. 



Lemma a_op2_red: forall M N, sf_red (App (App a_op M) N) (app_comb M N). 
Proof.
  unfold_op; intros. repeat eval_tac.
Qed.


Lemma a_op_red: forall M N P, sf_red (App (App (App a_op M) N) P) (App (App M N) P).
Proof.
  unfold a_op; intros. do 20 eval_tac.
  eapply2 preserves_app_sf_red.  eapply2 preserves_app_sf_red. 
  all: repeat   eval_tac. 
Qed. 

Fixpoint A_k k := 
match k with 
| 0 => i_op 
| 1 => i_op 
| 2 => a_op 
| S k1 => App (App s_op (App k_op (App s_op (App k_op (A_k k1))))) a_op 
end.

Lemma A_k_closed: forall k, maxvar (A_k k) = 0. 
Proof.
induction k; intros. split_all. 
induction k; intros. split_all. 
clear IHk0. induction k; intros. split_all. clear IHk0.
unfold A_k in *; fold A_k in *.  
repeat rewrite maxvar_app. simpl. rewrite IHk. auto. 
Qed. 

Lemma A_k_normal : forall k, normal (A_k k).
Proof.
induction k; split_all. 
unfold_op; auto. 
induction k; split_all. 
induction k; split_all. 
unfold_op; auto. repeat eapply2 star_opt_normal. 
repeat eapply2 nf_compound.
unfold_op. repeat apply nf_compound; unfold_op; auto.
Qed. 

Hint Resolve A_k_closed A_k_normal.



Ltac nf_out :=
  unfold a_op; unfold_op;
  match goal with
    | |- normal ?M =>
      match M with
        | star_opt _ => apply star_opt_normal; nf_out
        | A_k _ => apply A_k_normal; nf_out
        | app_comb _ _ => apply app_comb_normal; nf_out
          | App (App (Op _) _) _ => apply nf_compound; [| |auto]; nf_out
          | App (Op _) _ => apply nf_compound; [| |auto]; nf_out
          | _ => split_all
      end
    | _ => auto
        end.


(* fixpoints that wait *) 

(* Y2 *) 

Definition omega2 := 
 App
    (App (Op Sop)
       (App (App (Op Fop) (Op Fop))
          (App (Op Sop) (App (App (Op Sop) (App (Op Fop) (Op Fop))) (App (Op Fop) (Op Fop))))))
    (App
       (App (Op Sop)
          (App (App (Op Sop) (App (App (Op Fop) (Op Fop)) (Op Sop)))
             (App
                (App (Op Sop)
                   (App (App (Op Fop) (Op Fop)) (App (Op Sop) (App (App (Op Fop) (Op Fop)) (Op Sop)))))
                (App
                   (App (Op Sop)
                      (App (App (Op Sop) (App (App (Op Fop) (Op Fop)) (Op Sop)))
                         (App (App (Op Sop) (App (App (Op Fop) (Op Fop)) (App (Op Fop) (Op Fop))))
                            (App (App (Op Sop) (App (App (Op Fop) (Op Fop)) (Op Sop)))
                               (App (App (Op Sop) (App (App (Op Fop) (Op Fop)) (App (Op Fop) (Op Fop))))
                                  (App
                                     (App (Op Sop)
                                        (App (App (Op Sop) (App (App (Op Fop) (Op Fop)) (Op Sop)))
                                           (App
                                              (App (Op Sop)
                                                 (App
                                                    (App (Op Sop) (App (App (Op Fop) (Op Fop)) (Op Sop)))
                                                    (App (Op Fop) (Op Fop)))) 
                                              (App (Op Fop) (Op Fop)))))
                                     (App (App (Op Fop) (Op Fop))
                                        (App (App (Op Sop) (App (Op Fop) (Op Fop)))
                                           (App (Op Fop) (Op Fop))))))))))
                   (App (App (Op Fop) (Op Fop)) (App (Op Fop) (Op Fop)))))))
       (App (App (Op Fop) (Op Fop))
          (App (App (Op Fop) (Op Fop))
               (App (App (Op Sop) (App (Op Fop) (Op Fop))) (App (Op Fop) (Op Fop)))))). 


Lemma omega2_val: omega2 = star_opt(star_opt (App (Ref 0) (app_comb (app_comb (Ref 1) (Ref 1)) (Ref 0)))).
Proof. unfold omega2, star_opt; unfold_op; unfold subst; simpl; auto. Qed.

  
Definition Y2 f := app_comb (app_comb omega2 omega2) f.

Lemma Y2_program: forall f, program f -> program (Y2 f).
Proof.
  unfold Y2, omega2; split_all; unfold program; split; 
unfold subst, subst_rec; fold subst_rec; nf_out; try eapply2 H. 
unfold subst, subst_rec; fold subst_rec; nf_out; try eapply2 H. 
unfold maxvar; fold maxvar. simpl. rewrite max_zero; eapply2 H. 
Qed.

Lemma omega2_omega2 : 
forall f, sf_red (App (App omega2 omega2) f) (App f (Y2 f)).
Proof.
  intros; unfold omega2 at 1; unfold_op.
  do 5 eval_tac.  eapply2 preserves_app_sf_red.  
  all:  unfold Y2; unfold_op;   repeat  eval_tac.
Qed.

Lemma Y2_fix: forall M N, 
sf_red (App (Y2 M) N) (App (App M (Y2 M)) N).
Proof.
unfold Y2 at 1.  intros. 
eapply transitive_red. eapply2 app_comb_red. 
eapply transitive_red. eapply preserves_app_sf_red. eapply2 app_comb_red. auto. 
eapply transitive_red. eapply preserves_app_sf_red. eapply2 omega2_omega2. all:auto. 
Qed. 

(* Y3 *)


Definition app_comb_eta f :=
  App
    (App (Op Sop)
       (App (App (Op Sop) (App (App (Op Fop) (Op Fop)) (Op Sop)))
          (App
             (App (Op Sop) (App (App (Op Fop) (Op Fop)) (App (Op Sop) (App (App (Op Fop) (Op Fop)) f))))
             (App (Op Fop) (Op Fop)))))
    (App (App (Op Fop) (Op Fop)) (App (App (Op Sop) (App (Op Fop) (Op Fop))) (App (Op Fop) (Op Fop)))).


Definition Y3_aux w f  := app_comb_eta (app_comb (app_comb w w) f).


Definition omega3 := 
  star_opt(star_opt (app_comb_eta (app_comb (Ref 0) (Y3_aux (Ref 1) (Ref 0))))).


Definition Y3 f := Y3_aux omega3 f.



Lemma Y3_aux_program: forall w f, program w -> program f -> program (Y3_aux w f).
Proof.
  intros; unfold Y3_aux, app_comb_eta, program; split_all; split. 
  nf_out. eapply2 H. eapply2 H. eapply2 H0.
  rewrite ! max_zero.
  assert(maxvar w = 0) by eapply2 H. rewrite ! H1. simpl. eapply2 H0. 
Qed.
  
Lemma omega3_program: program omega3. 
Proof. split; auto. unfold omega3, app_comb_eta; nf_out.  unfold Y3_aux, app_comb_eta; nf_out. Qed.


Lemma Y3_program: forall f, program f -> program (Y3 f).
Proof. intros.  unfold Y3. eapply2 Y3_aux_program. eapply2 omega3_program.  Qed.
                                                                                              
Lemma omega3_omega3 : 
forall f M N, sf_red (App (App (App (App omega3 omega3) f) M) N) (App (App (App f (Y3 f)) M) N).
Proof.
  intros; cbv; do 56 eval_tac. 
  eapply2 preserves_app_sf_red. eapply2 preserves_app_sf_red.
  eapply2 preserves_app_sf_red. 
  all: repeat eval_tac.
Qed.


Lemma Y3_fix: forall M N P, 
sf_red (App (App (Y3 M) N) P) (App (App (App M (Y3 M)) N) P).
Proof.
  unfold Y3, Y3_aux, omega3, app_comb_eta; intros; cbv.
  do 73 eval_tac.
  eapply2 preserves_app_sf_red. eapply2 preserves_app_sf_red.
  eapply2 preserves_app_sf_red. all: repeat eval_tac.
Qed. 



Definition omega_k k := 
star_opt(star_opt (App (Ref 0) (app_comb (app_comb (app_comb (A_k (S k)) (Ref 1)) (Ref 1)) 
                                    (Ref 0)))).

Definition Y_k k := app_comb (app_comb (A_k (S k)) (omega_k k)) (omega_k k). 

Lemma omega_k_normal: forall k, normal (omega_k k).
Proof.  
intros; unfold omega_k. repeat eapply2 star_opt_normal.
eapply2 nf_active.  repeat eapply2 app_comb_normal. 
Qed. 


Hint Resolve A_k_closed A_k_normal omega_k_normal. 



Lemma omega_omega : 
forall k M, sf_red (App (App (omega_k k) (omega_k k)) M) (App M (app_comb (Y_k k) M)).
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

Lemma Y_k_program: forall k, program (Y_k k).
Proof.
  unfold Y_k; split_all; unfold program; split; nf_out.   
  (* 2 *) 
  case k; intros.  nf_out. 
unfold_op; unfold subst, subst_rec; fold subst_rec; case n; intros; nf_out. 
  (* 1 *)
  rewrite ! maxvar_app. rewrite ! maxvar_op. unfold max; fold max. 
unfold omega_k. rewrite ! maxvar_star_opt.
  rewrite ! maxvar_app. rewrite ! maxvar_app_comb. 
  rewrite ! A_k_closed.  unfold maxvar; fold maxvar; unfold max; fold max. 
unfold pred; rewrite ! max_zero. 
case k; split_all. case n; split_all. rewrite max_zero. 
induction n0; split_all. rewrite max_zero; auto. 
Qed.

Lemma Y_k_normal: forall k, normal (Y_k k). Proof. eapply2 Y_k_program. Qed. 
Lemma Y_k_closed: forall k, maxvar (Y_k k) = 0. Proof. eapply2 Y_k_program. Qed. 




Lemma Y4_fix: forall M N P Q, 
sf_red (App (App (App (App (Y_k 4) M) N) P) Q) (App (App (App (App M (app_comb (Y_k 4) M)) N) P) Q).
Proof.
unfold Y_k at 1; unfold_op; intros; cbv.  
do 112 eval_tac.
  eapply2 preserves_app_sf_red. eapply2 preserves_app_sf_red. 
  eapply2 preserves_app_sf_red.  eapply2 preserves_app_sf_red.
  all: repeat eval_tac.
Qed. 
