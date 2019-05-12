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

Lemma eqnat_equal: forall n k,  eqnat n k >0 -> n = k.
Proof. induction n; split_all; gen_case H k;   omega. Qed.

Lemma occurs_implies_mono:
  forall k M, occurs k M >0 -> forall N1 N2,  subst_rec M N1 k = subst_rec M N2 k -> N1 = N2.
Proof.
  induction M; split_all.
  assert(n=k) by eapply2 eqnat_equal. subst. 
  generalize H0; clear H0; insert_Ref_out.
  unfold lift. generalize N1 N2; clear; induction N1; split_all.
  gen_case H0 N2. 
  assert(n = n0) by (inversion H0; subst; eapply relocate_mono; eauto).
  congruence.
  all: try discriminate.
  gen_case H0 N2. 
  all: try discriminate.
  gen_case H0 N2;  try discriminate.
inversion H0; subst. rewrite (IHN1_1 t); auto. rewrite (IHN1_2 t0); auto. 
omega. 
inversion H0.
assert(occurs k M1 >0 \/ occurs k M2 >0) by omega. 
inversion H1. eapply2 IHM1. eapply2 IHM2. 
Qed.

Lemma occurs_subst: forall M k, occurs k (subst_rec M (Op Node) 0) = occurs (S k) M.
Proof. induction M; split_all; subst_tac. case n; split_all.  Qed. 


Lemma star_opt_mono:
  forall M, occurs 1 M >0 -> forall N1 N2,  subst (star_opt M) N1 = subst (star_opt M) N2 -> N1 = N2.
Proof.
  induction M; intros. 
  gen2_case H H0 n.   omega. 
  gen2_case H H0 n0. 
  unfold subst in *; simpl in *; inversion H0. 
  generalize H2; insert_Ref_out; unfold lift; rewrite ! lift_rec_null; auto. 
  omega.
  simpl in *. omega.
  (* 1 *)
  assert(occurs 0 M1 >0 \/ occurs 0 M1 = 0) by omega.
  inversion H1. 
  unfold star_opt in H0.
  replace (occurs 0 M1) with (S (pred (occurs 0 M1))) in H0 by omega.
  fold star_opt in *.
  unfold subst in H0; simpl in H0. inversion H0. 
  simpl in H. 
  assert(occurs 1 M1 >0 \/ occurs 1 M2 >0) by omega.
  inversion H3.  eapply2 IHM1. eapply2 IHM2. 
  (* 1 *)
  assert(star_opt M1 = App k_op (subst M1 (Op Node))). 
  eapply2 star_opt_occurs_false. 
  rewrite H3 in *. 
  assert(M2 = Ref 0 \/ M2 <> Ref 0) by repeat decide equality.
  inversion H4; subst.
  assert( star_opt (App M1 (Ref 0)) = subst M1 (Op Node)).
  unfold star_opt. rewrite H2. auto. 
  rewrite H5 in *.
  unfold subst in *. eapply2 (occurs_implies_mono 0 (subst_rec M1 (Op Node) 0)). 
  simpl in H.   assert(occurs 1 M1 >0) by omega.
  generalize H6; clear. induction M1; split_all.
  assert(n = 1) by eapply2 eqnat_equal.   subst. 
  insert_Ref_out.   simpl. omega.
  assert(occurs 1 M1_1 >0 \/ occurs 1 M1_2 >0) by omega.
  inversion H.   
  assert(occurs 0 (subst_rec M1_1 (Op Node) 0) >0) . eapply2 IHM1_1.   omega.
  assert(occurs 0 (subst_rec M1_2 (Op Node) 0) >0) . eapply2 IHM1_2.   omega.
  (* 1  M2 <> Ref 0 *)
  assert(occurs 0 M2 > 0 \/ occurs 0 M2 = 0) by omega.
  inversion H6.  
  assert(star_opt (App M1 M2) = App (App (Op Node) (App (Op Node) (star_opt M2))) (star_opt M1)).
  unfold star_opt at 1.   rewrite H2. fold star_opt. 
  assert (match M2 with
  | Ref 0 => subst M1 (Op Node)
  | _ =>
      match occurs 0 M2 with
      | 0 => App k_op (subst (App M1 M2) (Op Node))
      | S _ => App (App (Op Node) (App (Op Node) (star_opt M2))) (star_opt M1)
      end
  end = match occurs 0 M2 with
      | 0 => App k_op (subst (App M1 M2) (Op Node))
      | S _ => App (App (Op Node) (App (Op Node) (star_opt M2))) (star_opt M1)
        end).
gen_case H5 M2.   
gen_case H5 n. 
congruence.       
rewrite H8. clear H8. 
replace (occurs 0 M2) with (S (pred (occurs 0 M2))) by omega.
auto.
rewrite H8 in *.
generalize H0; clear H0. subst_tac. intro H0; inversion H0; subst.
simpl in H.
assert(occurs 1 M1 >0 \/ occurs 1 M2 >0) by omega.
inversion H9. eapply2 IHM1. rewrite H3 in *. auto. eapply2 IHM2.
(* 1 *)
rewrite star_opt_occurs_false in H0. 2: simpl; omega.
eapply (occurs_implies_mono 0 (App k_op (subst_rec (App M1 M2) (Op Node) 0))).
rewrite occurs_app. replace (occurs 0 k_op) with 0 by (unfold_op; simpl; auto).
unfold plus.
rewrite occurs_subst.  auto. 
unfold subst in *. auto.
Qed.

(* Waiting revisited *)


Lemma A_k_alt :
  forall k,  subst (star_opt (star_opt (app_comb (Ref 2) (app_comb (Ref 1) (Ref 0)))))
                   (A_k (S (S k))) = A_k (S(S(S k)))
. 
Proof.
  intros; unfold A_k; fold A_k. case k. 
  unfold subst; rewrite ! subst_rec_preserves_star_opt. 
  rewrite ! subst_rec_preserves_app_comb. subst_tac.   
  unfold lift; rewrite lift_rec_closed. auto. 
  cbv; auto. 
  intro; case n. 
  unfold subst; rewrite ! subst_rec_preserves_star_opt. 
  rewrite ! subst_rec_preserves_app_comb. subst_tac.   
  unfold lift; rewrite lift_rec_closed. auto. 
  cbv; auto. 
  intro. 
  unfold subst; rewrite ! subst_rec_preserves_star_opt. 
  rewrite ! subst_rec_preserves_app_comb. subst_tac.   
  unfold lift; rewrite lift_rec_closed. auto.
  rewrite ! maxvar_star_opt. 
  rewrite maxvar_app_comb.
  rewrite ! maxvar_star_opt. 
  rewrite maxvar_app_comb.
  rewrite A_k_closed. cbv; auto. 
Qed.

Lemma A_k_mono:
  forall k1 k2,  A_k (S (S (S k1))) = A_k (S (S (S k2))) -> k1 = k2 \/ (k1 <=2 /\ k2 <= 2).
Proof.
  induction k1; induction k2;  rewrite <- ! A_k_alt.
  (* 4 *)
  auto.
  (* 3 *)
  intro. assert(A_k 2 = subst (star_opt (star_opt (app_comb (Ref 2) (app_comb (Ref 1) (Ref 0))))) (A_k (S (S k2)))). 
 eapply2 star_opt_mono.  cbv.   auto. 
 generalize H0; clear. 
 unfold A_k at 1.  case k2. auto. 
 intro . unfold a_op.
 unfold app_comb, star_opt, occurs, eqnat. fold star_opt. 


 
      unfold A_k; intros.
  generalize H; clear H; case k1. case k2. auto. intro n. 
  case n. 
  (* 3 *)
  replace (star_opt
    (star_opt
       (app_comb (star_opt (star_opt (app_comb a_op (app_comb (Ref 1) (Ref 0)))))
                 (app_comb (Ref 1) (Ref 0)))))
    with (subst (star_opt
    (star_opt
       (app_comb (Ref 2)
                 (app_comb (Ref 1) (Ref 0)))))
                (star_opt (star_opt (app_comb a_op (app_comb (Ref 1) (Ref 0)))))).
  replace (star_opt (star_opt (app_comb a_op (app_comb (Ref 1) (Ref 0))))) with
      (subst (star_opt (star_opt (app_comb (Ref 2) (app_comb (Ref 1) (Ref 0))))) a_op).
  intro.
  assert(a_op=   (subst (star_opt (star_opt (app_comb (Ref 2) (app_comb (Ref 1) (Ref 0))))) a_op)).
  eapply star_opt_mono.
  2: eexact H.   cbv; auto.
  generalize H0; clear.
  unfold a_op.
  unfold app_comb, star_opt, occurs, eqnat; unfold_op.
  unfold subst; rewrite ! subst_rec_app. rewrite ! subst_rec_op. rewrite ! subst_rec_ref. 
  insert_Ref_out. unfold pred, plus; fold plus. subst_tac.   subst_tac.
  intro. discriminate. 
  unfold subst. rewrite ! subst_rec_preserves_star_opt.
  rewrite ! subst_rec_preserves_app_comb.
  subst_tac. 
  unfold lift; rewrite lift_rec_closed. 2: cbv; auto. auto. 
  unfold subst. rewrite ! subst_rec_preserves_star_opt.
  rewrite ! subst_rec_preserves_app_comb.
  subst_tac. 
  unfold lift; rewrite lift_rec_closed. 2: cbv; auto. auto. 
  (* 2 *)
  intro; case n0. 
  


  unfold app_comb; unfold_op.   unfold star_opt at 2; unfold occurs; unfold_op.
  unfold plus. fold plus. unfold eqnat. unfold plus.
  unfold subst; rewrite ! subst_rec_app. rewrite ! subst_rec_op. rewrite ! subst_rec_ref. 
  insert_Ref_out. unfold pred. 
  
  subst_tac.

  rewrite star_opt_occurs_true. 2: cbv; auto. 2: discriminate. star_opt, occurs in H0. fold star_opt in H0.
  gen_case H k1. 

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



Lemma omega_k_closed: forall k, maxvar(omega_k k) = 0. 
Proof. 
induction k; intros. 
cbv; auto.
unfold omega_k; fold omega_k. 
rewrite ! maxvar_star_opt. 
rewrite maxvar_app. 
rewrite ! maxvar_app_comb. 
rewrite A_k_closed.
simpl. auto.
Qed.
 

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




Lemma omega_k_alt:
  forall k,
    subst (star_opt
             (star_opt (App (Ref 0) (app_comb (app_comb (app_comb (Ref 2) (Ref 1)) (Ref 1)) (Ref 0)))))
             (A_k (S k)) =
    (omega_k k).
Proof.
  intros. unfold subst; rewrite ! subst_rec_preserves_star_opt. subst_tac.
  rewrite ! subst_rec_preserves_app_comb. repeat subst_tac.
  unfold lift; rewrite lift_rec_closed. unfold omega_k. congruence. apply A_k_closed.
Qed.


Lemma omega_3_not_omega_2: omega_k 3 <> omega_k 2. 
Proof.
  rewrite <- ! omega_k_alt. intro.
  assert(A_k 4 = A_k 3). eapply star_opt_mono.
  2: eexact H.   cbv; auto. 
  
unfold omega_k.
rewrite ! (star_opt_occurs_true (Ref 0)). 2: cbv; auto. 2: discriminate. 
2: cbv; auto. 2: discriminate.
unfold app_comb at 1 4. 
rewrite ! (star_opt_occurs_true (App (Op Node) (App (Op Node) i_op))). 
2: cbv; auto. 2: discriminate. 
2: cbv; auto. 2: discriminate.
rewrite ! (star_opt_occurs_true (App (Op Node) (App (Op Node) (App k_op (Ref 0))))). 
2: cbv; auto. 2: discriminate. 
2: cbv; auto. 2: discriminate.
rewrite ! (star_opt_occurs_false (App k_op _)). 
2: cbv; auto. 2: cbv; auto. 
rewrite ! subst_rec_app. 
rewrite ! subst_rec_preserves_app_comb. 
rewrite ! subst_rec_ref.  insert_Ref_out. unfold pred. 
rewrite ! (star_opt_occurs_true (App (Op _) _)). 
2: cbv; auto. 2: discriminate. 
2: cbv; auto. 2: discriminate.
intro H. inversion H; subst. 
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
eapply2 star_opt_beta2. auto. auto. 
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

