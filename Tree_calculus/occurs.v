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
(*                      occurs.v                                      *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)


Require Import Omega Max Bool List.
Require Import IntensionalLib.SF_calculus.Test.  
Require Import IntensionalLib.SF_calculus.General.  
Require Import IntensionalLib.Tree_calculus.Abstraction_Terms.  
Require Import IntensionalLib.Tree_calculus.Abstraction_Reduction.  
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


Lemma occurs_subst : forall M k, occurs k (subst_rec M (Op Node) 0) = occurs (S k) M.
Proof. 
induction M; intros. 
case n; intros;  simpl; auto.
cbv; auto.
simpl. rewrite IHM1. rewrite IHM2. auto. 
Qed. 



Lemma occurs_star_opt : forall M k, occurs k (star_opt M) = occurs (S k) M. 
Proof.
induction M; intros; unfold star_opt; fold star_opt. 
(* 3 *) 
case n; intros; unfold_op; simpl; auto.
(* 2 *) 
cbv; auto. 
(* 1 *) 
case (occurs 0 M1).
all: cycle 1. 
intro.
simpl. rewrite IHM1. rewrite IHM2. omega.
(* 1 *) 
gen_case IHM2 M2.
(* 3 *) 
gen_case IHM2 n; unfold subst; rewrite occurs_subst; omega.
rewrite occurs_subst; omega.
(* 1 *)
gen_case IHM2 (occurs 0 t).
gen_case IHM2 (occurs 0 t0).
rewrite ! occurs_subst. auto. 
rewrite IHM2. rewrite IHM1. omega. 
rewrite IHM2. rewrite IHM1. omega. 
Qed.


Lemma occurs_lift: forall M k n, occurs (k +n) (lift n M) = occurs k M. 
Proof. 
induction M; intros; unfold lift; simpl. 2: auto. 
relocate_lt. replace (k+n0) with (n0+k) by omega.
generalize k; clear k. induction n0; intros.
simpl; auto. 
replace (S n0 + n) with (S(n0 + n)) by omega. 
replace (S n0 + k) with (S(n0+ k)) by omega. 
unfold eqnat; fold eqnat.
eapply2 IHn0.
unfold lift in *. 
rewrite IHM1. rewrite IHM2. auto.   
Qed.   


Lemma occurs_case : 
forall P M k, occurs k (case P M) = occurs (k+ pattern_size P) M.
Proof.  
induction P; intros; unfold case; fold case. 
rewrite occurs_star_opt. simpl. 
replace (k+1) with (S k) by omega. auto. 
rewrite occurs_star_opt. 
unfold swap, pattern_size; unfold_op; rewrite ! occurs_app. 
rewrite ! occurs_op. 
rewrite occurs_closed. 
2: eapply2 Fop_closed. 
unfold occurs at 1. unfold eqnat.
unfold occurs; fold occurs. unfold eqnat. 
replace (k+0) with k by omega.
replace (S k) with (k+1) by omega. rewrite occurs_lift.
omega. 
(* 1 *) 
assert(is_program (App P1 P2) = true \/ is_program (App P1 P2) <> true) by decide equality.
inversion H. rewrite H0.  
rewrite occurs_star_opt. 
unfold swap. unfold_op. 
rewrite ! occurs_app. 
rewrite occurs_closed. 
2: eapply2 equal_comb_closed. 
simpl.
assert (program (App P1 P2)) by eapply2 program_is_program. 
inversion H1. simpl in H3; max_out. 
rewrite occurs_closed. 2: auto. 
rewrite occurs_closed. 2: auto. 
rewrite ! pattern_size_closed. 
replace (k+ (0+0)) with k by omega. 
all: auto. 
simpl; auto. 
replace (S k) with (k+1) by omega. 
rewrite occurs_lift. omega. 
(* 1 *) 
assert(is_program (App P1 P2) = false). 
gen_case H0 (is_program (App P1 P2)). congruence. 
rewrite H1. 
unfold case_app. 
rewrite occurs_star_opt. 
rewrite ! occurs_app. 
rewrite occurs_closed. 
2: eapply2 Fop_closed. 
replace (S k) with (k+1) by omega.
unfold occurs; fold occurs. 
unfold eqnat. replace (k+1) with (S k) at 1 by omega.
replace (S k) with (k+1) by omega. rewrite occurs_lift.
rewrite ! occurs_star_opt.
rewrite occurs_closed. 2: cbv; auto. 
rewrite ! occurs_app.
replace (S (S k)) with (k+2) by omega.
rewrite ! occurs_lift.
rewrite IHP1. rewrite IHP2. 
unfold_op; simpl. replace (k+2) with (S (S k)) by omega.
replace (k+1) with (S k) by omega.
replace (k+ (pattern_size P1 + pattern_size P2)) with 
(k + (pattern_size P1) + (pattern_size P2)) by omega. 
omega.
Qed. 
  
 


Lemma occurs_false_1 : forall M, occurs 0 M = 0 -> maxvar M <= 1 -> maxvar M = 0.
Proof.
induction M; intros. 
gen2_case H H0 n. omega. 
auto.  
simpl in *. 
rewrite IHM1. rewrite IHM2. auto.
omega.
assert(max (maxvar M1) (maxvar M2) >= maxvar M2) by eapply2 max_is_max.
omega.
omega.
assert(max (maxvar M1) (maxvar M2) >= maxvar M1) by eapply2 max_is_max.
omega. 
Qed. 


Lemma occurs_extension : 
forall k P M N, occurs k (extension P M N) = occurs k N + occurs (k+ pattern_size P) M.
Proof.
intros; unfold extension.  unfold_op. 
rewrite ! occurs_app. rewrite ! occurs_op. simpl.
rewrite occurs_case. auto. 
Qed. 
    


Lemma star_mono2: forall M N, M <> N -> star M <> star N.
Proof. intros. intro. assert(M = N) by eapply2 star_mono. eapply2 H. Qed. 


Lemma app_comb_mono2: forall M1 M2 N1 N2, M1 <> N1 -> app_comb M1 M2 <> app_comb N1 N2.
Proof. intros. intro. inversion H0. eapply2 H. Qed. 



Lemma app_comb_vs_I : forall M N, matchfail (app_comb M N) i_op. 
Proof. intros. unfold_op. eapply2 matchfail_compound_l. Qed. 

(* restore as needed 

Lemma star_opt_app_comb1:
  forall M N, maxvar M = 0 -> occurs 0 N >0 -> 
              star_opt (app_comb M  N) =
              App
    (App (Op Node)
       (App (Op Node)
          (App (App (Op Node) (App (Op Node) (App k_op (App k_op M))))
             (App
                (App (Op Node)
                   (App (Op Node)
                      (App (App (Op Node) (App (Op Node) (star_opt (App k_op N))))
                         (App k_op (Op Node))))) (App k_op (Op Node))))))
    (App k_op (App (Op Node) (App (Op Node) i_op))).
Proof.
  intros.
  unfold app_comb. 
  rewrite star_opt_occurs_true. 
  2: simpl; rewrite H0; auto. 2: congruence. 
  rewrite star_opt_occurs_true. 
  2: simpl; rewrite H0; auto. 2: congruence. 
  rewrite star_opt_closed. 
  2: cbv; auto.
  rewrite star_opt_occurs_true. 
  2: simpl; rewrite H0; auto. 2: congruence. 
  rewrite star_opt_occurs_true. 
  2: simpl; rewrite H0; auto. 2: congruence. 
  rewrite (star_opt_closed  (App (Op Node) (App (Op Node) i_op))).
  2: cbv; auto.
  rewrite ! (star_opt_closed (Op Node)).
  2: cbv; auto. auto. 
Qed.



Lemma subst_star_opt:
  forall M N1 N2,  occurs 1 M = true -> subst(star_opt M) N1 = subst(star_opt M) N2 -> N1 = N2. 
Proof.
  induction M; split_all.
  gen2_case H H0 n.   discriminate.
  gen2_case H H0 n0. 
  unfold subst in *; simpl in *. inversion H0. generalize H2; insert_Ref_out; auto.
  unfold lift; rewrite ! lift_rec_null; auto.
  discriminate.
  (* 1 *)
gen2_case IHM1 H (occurs 1 M1). 
gen2_case IHM1 H (occurs 1 M1). 

  unfold eqnat in *. 
  
Lemma size_subst_star_opt : forall M N,  size (subst (star_opt M) N) = size M + size N.
Proof.
  intros. unfold subst; rewrite subst_rec_preserves_star_opt. 
  induction M; intros; auto. 
case n; intros; simpl; auto. 



  Lemma A_k_size :
  forall k, size (A_k (S (S (S k)))) =
            size (star_opt (star_opt (app_comb (Ref 2) (app_comb (Ref 1) (Ref 0))))) +
            size (A_k (S (S k)))
.
Proof.
  intros. rewrite <- A_k_alt at 1. 


       cbv. 

  
  forall k, A_k (S (S (S k))) = k_op.
Proof.
  intros. rewrite <- A_k_alt.
  unfold app_comb; unfold_op.
  unfold star_opt at 2. unfold_op; unfold occurs; fold occurs.
  rewrite ! orb_false_l. unfold eqnat; fold eqnat.
  rewrite ! orb_true_l.
  unfold subst; rewrite ! subst_rec_preserves_star_opt. subst_tac. subst_tac. 

  simpl. 
  ; fold star_opt. unfold_op. 


Lemma size_A_k : forall k,  size (A_k (S(S(S k)))) = size (A_k (S(S k))) + 142.
Proof.
  intros. unfold A_k; fold A_k. case k.
  (* 2 *)
  cbv; auto. intro. case n. cbv. auto. intro. unfold plus. intro.

 


Lemma  A_k_vs_A_k_3: forall k n, A_k (S (S (S k))) <> A_k (S (S (S (S k)) +n)). 
Proof. 
induction k; intros. 
(* 2 *) 
unfold A_k; fold A_k. unfold plus.
rewrite ! star_opt_app_comb.
2: apply A_k_closed.
2: cbv; auto. 2: cbv; auto. 2: cbv; auto.
rewrite ! (star_opt_occurs_true k_op).
2: cbv; auto. 2: discriminate.

rewrite ! star_opt_app_comb.
2: cbv; auto. 2: cbv; auto. 2: cbv; auto.


2: cbv; auto. 2: cbv; auto.




intro. inversion H; subst. 
assert(

unfold app_comb at 1. 
rewrite star_opt_occurs_true. 
rewrite (star_opt_occurs_true (App (Op Node) (App (Op Node) (App k_op (app_comb (Ref 1) (Ref 0)))))).
2: cbv; auto.  2: congruence. 
2: cbv; auto. 2: congruence.
rewrite star_opt_occurs_true. 
2: cbv; auto.  2: simpl; congruence.
rewrite (star_opt_closed (App (Op Node) (App (Op Node) i_op))).
2: cbv; auto.
rewrite (star_opt_closed (App k_op (App (Op Node) (App (Op Node) i_op)))).
2: cbv; auto.
rewrite star_opt_occurs_true. 
2: cbv; auto. 
2: congruence.
rewrite (star_opt_closed (App k_op a_op)). 
2: cbv; auto.
rewrite star_opt_closed.
unfold app_comb at 1.


unfold star_opt at 1.
2: cbv; auto. 
unfold_op. 

unfold app_comb at 2.





at 2. 
unfold star_opt at 1 2. 



repeat eapply2 star_mono2.
eapply2 app_comb_mono2.
Qed. 

Lemma A_k_vs_A_k : forall k n, A_k (S k) <> A_k (S (S (k+n))). 
Proof.
induction k; intros. 
unfold plus, A_k; fold A_k. 
case n; intros. discriminate. 
unfold app_comb at 1; unfold star; fold star. discriminate . 
clear; case k; intros. 
unfold plus, A_k; fold A_k. 
unfold app_comb, star; fold star. discriminate . 
eapply A_k_vs_A_k_3. 
Qed. 
 
  


Lemma omega_k_vs_omega_k_aux: 
forall M N,  maxvar M = 0 -> maxvar N = 0 -> M <> N -> 
star_opt
  (star_opt
     (App (Ref 0)
        (app_comb (app_comb (app_comb M (Ref 1)) (Ref 1)) (Ref 0)))) <>
star_opt
  (star_opt
     (App (Ref 0)
        (app_comb (app_comb (app_comb N (Ref 1)) (Ref 1))
           (Ref 0)))).
Proof. 
intros. 
rewrite star_opt_occurs_true. 
2: simpl; auto. 2: discriminate.
unfold  app_comb at 1. 
rewrite (star_opt_occurs_true (App (Op Node) (App (Op Node) i_op))). 
2: simpl; auto. 2: discriminate. 
rewrite (star_opt_occurs_true (App (Op Node) (App (Op Node) (App k_op (Ref 0))))). 
2: simpl; auto. 2: discriminate. 
rewrite (star_opt_occurs_false (App k_op _)). 
all: cycle 1. 
unfold app_comb. 
rewrite ! occurs_app.
simpl; auto. rewrite occurs_closed; auto. 
(* 1 *) 
rewrite (star_opt_occurs_true). 
2: simpl; auto. 2: discriminate.
match goal with 
| |- ?M <> ?N => 
assert(N <> M)
end. 
all: cycle 1. 
intro. apply H2. apply  (eq_sym H3).
(* 1 *) 
rewrite star_opt_occurs_true. 
2: simpl; auto. 2: discriminate.
unfold  app_comb at 1. 
rewrite (star_opt_occurs_true (App (Op Node) (App (Op Node) i_op))). 
2: simpl; auto. 2: discriminate. 
rewrite (star_opt_occurs_true (App (Op Node) (App (Op Node) (App k_op (Ref 0))))). 
2: simpl; auto. 2: discriminate. 
rewrite (star_opt_occurs_false (App k_op _)) at 1.
all: cycle 1.
unfold app_comb. rewrite ! occurs_app.
simpl. rewrite occurs_closed; auto.  
rewrite subst_rec_app.
rewrite ! subst_rec_preserves_app_comb.
rewrite (subst_rec_closed k_op). 
2: cbv; auto.  
rewrite ! subst_rec_ref. insert_Ref_out.
rewrite subst_rec_closed. 2: rewrite H0; auto.  
rewrite (star_opt_occurs_true). 
2: simpl; auto. 2: discriminate.
(* 1 *) 
match goal with 
| |- App (App (Op Node) (App (Op Node) (star_opt (star_opt (Ref 0))))) ?M <> 
App (App (Op Node) (App (Op Node) (star_opt (star_opt (Ref 0))))) ?N => 
assert(M<>N)
end. 
all: cycle 1.
congruence . 
(* 1 *) 
rewrite star_opt_occurs_true. 
2: simpl; auto.  2: congruence. 
rewrite star_opt_occurs_true. 
2: simpl; auto.  2: congruence. 
rewrite star_opt_occurs_true. 
2: simpl; auto.  2: cbv; congruence.
unfold star_opt at 2. unfold occurs. 
unfold_op. rewrite ! orb_false_l.   
match goal with 
| |- ?M <> ?N => 
assert(N <> M)
end. 
all: cycle 1. 
intro. apply H2. apply  (eq_sym H3).
(* 1 *) 
rewrite star_opt_occurs_true. 
2: simpl; auto.  2: congruence. 
rewrite star_opt_occurs_true. 
2: simpl; auto.  2: congruence. 
rewrite star_opt_occurs_true. 
2: simpl; auto.  2: cbv; congruence.
unfold star_opt at 2. unfold occurs. 
unfold_op. rewrite ! orb_false_l.   
match goal with 
| |- App ?M1 ?M <> App ?N1 ?M =>  assert(M1 <> N1) end. 
2: congruence.
match goal with 
| |- App ?M1 ?M2 <> App ?N1 ?N2 =>  assert(M2 <> N2) end. 
2: congruence.
match goal with 
| |- App ?M1 ?M2 <> App ?N1 ?N2 =>  assert(M2 <> N2) end. 
2: congruence.
match goal with 
| |- App ?M1 ?M2 <> App ?N1 ?N2 =>  assert(M1 <> N1) end. 
2: congruence.
match goal with 
| |- App ?M1 ?M2 <> App ?N1 ?N2 =>  assert(M2 <> N2) end. 
2: congruence.
match goal with 
| |- App ?M1 ?M2 <> App ?N1 ?N2 =>  assert(M2 <> N2) end. 
2: congruence.
match goal with 
| |- App ?M1 ?M2 <> App ?N1 ?N2 =>  assert(M2 <> N2) end. 
2: congruence.
(* 1 *) 
rewrite star_opt_occurs_true. 
2: cbv; auto.  2: congruence. 
match goal with 
| |- ?M <> ?N => 
assert(N <> M)
end. 
all: cycle 1. 
intro. apply H2. apply  (eq_sym H3).
(* 1 *) 
rewrite star_opt_occurs_true. 
2: cbv; auto.  2: congruence. 
match goal with 
| |- App ?M1 ?M2 <> App ?N1 ?N2 =>  assert(M1 <> N1) end. 
2: congruence.
match goal with 
| |- App ?M1 ?M2 <> App ?N1 ?N2 =>  assert(M2 <> N2) end. 
2: congruence.
match goal with 
| |- App ?M1 ?M2 <> App ?N1 ?N2 =>  assert(M2 <> N2) end. 
2: congruence.
(* 1 *) 
rewrite star_opt_occurs_true. 
2: cbv; auto.  2: congruence. 
match goal with 
| |- ?M <> ?N => 
assert(N <> M)
end. 
all: cycle 1. 
intro. apply H2. apply  (eq_sym H3).
(* 1 *) 
rewrite star_opt_occurs_true. 
2: cbv; auto.  2: congruence. 
match goal with 
| |- App ?M1 ?M2 <> App ?N1 ?N2 =>  assert(M1 <> N1) end. 
2: congruence.
match goal with 
| |- App ?M1 ?M2 <> App ?N1 ?N2 =>  assert(M2 <> N2) end. 
2: congruence.
match goal with 
| |- App ?M1 ?M2 <> App ?N1 ?N2 =>  assert(M2 <> N2) end. 
2: congruence.
(* 1 *) 
rewrite star_opt_occurs_true. 
2: cbv; auto.  2: cbv; congruence. 
match goal with 
| |- ?M <> ?N => 
assert(N <> M)
end. 
all: cycle 1. 
intro. apply H2. apply  (eq_sym H3).
rewrite star_opt_occurs_true. 
2: cbv; auto.  2: cbv; congruence. 
match goal with 
| |- App ?M1 ?M2 <> App ?N1 ?N2 =>  assert(M2 <> N2) end. 
2: congruence.
(* 1 *) 
rewrite star_opt_occurs_true. 
2: cbv; auto.  2: congruence. 
match goal with 
| |- ?M <> ?N => 
assert(N <> M)
end. 
all: cycle 1. 
intro. apply H2. apply  (eq_sym H3).
rewrite star_opt_occurs_true. 
2: cbv; auto.  2: congruence. 
match goal with 
| |- App ?M1 ?M2 <> App ?N1 ?N2 =>  assert(M1 <> N1) end. 
2: congruence.
match goal with 
| |- App ?M1 ?M2 <> App ?N1 ?N2 =>  assert(M2 <> N2) end. 
2: congruence.
match goal with 
| |- App ?M1 ?M2 <> App ?N1 ?N2 =>  assert(M2 <> N2) end. 
2: congruence.
(* 1 *) 
rewrite star_opt_occurs_true. 
2: cbv; auto.  2: congruence. 
match goal with 
| |- ?M <> ?N => 
assert(N <> M)
end. 
all: cycle 1. 
intro. apply H2. apply  (eq_sym H3).
rewrite star_opt_occurs_true. 
2: cbv; auto.  2: congruence. 
match goal with 
| |- App ?M1 ?M2 <> App ?N1 ?N2 =>  assert(M1 <> N1) end. 
2: congruence.
match goal with 
| |- App ?M1 ?M2 <> App ?N1 ?N2 =>  assert(M2 <> N2) end. 
2: congruence.
match goal with 
| |- App ?M1 ?M2 <> App ?N1 ?N2 =>  assert(M2 <> N2) end. 
2: congruence.
(* 1 *) 
rewrite star_opt_occurs_true. 
2: cbv; auto.  2: congruence. 
match goal with 
| |- ?M <> ?N => 
assert(N <> M)
end. 
all: cycle 1. 
intro. apply H2. apply  (eq_sym H3).
rewrite star_opt_occurs_true. 
2: cbv; auto.  
all: cycle 1. 
unfold subst_rec; congruence. 
match goal with 
| |- App ?M1 ?M2 <> App ?N1 ?N2 =>  assert(M1 <> N1) end. 
2: congruence.
match goal with 
| |- App ?M1 ?M2 <> App ?N1 ?N2 =>  assert(M2 <> N2) end. 
2: congruence.
match goal with 
| |- App ?M1 ?M2 <> App ?N1 ?N2 =>  assert(M2 <> N2) end. 
2: congruence.
(* 1 *) 
unfold subst_rec; fold subst_rec.
rewrite subst_rec_closed. 
2: rewrite H; auto. 
insert_Ref_out.  
rewrite star_opt_occurs_true. 
2: cbv; auto.  2: congruence. 
match goal with 
| |- ?M <> ?N => 
assert(N <> M)
end. 
all: cycle 1. 
intro. apply H2. apply  (eq_sym H3).
rewrite star_opt_occurs_true. 
2: cbv; auto.  2: congruence. 
match goal with 
| |- App ?M1 ?M2 <> App ?N1 ?N2 =>  assert(M1 <> N1) end. 
2: congruence.
match goal with 
| |- App ?M1 ?M2 <> App ?N1 ?N2 =>  assert(M2 <> N2) end. 
2: congruence.
match goal with 
| |- App ?M1 ?M2 <> App ?N1 ?N2 =>  assert(M2 <> N2) end. 
2: congruence.
(* 1 *) 
rewrite star_opt_occurs_true. 
2: cbv; auto.  2: congruence. 
match goal with 
| |- ?M <> ?N => 
assert(N <> M)
end. 
all: cycle 1. 
intro. apply H2. apply  (eq_sym H3).
rewrite star_opt_occurs_true. 
2: cbv; auto.  2: congruence. 
match goal with 
| |- App ?M1 ?M2 <> App ?N1 ?N2 =>  assert(M1 <> N1) end. 
2: congruence.
match goal with 
| |- App ?M1 ?M2 <> App ?N1 ?N2 =>  assert(M2 <> N2) end. 
2: congruence.
match goal with 
| |- App ?M1 ?M2 <> App ?N1 ?N2 =>  assert(M2 <> N2) end. 
2: congruence.
(* 1 *) 
rewrite star_opt_occurs_true. 
2: cbv; auto.  2: congruence. 
match goal with 
| |- ?M <> ?N => 
assert(N <> M)
end. 
all: cycle 1. 
intro. apply H2. apply  (eq_sym H3).
rewrite star_opt_occurs_true. 
2: cbv; auto.  2: congruence. 
match goal with 
| |- App ?M1 ?M2 <> App ?N1 ?N2 =>  assert(M1 <> N1) end. 
2: congruence.
match goal with 
| |- App ?M1 ?M2 <> App ?N1 ?N2 =>  assert(M2 <> N2) end. 
2: congruence.
match goal with 
| |- App ?M1 ?M2 <> App ?N1 ?N2 =>  assert(M2 <> N2) end. 
2: congruence.
(* 1 *) 
rewrite star_opt_occurs_true. 
2: cbv; auto.  2: congruence. 
match goal with 
| |- ?M <> ?N => 
assert(N <> M)
end. 
all: cycle 1. 
intro. apply H2. apply  (eq_sym H3).
rewrite star_opt_occurs_true. 
2: cbv; auto.  2: congruence. 
match goal with 
| |- App ?M1 ?M2 <> App ?N1 ?N2 =>  assert(M1 <> N1) end. 
2: congruence.
match goal with 
| |- App ?M1 ?M2 <> App ?N1 ?N2 =>  assert(M2 <> N2) end. 
2: congruence.
match goal with 
| |- App ?M1 ?M2 <> App ?N1 ?N2 =>  assert(M2 <> N2) end. 
2: congruence.
(* 1 *) 
rewrite star_opt_occurs_true. 
2: cbv; auto.  2: congruence. 
match goal with 
| |- ?M <> ?N => 
assert(N <> M)
end. 
all: cycle 1. 
intro. apply H2. apply  (eq_sym H3).
rewrite star_opt_occurs_true. 
2: cbv; auto.  2: congruence. 
match goal with 
| |- App ?M1 ?M2 <> App ?N1 ?N2 =>  assert(M1 <> N1) end. 
2: congruence.
match goal with 
| |- App ?M1 ?M2 <> App ?N1 ?N2 =>  assert(M2 <> N2) end. 
2: congruence.
match goal with 
| |- App ?M1 ?M2 <> App ?N1 ?N2 =>  assert(M2 <> N2) end. 
2: congruence.
(* 1 *) 
rewrite star_opt_occurs_true. 
2: cbv; auto.  2: congruence. 
match goal with 
| |- ?M <> ?N => 
assert(N <> M)
end. 
all: cycle 1. 
intro. apply H2. apply  (eq_sym H3).
rewrite star_opt_occurs_true. 
2: cbv; auto.  2: congruence. 
match goal with 
| |- App ?M1 ?M2 <> App ?N1 ?N2 =>  assert(M1 <> N1) end. 
2: congruence.
match goal with 
| |- App ?M1 ?M2 <> App ?N1 ?N2 =>  assert(M2 <> N2) end. 
2: congruence.
match goal with 
| |- App ?M1 ?M2 <> App ?N1 ?N2 =>  assert(M2 <> N2) end. 
2: congruence.
rewrite ! star_opt_closed.
2: rewrite ! maxvar_app. 2: rewrite H0. 2: auto. 
2: rewrite ! maxvar_app. 2: rewrite H. 2: auto. 
match goal with 
| |- App ?M1 ?M2 <> App ?N1 ?N2 =>  assert(M2 <> N2) end. 
2: congruence.
match goal with 
| |- App ?M1 ?M2 <> App ?N1 ?N2 =>  assert(M2 <> N2) end. 
2: congruence.
(* 1 *) 
auto. 
Qed. 
 

Lemma omega_k_vs_omega_k : forall k n, omega_k k <> omega_k (S (k+n)).
Proof.
induction k; intros. 
(* 2 *)
unfold plus, omega_k; fold omega_k.
eapply2 omega_k_vs_omega_k_aux.  
replace n with (0+n) by auto. 
eapply2 A_k_vs_A_k. 
(* 1 *) 
unfold omega_k; fold omega_k. 
eapply2 omega_k_vs_omega_k_aux. eapply2 A_k_vs_A_k.
Qed. 
 
*) 

