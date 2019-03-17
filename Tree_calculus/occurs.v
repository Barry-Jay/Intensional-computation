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


Lemma occurs_subst : forall M k, occurs k (subst M (Op Node)) = occurs (S k) M.
Proof. 
induction M; intros. 
case n; intros; unfold subst; simpl; auto.
cbv; auto.
unfold subst; simpl. rewrite IHM1. rewrite IHM2. auto. 
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
simpl. rewrite IHM1. rewrite IHM2. 
case (occurs (S k) M2); simpl; auto.
rewrite orb_true_r; auto. 
rewrite orb_false_r; auto. 
(* 1 *) 
gen_case IHM2 M2.
(* 3 *) 
gen_case IHM2 n.
rewrite orb_false_r. 
clear.
induction M1; intros. 
case n; intros; unfold subst; simpl; auto.
cbv; auto. 
unfold subst in *; simpl.
rewrite IHM1_1. rewrite IHM1_2. auto.
replace (subst_rec M1 (Op Node) 0) with (subst M1 (Op Node)) by auto. 
rewrite occurs_subst. auto. 
replace (subst_rec M1 (Op Node) 0) with (subst M1 (Op Node)) by auto. 
rewrite occurs_subst. auto. 
(* 1 *) 
gen_case IHM2 (occurs 0 t).
rewrite IHM1. rewrite IHM2. 
case (occurs (S k) t); case (occurs (S k) t0); simpl; auto. 
all: try (rewrite orb_true_r; auto).
rewrite orb_false_r; auto.
(* 1 *) 
gen_case IHM2 (occurs 0 t0).
gen_case IHM2 t0. 
(* 4 *) 
gen_case IHM2 n. 
rewrite occurs_subst.  rewrite IHM1. 
case (occurs (S k) t). simpl. rewrite orb_true_r; auto.
simpl. rewrite orb_false_r; auto.
rewrite IHM2.  rewrite IHM1. 
case (occurs (S k) t); simpl; try discriminate.  
rewrite orb_true_r. auto.
case (eqnat n0 k); simpl; auto. 
rewrite orb_true_r; auto.
rewrite orb_false_r; auto. 
(* 3 *) 
rewrite IHM1.
rewrite <- IHM2. 
case (occurs k (star_opt t)).      
simpl. rewrite orb_true_r; auto. 
simpl. rewrite orb_false_r; auto.
(* 2 *) 
gen_case IHM2 (occurs 0 t1).
 rewrite IHM1. rewrite IHM2.  
case (occurs (S k) t). simpl. rewrite orb_true_r; auto.
simpl. 
case (occurs (S k) t1); simpl; try discriminate.  
rewrite orb_true_r. auto.
case (occurs (S k) t2); simpl; try discriminate.  
rewrite orb_true_r. auto.
rewrite orb_false_r; auto. 
(* 2 *) 
gen_case IHM2 t2.
gen_case IHM2 n.
rewrite IHM1.
rewrite <- IHM2. 
case (occurs k (subst t1 (Op Node))); simpl; try discriminate.
rewrite orb_true_r; auto.
case (occurs k (star_opt t)).  
simpl. rewrite orb_true_r; auto. 
simpl; rewrite orb_false_r; auto.
rewrite IHM1. rewrite IHM2.
case (occurs (S k) t). simpl. rewrite orb_true_r; auto.
simpl. 
case (occurs (S k) t1); simpl; try discriminate.  
rewrite orb_true_r. auto.
case (eqnat n0 k); simpl; try discriminate.  
rewrite orb_true_r. auto.
rewrite orb_false_r; auto. 
rewrite IHM1. rewrite IHM2.
case (occurs (S k) t). simpl. rewrite orb_true_r; auto.
simpl. 
case (occurs (S k) t1); simpl; try discriminate.  
rewrite orb_true_r. auto.
rewrite orb_false_r. auto.
(* 2 *) 
gen_case IHM2 (occurs 0 t3).
 rewrite IHM1. rewrite IHM2.  
case (occurs (S k) t). simpl. rewrite orb_true_r; auto.
simpl. 
case (occurs (S k) t1); simpl; try discriminate.  
rewrite orb_true_r. auto.
case (occurs (S k) t3); simpl; try discriminate.  
rewrite orb_true_r. auto.
case (occurs (S k) t4); simpl; try discriminate.  
rewrite orb_true_r. auto.
rewrite orb_false_r; auto. 
(* 2 *) 
gen_case IHM2 (occurs 0 t4).
 rewrite IHM1. rewrite IHM2.  
case (occurs (S k) t). simpl. rewrite orb_true_r; auto.
simpl. 
case (occurs (S k) t1); simpl; try discriminate.  
rewrite orb_true_r. auto.
case (occurs (S k) t3); simpl; try discriminate.  
rewrite orb_true_r. auto.
case (occurs (S k) t4); simpl; try discriminate.  
rewrite orb_true_r. auto.
rewrite orb_false_r; auto. 
(* 2 *) 
rewrite IHM1.
rewrite <- IHM2. 
case (occurs k (subst_rec t1 (Op Node)0 )); simpl; try discriminate.
rewrite orb_true_r; auto.
case (occurs k (subst_rec t3 (Op Node)0 )); simpl; try discriminate.
rewrite orb_true_r; auto.
case (occurs k (subst_rec t4 (Op Node)0 )); simpl; try discriminate.
rewrite orb_true_r; auto.
case (occurs k (star_opt t)); simpl; try discriminate.
rewrite orb_true_r; auto.
rewrite orb_false_r; auto. 
(* 1 *) 
replace (subst_rec M1 (Op Node) 0) with (subst M1 (Op Node)) by auto. 
replace (subst_rec t0 (Op Node) 0) with (subst t0 (Op Node)) by auto. 
replace (subst_rec t (Op Node) 0) with (subst t (Op Node)) by auto. 
rewrite ! occurs_subst. auto. 
Qed.
 

Lemma occurs_lift: forall M k n, occurs (k +n) (lift n M) = occurs k M. 
Proof. 
induction M; intros; unfold lift; simpl.
relocate_lt. replace (k+n0) with (n0+k) by omega.
generalize k; induction n0; intros.
simpl; auto. 
replace (S n0 + k0) with (S (n0+k0)) by omega. 
simpl. auto. auto. 
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
rewrite ! orb_false_l. rewrite orb_false_r. 
replace (k+0) with k by omega. 
replace (S k) with (k+1) by omega. 
rewrite occurs_lift.  auto. 
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
rewrite orb_false_r; auto.
replace (S k) with (k+1) by omega. 
eapply2 occurs_lift. 
(* 1 *) 
assert(is_program (App P1 P2) = false). 
gen_case H0 (is_program (App P1 P2)). congruence. 
rewrite H1. 
unfold case_app. 
rewrite occurs_star_opt. 
rewrite ! occurs_app. 
rewrite occurs_closed. 
2: eapply2 Fop_closed. 
unfold_op; simpl.
replace (S k) with (k+1) by omega. 
rewrite ! occurs_lift.
rewrite occurs0_lift. simpl. 
rewrite orb_true_r. 
simpl. 
unfold lift; rewrite subst_rec_lift_rec; try omega.
replace (lift_rec
            (case P1
               (case P2
                  (App (App (Op Node) (Op Node))
                     (App (App (Op Node) (Op Node)) M)))) 0 1) with 
(lift 1
            (case P1
               (case P2
                  (App (App (Op Node) (Op Node))
                     (App (App (Op Node) (Op Node)) M))))) by auto. 
rewrite occurs0_lift.
unfold subst, lift; rewrite subst_rec_lift_rec; try omega.
rewrite ! orb_false_r. 
rewrite lift_rec_null. 
rewrite IHP1.  rewrite IHP2. 
rewrite ! occurs_app. 
rewrite ! occurs_op. simpl. 
replace (k+ (pattern_size P1 + pattern_size P2)) with 
(k + (pattern_size P1) + (pattern_size P2)) by omega. 
auto. 
Qed. 
  
 

Lemma occurs_false_1 : forall M, occurs 0 M = false -> maxvar M <= 1 -> maxvar M = 0.
Proof.
induction M; intros. 
gen2_case H H0 n.
discriminate. 
omega.
auto.  
simpl in *. 
rewrite IHM1. rewrite IHM2. auto.
gen_case H (occurs 0 M2). 
rewrite orb_true_r in *. discriminate. 
assert(max (maxvar M1) (maxvar M2) >= maxvar M2) by eapply2 max_is_max. 
omega. 
gen_case H (occurs 0 M1). 
assert(max (maxvar M1) (maxvar M2) >= maxvar M1) by eapply2 max_is_max. 
omega.
Qed. 


Lemma occurs_extension : 
forall k P M N, occurs k (extension P M N) = occurs k N || occurs (k+ pattern_size P) M.
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


Lemma  A_k_vs_A_k_3: forall k n, A_k (S (S (S k))) <> A_k (S (S (S (S k)) +n)). 
Proof. 
induction k; intros. 
(* 2 *) 
discriminate.
(* 1 *) 
unfold A_k; fold A_k.
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
 


