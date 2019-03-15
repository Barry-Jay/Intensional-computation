(**********************************************************************)
(* This Program is free sofut even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 021101301 USA                                                     *)
(**********************************************************************)

(**********************************************************************)
(*                 Abstraction_to_Tree.v                              *)
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
Require Import IntensionalLib.Tree_calculus.Abstraction.  
Require Import IntensionalLib.Tree_calculus.Abstraction2.  
Require Import IntensionalLib.Tree_calculus.Abstraction3. 



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
 



Lemma h_fn_vs_omega_k : forall k, h_fn <> omega_k k. 
Proof. 
intros. unfold omega_k. 
rewrite star_opt_occurs_true. 
2: simpl; auto.  2: discriminate.
unfold app_comb at 1.
rewrite (star_opt_occurs_true (App (Op Node) (App (Op Node) i_op))). 
2: simpl; auto.  2: discriminate.
rewrite (star_opt_occurs_true ((App (Op Node) (App (Op Node) (App k_op (Ref 0)))))). 
2: simpl; auto.  2: discriminate.
rewrite (star_opt_occurs_false (App k_op
                                   (app_comb (app_comb (A_k (S k)) (Ref 1))
                                      (Ref 1)))).
rewrite subst_rec_app. rewrite ! subst_rec_preserves_app_comb.
rewrite ! subst_rec_ref; insert_Ref_out.   
rewrite (star_opt_occurs_true).
all: cycle 1. 
unfold app_comb. rewrite ! occurs_app. unfold pred. 
replace (occurs 0 (Ref 0)) with true by auto.
rewrite ! orb_true_r. 
auto. discriminate.
unfold app_comb; unfold_op; rewrite ! occurs_app. 
rewrite (occurs_closed 0 (A_k _)). 
simpl. auto. eapply2 A_k_closed. 
discriminate.
Qed. 

Lemma star_bigger: 
forall M, maxvar M = 0 -> 
star_opt
  (star_opt
     (App (Ref 0)
        (app_comb (app_comb (app_comb M (Ref 1)) (Ref 1)) (Ref 0)))) <>
M. 
Proof. 
intros. 
rewrite star_opt_occurs_true. 
2: unfold app_comb; simpl; auto.
2: discriminate . 
unfold app_comb at 1.
 rewrite  (star_opt_occurs_true (App (Op Node) (App (Op Node) i_op))). 
2: unfold app_comb; simpl; auto.
2: discriminate . 
 rewrite  (star_opt_occurs_true (App (Op Node) (App (Op Node) (App k_op (Ref 0))))). 
2: unfold app_comb; simpl; auto.
2: discriminate .
rewrite (star_opt_occurs_false (App k_op (app_comb (app_comb M (Ref 1)) (Ref 1)))). 
2: simpl; auto. 2: eapply2 occurs_closed; auto.
rewrite subst_rec_app; rewrite ! subst_rec_preserves_app_comb.
rewrite ! subst_rec_ref; insert_Ref_out. 
rewrite ! subst_rec_closed. 2: rewrite H; auto.  2: cbv; auto. 
unfold pred. 
rewrite star_opt_occurs_true. 
2: simpl; auto. 2: discriminate. 
unfold_op; unfold star_opt at 2 1 4 5. unfold_op. 
unfold occurs. rewrite ! orb_false_l. 
unfold subst, subst_rec. 
rewrite star_opt_occurs_true.
2: unfold app_comb; simpl; auto.
2: discriminate .
rewrite star_opt_occurs_true.
2: unfold app_comb; simpl; auto.
2: discriminate .
rewrite star_opt_occurs_true.
2: unfold app_comb; simpl; auto.
2: discriminate .
rewrite star_opt_closed.
2: cbv; auto. 
rewrite star_opt_occurs_true.
2: unfold app_comb; simpl; auto.
2: discriminate .
rewrite star_opt_occurs_true.
2: unfold app_comb; simpl; auto.
2: discriminate .
rewrite star_opt_occurs_true.
2: unfold app_comb; simpl; auto.
2: discriminate .
rewrite star_opt_closed.
2: cbv; auto. 
rewrite star_opt_occurs_true.
2: unfold app_comb; simpl; auto.
2: discriminate .
rewrite star_opt_occurs_true.
2: unfold app_comb; simpl; auto.
2: discriminate .
rewrite star_opt_occurs_true.
2: unfold app_comb; simpl; auto.
2: discriminate .
rewrite star_opt_occurs_true.
2: unfold app_comb; simpl; auto.
2: discriminate .
rewrite star_opt_occurs_true.
2: unfold app_comb; simpl; auto.
2: discriminate .
rewrite star_opt_occurs_true.
2: unfold app_comb; simpl; auto.
2: discriminate .
rewrite star_opt_occurs_true.
2: unfold app_comb; simpl; auto.
2: discriminate .
rewrite star_opt_occurs_true.
2: unfold app_comb; simpl; auto.
2: discriminate .
rewrite star_opt_occurs_true.
2: unfold app_comb; simpl; auto.
2: discriminate .
rewrite star_opt_closed.
2: cbv; auto. 
intro. clear H.  
match goal with 
| H: ?M = ?N |- _ => assert(size M = size N) by congruence 
end.
clear H0.
generalize H. clear H. unfold_op; unfold star_opt, occurs, size; fold size.
rewrite ! orb_false_l. 
unfold_op; unfold subst, subst_rec, size; fold size. 
intro; omega.
Qed. 
  

Lemma b_r_op_red: forall M N, sf_red (App (App (App b_op M) N) r_op) r_op.
Proof.
intros; unfold b_op. 
eapply transitive_red. 
eapply preserves_app_sf_red.
eapply preserves_app_sf_red.
eapply2 app_comb_red. all: auto. 
eapply transitive_red.    
eapply2 Y4_fix.
unfold b_fn at 1. 
eapply transitive_red.
eapply preserves_app_sf_red. 
eapply2 star_opt_beta3. auto. 
unfold subst.
rewrite ! subst_rec_preserves_extension.
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_r.
eapply2 matchfail_program. 
eapply2 h_fn_program.
split. eapply2 omega_k_normal. eapply2 omega_k_closed. 
eapply2 h_fn_not_omega.
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
unfold A_k. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. 
unfold_op; eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r.
eapply2 matchfail_op. 
unfold factorable. right; auto. congruence. 
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
unfold r_op, Y_k. 
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
eapply2 program_matching.
split. eapply2 omega_k_normal. eapply2 omega_k_closed.
eapply2 matchfail_program. 
split. eapply2 omega_k_normal. eapply2 omega_k_closed.
split. eapply2 A_k_normal. eapply2 A_k_closed.
unfold omega_k; fold omega_k. 
apply star_bigger. eapply2 A_k_closed.  
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
unfold r_op, Y_k. 
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_r.
eapply2 matchfail_program. 
split. eapply2 omega_k_normal. eapply2 omega_k_closed.
split. eapply2 omega_k_normal. eapply2 omega_k_closed.
replace 3 with (S (2+0)) by auto. 
apply omega_k_vs_omega_k. 
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail. 
unfold r_op, Y_k. 
eapply2 matchfail_app_comb_r.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_compound_l. 
simpl. 
unfold_op; eapply2 matchfail_compound_r. 
(* 1 *) 
unfold_op; simpl. repeat eval_tac. 
Qed. 



Lemma b_h_op_red: forall M N, sf_red (App (App (App b_op M) N) h_op) h_op.
Proof.
intros; unfold b_op. 
eapply transitive_red. 
eapply preserves_app_sf_red.
eapply preserves_app_sf_red.
eapply2 app_comb_red. all: auto. 
eapply transitive_red.    
eapply2 Y4_fix.
unfold b_fn at 1. 
eapply transitive_red.
eapply preserves_app_sf_red. 
eapply2 star_opt_beta3. auto. 
unfold subst.
rewrite ! subst_rec_preserves_extension.
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_r.
eapply2 matchfail_program. 
eapply2 h_fn_program.
split. eapply2 omega_k_normal. eapply2 omega_k_closed. 
eapply2 h_fn_vs_omega_k. 
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
unfold A_k. 
eapply2 matchfail_compound_l.
simpl.  
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. 
unfold_op; eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r.
eapply2 matchfail_op. 
unfold factorable. right; auto. congruence. 
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
unfold h_op. 
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_r.
eapply2 matchfail_program.
split. eapply2 omega_k_normal. eapply2 omega_k_closed.
split. eapply2 omega_k_normal. eapply2 omega_k_closed.
replace 4 with (S (3 +0)) by auto. 
eapply2 omega_k_vs_omega_k. 
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_r.
eapply2 matchfail_program. 
split. eapply2 omega_k_normal. eapply2 omega_k_closed.
split. eapply2 omega_k_normal. eapply2 omega_k_closed.
replace 4 with (S(2+1)) by auto.
eapply2 omega_k_vs_omega_k.  
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
unfold h_op. 
eapply2 matchfail_app_comb_r.
unfold h_fn.
rewrite star_opt_eta. 
2: simpl; auto.
unfold subst, subst_rec. insert_Ref_out. unfold pred.   
rewrite star_opt_occurs_true. 
2: simpl; auto. 2: discriminate. 
rewrite star_opt_eta.  2: auto. 
rewrite star_opt_occurs_true. 
2: simpl; auto. 2: discriminate.
unfold subst, subst_rec; insert_Ref_out. unfold pred.
rewrite star_opt_occurs_true. 
2: simpl; auto. 2: discriminate. 
eapply2 matchfail_compound_l.
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
cbv.  eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
eapply2 matchfail_op.
unfold factorable. right; auto. 
discriminate. 
(* 1 *) 
unfold_op. simpl. eval_tac. eval_tac.   
Qed. 


Lemma app_comb_vs_abs_op: forall M N, 
matchfail
  (app_comb M N) abs_op.
Proof. 
intros.
unfold abs_op, ab_op, app_comb2.
unfold app_comb at 2.
rewrite star_opt_occurs_true. 
all: cycle 1. 
unfold flip, app_comb; rewrite ! occurs_app.
replace (occurs 0 (Ref 1)) with false by auto.
replace (occurs 0 (Ref 0)) with true by auto. 
rewrite ! occurs_closed. auto.  auto. 
eapply2 A_k_closed.
unfold ab_fn. 
rewrite ! maxvar_star_opt.
rewrite ! maxvar_app. 
rewrite b_op_closed. auto.  
cbv; auto. cbv; auto. auto. 
discriminate.  
all: cycle -1.
rewrite (star_opt_occurs_true (App (Op Node)
                       (App (Op Node)
                          (App k_op
                             (app_comb (app_comb (A_k 3) (ab_fn b_op))
                                (Ref 1)))))) at 1.
all: cycle 1. 
unfold flip; rewrite ! occurs_app. 
replace (occurs 0 (Ref 1)) with false by auto.
replace (occurs 0 (Ref 0)) with true by auto. 
rewrite orb_true_r.  auto. discriminate . 
(* 2 *) 
all: cycle -1. 
unfold flip. 
rewrite (star_opt_occurs_false (App (Op Node) _)) at 1.
all: cycle 1. 
unfold app_comb; rewrite ! occurs_app.
replace (occurs 0 (Ref 1)) with false by auto. 
rewrite ! occurs_closed. 
auto. 
eapply2 A_k_closed.
unfold ab_fn. 
rewrite ! maxvar_star_opt.
rewrite ! maxvar_app. 
rewrite b_op_closed. auto.  
cbv; auto. cbv; auto. auto. 
all: cycle -1.
unfold subst_rec; fold subst_rec. 
rewrite ! subst_rec_preserves_app_comb.
rewrite ! subst_rec_ref.  insert_Ref_out.
(* 1 *) 
rewrite star_opt_occurs_true.
all: cycle 1. 
unfold pred, app_comb. 
rewrite ! occurs_app.    
replace (occurs 0 (Ref 0)) with true by auto. 
rewrite ! orb_true_r. 
auto. 
discriminate. 
(* 1 *) 
all: cycle -1. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_l. 
unfold_op; auto. 
eapply2 matchfail_compound_r.
unfold_op; auto. 
unfold_op; eapply2 matchfail_compound_op.
Qed.

Lemma b_abs_op_red: forall M N, sf_red (App (App (App b_op M) N) abs_op) abs_op.
Proof.
intros; unfold b_op. 
eapply transitive_red. 
eapply preserves_app_sf_red.
eapply preserves_app_sf_red.
eapply2 app_comb_red. auto. auto.  
eapply transitive_red.    
eapply2 Y4_fix.
unfold b_fn at 1. 
eapply transitive_red.
eapply preserves_app_sf_red. 
eapply2 star_opt_beta3. auto. 
unfold subst.
rewrite ! subst_rec_preserves_extension.
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
eapply2 app_comb_vs_abs_op. 
(* 1 *) 
eapply transitive_red. 
apply extensions_by_matchfail.  
eapply2 app_comb_vs_abs_op.
(* 1 *)  
eapply transitive_red. 
apply extensions_by_matchfail.  
eapply2 app_comb_vs_abs_op.
(* 1 *)  
eapply transitive_red. 
apply extensions_by_matchfail.  
eapply2 app_comb_vs_abs_op.
eapply transitive_red. 
apply extensions_by_matchfail.  
eapply2 app_comb_vs_abs_op.
(* 1 *) 
unfold_op; simpl.
eapply succ_red. eapply2 s_red. 
eapply succ_red. eapply k_red.
auto. 
auto. 
Qed. 

Lemma b_i_op_red: forall M N, sf_red (App (App (App b_op M) N) i_op) i_op.
Proof.
intros; unfold b_op. 
eapply transitive_red. 
eapply preserves_app_sf_red.
eapply preserves_app_sf_red.
eapply2 app_comb_red. all: auto. 
eapply transitive_red.    
eapply2 Y4_fix.
unfold b_fn at 1. 
eapply transitive_red.
eapply preserves_app_sf_red. 
eapply2 star_opt_beta3. auto. 
unfold subst.
rewrite ! subst_rec_preserves_extension.
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
eapply2 app_comb_vs_I. 
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
eapply2 app_comb_vs_I. 
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
eapply2 app_comb_vs_I. 
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
eapply2 app_comb_vs_I. 
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
eapply2 app_comb_vs_I. 
(* 1 *) 
unfold_op; simpl. repeat eval_tac. 
Qed. 

(* 

Lemma app_comb_vs_A_k : forall M N k, matchfail (app_comb M N) (A_k (S(S(S (S k))))). 
Proof.
 intros. unfold A_k; fold A_k. 
case k; intros. eapply2 app_comb_vs_I. 
case n; intros. eapply2 app_comb_vs_I. 
case n0; intros. unfold app_comb, a_op.
unfold app_comb; unfold star_opt at 2; unfold occurs. unfold_op. 
rewrite ! orb_false_l. 
rewrite orb_true_l.   
eapply2 matchfail_compound_l. unfold occurs.  
 eapply2 app_comb_vs_I. 

 eapply2 matchfail_compound_r.
unfold_op; repeat eapply2 match_app. 
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
unfold_op; auto. 
 Qed. 

*) 


Lemma maxvar_occurs: forall M, maxvar M = 1 -> occurs 0 M = true. 
Proof.
induction M; split_all.
gen_case H n.  omega.
assert(maxvar M1 = 1 \/ maxvar M2 = 1). 
gen_case H (maxvar M1).
gen_case H (maxvar M2).
assert (max n n0 >= n) by eapply2 max_is_max.
left; omega. 
inversion H0. 
rewrite IHM1; auto. 
rewrite IHM2; auto.
eapply2 orb_true_r. 
Qed.  

Lemma pattern_size_app: forall M N, pattern_size (App M N) = pattern_size M + pattern_size N.
Proof. auto. Qed. 

Lemma pattern_size_op: forall o, pattern_size (Op o) = 0.
Proof. auto. Qed. 

 


Lemma b_b_op_red: forall M N, sf_red (App (App (App b_op M) N) b_op) b_op.
Proof.
intros; unfold b_op. 
eapply transitive_red. 
eapply preserves_app_sf_red.
eapply preserves_app_sf_red.
eapply2 app_comb_red. all: auto. 
eapply transitive_red.    
eapply2 Y4_fix.
unfold b_fn at 1. 
eapply transitive_red.
eapply preserves_app_sf_red. 
eapply2 star_opt_beta3. auto. 
unfold subst.
rewrite ! subst_rec_preserves_extension.
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_r.
apply matchfail_program.
eapply2 h_fn_program. 
split. eapply2 omega_k_normal. eapply2 omega_k_closed. 
eapply2 h_fn_vs_omega_k. 
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
eapply matchfail_program. 
eapply2 app_comb_program. 
split. eapply2 omega_k_normal. eapply2 omega_k_closed. 
split. eapply2 omega_k_normal. eapply2 omega_k_closed. 
split. eapply2 A_k_normal. eapply2 A_k_closed.
discriminate.   
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_r.
eapply matchfail_program. 
split. eapply2 omega_k_normal. eapply2 omega_k_closed. 
split. eapply2 omega_k_normal. eapply2 omega_k_closed. 
replace 4 with (S (3+0)) by auto. 
apply omega_k_vs_omega_k.
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_r.
eapply matchfail_program. 
split. eapply2 omega_k_normal. eapply2 omega_k_closed. 
split. eapply2 omega_k_normal. eapply2 omega_k_closed. 
replace 4 with (S (2+1)) by auto. 
apply omega_k_vs_omega_k.
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
eapply2 matchfail_app_comb_r.
all: cycle 1. 
unfold_op; simpl. eval_tac . eval_tac. 
(* 1 *) 
unfold b_fn.
unfold extension at 1. 
rewrite star_opt_occurs_true.
all: cycle 1.
unfold_op. 
rewrite ! occurs_app.
rewrite ! occurs_op.
rewrite ! occurs_extension.  
rewrite ! occurs_app.
rewrite ! occurs_op.
rewrite pattern_size_app_comb2.
rewrite ! pattern_size_app. 
rewrite ! pattern_size_op. 
rewrite ! pattern_size_ref.
rewrite ! pattern_size_closed.
all: cycle 1. 
rewrite omega_k_closed. auto. 
rewrite omega_k_closed; auto.
rewrite Y_k_closed. omega. omega.  
rewrite A_k_closed. omega. 
discriminate. 
all: cycle 1. 
unfold ab_op. 
rewrite ! occurs_star_opt. 
unfold app_comb2, flip, app_comb.
unfold_op.  
rewrite ! occurs_app.
rewrite ! occurs_op.
rewrite orb_false_l at 1.  
rewrite 10? orb_false_l. 
rewrite ! orb_false_l. 
 
unfold pattern_size; fold pattern_size. 
rewrite ! pattern_size_app.  
rewrite ! occurs_extension.  

..............

apply maxvar_occurs.
rewrite ! maxvar_app.
rewrite ! maxvar_op. 
rewrite maxvar_extension. 
rewrite ! pattern_size_app_comb. 
rewrite ! pattern_size_ref. 
rewrite ! pattern_size_closed. 
2: eapply2 omega_k_closed. 
rewrite ! maxvar_app.
rewrite maxvar_extension. 
rewrite ! pattern_size_app_comb. 
rewrite ! pattern_size_ref. 
rewrite ! pattern_size_closed. 
2: eapply2 omega_k_closed. 
rewrite ! maxvar_app.
rewrite maxvar_extension. 
rewrite ! pattern_size_app_comb. 
rewrite ! pattern_size_ref. 
rewrite ! pattern_size_closed. 
2: eapply2 Y_k_closed.
rewrite maxvar_extension. 
rewrite ! pattern_size_app_comb2. 
rewrite ! pattern_size_app_comb. 
rewrite ! pattern_size_ref. 
rewrite ! pattern_size_closed. 
2: eapply2 A_k_closed. 
rewrite ! maxvar_app.
rewrite maxvar_ab_op. 
rewrite ! maxvar_ref. 
rewrite ! maxvar_app_comb.
rewrite maxvar_case .
rewrite ! pattern_size_app_comb. 
rewrite ! pattern_size_ref. 
rewrite ! pattern_size_closed. 
2: eapply2 omega_k_closed.
2: cbv; auto.
rewrite ! maxvar_app.
rewrite ! maxvar_ref.
rewrite ! A_k_closed.
rewrite ! omega_k_closed.
cbv.    
rewrite maxvar_extension. 
rewrite ! pattern_size_app_comb. 
rewrite ! pattern_size_ref. 
rewrite ! pattern_size_closed. 
2: eapply2 omega_k_closed. 
 




 
rewrite star_opt_occurs_true. 
rewrite star_opt_occurs_true. 
(* 7 *) 
eapply2 matchfail_compound_l.
eapply2 matchfail_compound_r .
eapply2 matchfail_compound_r .
rewrite star_opt_occurs_true. 
rewrite star_opt_occurs_true. 
(* 7 *) 
eapply2 matchfail_compound_l.
eapply2 matchfail_compound_r .
unfold_op; auto. 
eapply2 matchfail_compound_r .
unfold_op; auto.
simpl. 
eapply2 matchfail_op. 
unfold_op; unfold factorable; auto. 
discriminate. 
2: discriminate. 
3: discriminate. 
(* 8 *) 
all: try (rewrite ! occurs_app). 
all: try (rewrite ! occurs_op). 
rewrite orb_false_l at 1. 
rewrite orb_false_l at 1. 
unfold app_comb at 1; unfold case; fold case. 
unfold_op. 
unfold is_program at 1. 
rewrite andb_true_l at 1. 
rewrite andb_true_l at 1. 
rewrite andb_true_l at 1. 
rewrite andb_false_l at 1. 
unfold case_app; fold case_app.
rewrite (star_opt_occurs_true  (App (App (App Fop (Ref 0)) i_op) _)). 
rewrite (star_opt_occurs_true  (App (App Fop (Ref 0)) i_op)).
rewrite (star_opt_occurs_true (Op Node)). 
rewrite ! occurs_app.  

rewrite andb_true_l at 1. 
; fold is_program. 
4: discriminate. 

 





eapply2 app_comb_vs_star_opt.
split. 2: eexact H. auto.  
2: match goal with 
| |- maxvar ?M = 0 => replace M with b_fn by auto end. 
eapply2 b_fn_closed. 
eapply2 b_fn_program.  
(* 1 *) 
rewrite ! occurs_closed. 
2: max_out. 2: max_out. simpl. 


 
inversion H3; subst. eapply2 match_app.
eapply2 app_comb_vs_star_opt_aux.
inversion H. split. inversion H4; auto. 
simpl in H5; max_out. 

  


unfold_op; auto. 
(* 1 *) 
all: cycle 1. 
inversion H. simpl in *; max_out.
(* 1 *)  
ass
case P2. 


 
unfold_op; auto. 
 
 
 

 *) 

 




unfold b_fn. 

eapply2 matchfail_app_comb_r.
eapply matchfail_program. 
split. eapply2 omega_k_normal. eapply2 omega_k_closed. 
split. eapply2 omega_k_normal. eapply2 omega_k_closed. 
replace 4 with (S (2+1)) by auto. 
apply omega_k_vs_omega_k.



split. eapply2 A_k_normal. eapply2 A_k_closed.
discriminate.  
 


 
split. eapply2 A_k_normal. eapply2 A_k_closed.
discriminate.  
 




unfold A_k; fold A_k. 
eapply2 matchfail_app_comb_l.

apply matchfail_program.
eapply2 h_fn_program. 
split. eapply2 omega_k_normal. eapply2 omega_k_closed. 
eapply2 h_fn_vs_omega_k. 
(* 1 *) 



eapply2 matchfail_program. 
eapply2 h_fn_program.
split. eapply2 omega_k_normal. eapply2 omega_k_closed. 
eapply2 h_fn_not_omega.
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
unfold A_k. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. 
unfold_op; eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r.
eapply2 matchfail_op. 
unfold factorable. right; auto. congruence. 
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
unfold r_op, Y_k. 
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
eapply2 program_matching.
split. eapply2 omega_k_normal. eapply2 omega_k_closed.
eapply2 matchfail_program. 
split. eapply2 omega_k_normal. eapply2 omega_k_closed.
split. eapply2 A_k_normal. eapply2 A_k_closed.
discriminate. 
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
unfold r_op, Y_k. 
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_r.
eapply2 matchfail_program. 
split. eapply2 omega_k_normal. eapply2 omega_k_closed.
split. eapply2 omega_k_normal. eapply2 omega_k_closed.
discriminate. 
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail. 
unfold r_op, Y_k. 
eapply2 matchfail_app_comb_r.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_compound_l. 
simpl. 
unfold_op; eapply2 matchfail_compound_r. 
(* 1 *) 
unfold_op; simpl. repeat eval_tac. 
Qed. 



Lemma b_r_op_red: forall M N, sf_red (App (App (App b_op M) N) r_op) r_op.
Proof.
intros; unfold b_op. 
eapply transitive_red. 
eapply preserves_app_sf_red.
eapply preserves_app_sf_red.
eapply2 app_comb_red. all: auto. 
eapply transitive_red.    
eapply2 Y4_fix.
unfold b_fn at 1. 
eapply transitive_red.
eapply preserves_app_sf_red. 
eapply2 star_opt_beta3. auto. 
unfold subst.
rewrite ! subst_rec_preserves_extension.
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_r.
eapply2 matchfail_program. 
eapply2 h_fn_program.
split. eapply2 omega_k_normal. eapply2 omega_k_closed. 
eapply2 h_fn_not_omega.
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
unfold A_k. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. 
unfold_op; eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r.
eapply2 matchfail_op. 
unfold factorable. right; auto. congruence. 
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
unfold r_op, Y_k. 
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
eapply2 program_matching.
split. eapply2 omega_k_normal. eapply2 omega_k_closed.
eapply2 matchfail_program. 
split. eapply2 omega_k_normal. eapply2 omega_k_closed.
split. eapply2 A_k_normal. eapply2 A_k_closed.
discriminate. 
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
unfold r_op, Y_k. 
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_r.
eapply2 matchfail_program. 
split. eapply2 omega_k_normal. eapply2 omega_k_closed.
split. eapply2 omega_k_normal. eapply2 omega_k_closed.
discriminate. 
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail. 
unfold r_op, Y_k. 
eapply2 matchfail_app_comb_r.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_compound_l. 
simpl. 
unfold_op; eapply2 matchfail_compound_r. 
(* 1 *) 
unfold_op; simpl. repeat eval_tac. 
Qed. 



Lemma b_r_op_red: forall M N, sf_red (App (App (App b_op M) N) r_op) r_op.
Proof.
intros; unfold b_op. 
eapply transitive_red. 
eapply preserves_app_sf_red.
eapply preserves_app_sf_red.
eapply2 app_comb_red. all: auto. 
eapply transitive_red.    
eapply2 Y4_fix.
unfold b_fn at 1. 
eapply transitive_red.
eapply preserves_app_sf_red. 
eapply2 star_opt_beta3. auto. 
unfold subst.
rewrite ! subst_rec_preserves_extension.
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_r.
eapply2 matchfail_program. 
eapply2 h_fn_program.
split. eapply2 omega_k_normal. eapply2 omega_k_closed. 
eapply2 h_fn_not_omega.
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
unfold A_k. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. 
unfold_op; eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r.
eapply2 matchfail_op. 
unfold factorable. right; auto. congruence. 
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
unfold r_op, Y_k. 
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
eapply2 program_matching.
split. eapply2 omega_k_normal. eapply2 omega_k_closed.
eapply2 matchfail_program. 
split. eapply2 omega_k_normal. eapply2 omega_k_closed.
split. eapply2 A_k_normal. eapply2 A_k_closed.
discriminate. 
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
unfold r_op, Y_k. 
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_r.
eapply2 matchfail_program. 
split. eapply2 omega_k_normal. eapply2 omega_k_closed.
split. eapply2 omega_k_normal. eapply2 omega_k_closed.
discriminate. 
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail. 
unfold r_op, Y_k. 
eapply2 matchfail_app_comb_r.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_compound_l. 
simpl. 
unfold_op; eapply2 matchfail_compound_r. 
(* 1 *) 
unfold_op; simpl. repeat eval_tac. 
Qed. 



Lemma b_r_op_red: forall M N, sf_red (App (App (App b_op M) N) r_op) r_op.
Proof.
intros; unfold b_op. 
eapply transitive_red. 
eapply preserves_app_sf_red.
eapply preserves_app_sf_red.
eapply2 app_comb_red. all: auto. 
eapply transitive_red.    
eapply2 Y4_fix.
unfold b_fn at 1. 
eapply transitive_red.
eapply preserves_app_sf_red. 
eapply2 star_opt_beta3. auto. 
unfold subst.
rewrite ! subst_rec_preserves_extension.
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_r.
eapply2 matchfail_program. 
eapply2 h_fn_program.
split. eapply2 omega_k_normal. eapply2 omega_k_closed. 
eapply2 h_fn_not_omega.
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
unfold A_k. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. 
unfold_op; eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r.
eapply2 matchfail_op. 
unfold factorable. right; auto. congruence. 
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
unfold r_op, Y_k. 
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
eapply2 program_matching.
split. eapply2 omega_k_normal. eapply2 omega_k_closed.
eapply2 matchfail_program. 
split. eapply2 omega_k_normal. eapply2 omega_k_closed.
split. eapply2 A_k_normal. eapply2 A_k_closed.
discriminate. 
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
unfold r_op, Y_k. 
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_r.
eapply2 matchfail_program. 
split. eapply2 omega_k_normal. eapply2 omega_k_closed.
split. eapply2 omega_k_normal. eapply2 omega_k_closed.
discriminate. 
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail. 
unfold r_op, Y_k. 
eapply2 matchfail_app_comb_r.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_compound_l. 
simpl. 
unfold_op; eapply2 matchfail_compound_r. 
(* 1 *) 
unfold_op; simpl. repeat eval_tac. 
Qed. 



Lemma b_r_op_red: forall M N, sf_red (App (App (App b_op M) N) r_op) r_op.
Proof.
intros; unfold b_op. 
eapply transitive_red. 
eapply preserves_app_sf_red.
eapply preserves_app_sf_red.
eapply2 app_comb_red. all: auto. 
eapply transitive_red.    
eapply2 Y4_fix.
unfold b_fn at 1. 
eapply transitive_red.
eapply preserves_app_sf_red. 
eapply2 star_opt_beta3. auto. 
unfold subst.
rewrite ! subst_rec_preserves_extension.
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_r.
eapply2 matchfail_program. 
eapply2 h_fn_program.
split. eapply2 omega_k_normal. eapply2 omega_k_closed. 
eapply2 h_fn_not_omega.
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
unfold A_k. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. 
unfold_op; eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r.
eapply2 matchfail_op. 
unfold factorable. right; auto. congruence. 
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
unfold r_op, Y_k. 
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
eapply2 program_matching.
split. eapply2 omega_k_normal. eapply2 omega_k_closed.
eapply2 matchfail_program. 
split. eapply2 omega_k_normal. eapply2 omega_k_closed.
split. eapply2 A_k_normal. eapply2 A_k_closed.
discriminate. 
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
unfold r_op, Y_k. 
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_r.
eapply2 matchfail_program. 
split. eapply2 omega_k_normal. eapply2 omega_k_closed.
split. eapply2 omega_k_normal. eapply2 omega_k_closed.
discriminate. 
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail. 
unfold r_op, Y_k. 
eapply2 matchfail_app_comb_r.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_compound_l. 
simpl. 
unfold_op; eapply2 matchfail_compound_r. 
(* 1 *) 
unfold_op; simpl. repeat eval_tac. 
Qed. 


simpl. 

eapply2 matchfail_program. 
split. eapply2 omega_k_normal. eapply2 omega_k_closed.
split. eapply2 omega_k_normal. eapply2 omega_k_closed.
discriminate. 


  
unfold A_k. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. 
unfold_op; eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r.
eapply2 matchfail_op. 
unfold factorable. right; auto. congruence. 
(* 1 *) 
 
 

eapply2 matchfail_app_comb_l.
eapply2 matchfail_program. 
eapply2 h_fn_program.
split. eapply2 omega_k_normal. eapply2 omega_k_closed. 
eapply2 h_fn_not_omega.
(* 1 *) 
 
program.  

eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_flip. 
eapply2 extension_by_matchfail. 

rewrite ! pattern_size_app_comb2.
rewrite ! pattern_size_app_comb. 
rewrite ! pattern_size_ref. 
rewrite ! (pattern_size_closed h_fn). 
2: cbv; auto.
rewrite ! (pattern_size_closed (omega_k 4)). 
2: eapply2 omega_k_closed.
rewrite ! (pattern_size_closed (omega_k 3)). 
2: eapply2 omega_k_closed.
rewrite ! (pattern_size_closed (Y_k 2)). 
2: eapply2 Y_k_closed.
rewrite ! (pattern_size_closed 
unfold plus. 
rewrite ! subst_rec_app.
rewrite ! subst_rec_preserves_app_comb.
rewrite ! (subst_rec_closed (A_k  
rewrite ! subst_rec_ref.   
 
eapply2 h_fn_program.  


 
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
eapply2 Y4_red. 
 
 


Definition op_to_tree o := 
match o with 
| Jop => j_op
| Rop => r_op 
| Hop => h_op 
| Aop => abs_op 
| Iop => i_op 
| Bop => b_op
end.


Fixpoint abs_to_tree M := 
match M with 
| Abstraction_Terms.Op o => op_to_tree o
| Abstraction_Terms.App M1 M2 => App (abs_to_tree M1) (abs_to_tree M2)
end.

Theorem translation_preserves_abs_reduction:
forall M N, abs_red1 M N -> sf_red (abs_to_tree M) (abs_to_tree N). 
Proof. 
intros M N r; induction r; intros; 
unfold abs_to_tree; fold abs_to_tree; unfold op_to_tree. 
(* 14 *) 
auto. 
(* 13 *)  
eapply2 j_red. 
(* 12 *) 
eapply2 r_red. 
(* 11 *) 
eapply2 h_red. 
(* 10 *) 
eapply2 abs_red.
(* 9 *) 
unfold_op. repeat eval_tac. 
(* 8 *) 
eapply2 b_j_red.
(* 7 *) 
eapply2 b_r_red. 
(* 6 *) 
eapply2 b_h_red.
(* 5 *) 
eapply2 b_a_red. 
(* 4 *) 
eapply2 b_i_red.
(* 3 *) 
eapply2 b_b_red.
(* 2 *) 
generalize H; case o; intro. 
(* 7 *) 
congruence. 
(* 6 *) 


unfold r_op. 
unfold b_op at 1. 
eapply transitive-red 



gen_case H o. 
 
all: cycle 1. 


problems with atoms, compounds and abs_op. 


gen_case H o. 
(* 8 *) 
congruence. 
(* 7 *) 




discriminate. 

eapply2 zero_red.     
 
 
*)
