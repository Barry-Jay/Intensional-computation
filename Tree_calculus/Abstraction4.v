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


Lemma star_mono2: forall M N, M <> N -> star M <> star N.
Proof. intros. intro. assert(M = N) by eapply2 star_mono. eapply2 H. Qed. 


Lemma app_comb_mono2: forall M1 M2 N1 N2, M1 <> N1 -> app_comb M1 M2 <> app_comb N1 N2.
Proof. intros. intro. inversion H0. eapply2 H. Qed. 

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
unfold star_opt at 2. unfold occurs0. 
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
unfold star_opt at 2. unfold occurs0. 
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
replace (occurs0 (Ref 0)) with true by auto.
rewrite ! orb_true_r. 
auto. discriminate.
unfold app_comb; unfold_op; rewrite ! occurs_app. 
rewrite (occurs_closed (A_k _)). 
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
unfold occurs0. rewrite ! orb_false_l. 
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
generalize H. clear H. unfold_op; unfold star_opt, occurs0, size; fold size.
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
unfold r_op, Y_k. 
eapply2 matchfail_app_comb_r.
unfold h_fn.
unfold star_opt at 4; unfold occurs0.  rewrite ! orb_false_l. 
unfold subst, subst_rec. insert_Ref_out. unfold pred. 
unfold star_opt at 3; unfold occurs0.  rewrite ! orb_false_l. 
unfold subst, subst_rec. insert_Ref_out. unfold pred. unfold_op. 
unfold star_opt at 2; unfold occurs0.  rewrite ! orb_false_l. 
unfold subst, subst_rec. insert_Ref_out. unfold pred. unfold_op. 
unfold star_opt at 1; unfold occurs0.  rewrite ! orb_false_l.
rewrite ! orb_true_l.  
unfold subst, subst_rec. insert_Ref_out. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_op.
unfold_op; unfold factorable. right; auto. discriminate. 
unfold_op. simpl. eval_tac. eval_tac.   
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
unfold abs_op, ab_op, app_comb2.
unfold app_comb at 5.
rewrite star_opt_occurs_true. 
2: unfold flip; rewrite ! occurs_app.
2: rewrite orb_false_l at 1.  
2: rewrite orb_false_l at 1.  
2: rewrite orb_false_l at 1.  
2: unfold_op; rewrite ! occurs_app; rewrite ! occurs_op.
2: rewrite orb_false_l at 1.  
2: rewrite orb_false_l at 1.  
rewrite occurs_ref. 
2: rewrite orb_false_l at 1.  
2: rewrite orb_false_l at 1.  
2: rewrite orb_false_l at 1.  
2: rewrite orb_false_l at 1.  
2: rewrite orb_false_l at 1.  
2: rewrite orb_false_l at 1.  
2: rewrite orb_false_l at 1.  
2: rewrite orb_false_l at 1.  
2: rewrite orb_false_l at 1.  
2: rewrite orb_false_l at 1.  
2: rewrite orb_false_l at 1.  
2: rewrite orb_false_l at 1.  
2: rewrite orb_false_l at 1.  
2: rewrite (orb_true_r (occurs0 k_op)).
2: rewrite (orb_true_r (occurs0 k_op)).
2: rewrite ! (orb_true_r (occurs0 node)).
2: rewrite (orb_true_l (occurs0 i_op)).
2: rewrite (orb_true_r (occurs0 k_op)).
2: unfold_op; rewrite 1 orb_false_r. rewrite (orb_true_r).
2: rewrite (orb_true_r (occurs0 k_op)).
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r. 


 at 1. 
   



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
 
 

