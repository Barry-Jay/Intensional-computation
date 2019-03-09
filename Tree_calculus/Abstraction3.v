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
(*                   Abstraction3.v                                   *)
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
Require Import IntensionalLib.Tree_calculus.Abstraction.  
Require Import IntensionalLib.Tree_calculus.Abstraction2.  
Require Import IntensionalLib.Tree_calculus.Abstraction2a.  

Set
Keep Proof Equalities.



Lemma matchfail_program: forall P M, program P -> program M -> P <> M -> matchfail P M. 
Proof.
induction P; split_all.
(* 3 *) 
inversion H; split_all. simpl in *; congruence. 
gen2_case H0 H1 M.
inversion H0; subst. simpl in *; congruence.
gen_case H1 o; gen_case H1 o0. 
congruence .
eapply2 matchfail_op. 
eapply2 programs_are_factorable. 
(* 1 *) 
gen2_case H0 H1 M. 
inversion H0; subst. 
simpl in *; congruence.
eapply2 matchfail_compound_op.
inversion H; subst. 
inversion H2; subst. assert(status (App P1 P2) = Passive) by eapply2 closed_implies_passive. 
rewrite H4 in H8. 
congruence. auto. 
(* 1 *) 
assert(P1 = t \/ P1 <> t).  repeat decide equality.
inversion H2; subst. 
eapply2 matchfail_compound_r.
inversion H. inversion H3. 
assert(status (App t P2) = Passive) by eapply2 closed_implies_passive. 
rewrite H9 in H10. 
congruence. auto.        
inversion H0. inversion H3. 
assert(status (App t t0) = Passive) by eapply2 closed_implies_passive. 
rewrite H9 in H10. 
congruence. auto.
eapply2 program_matching. 
inversion H0.  unfold program. split. inversion H3; auto. simpl in *; max_out. 
eapply2 IHP2. 
inversion H; subst. unfold program. split. inversion H3; auto. simpl in *; max_out. 
inversion H0; subst. unfold program. split. inversion H3; auto. simpl in *; max_out.
intro. subst. congruence. 
(* 1 *) 
eapply2 matchfail_compound_l.
inversion H; subst. 
inversion H4; subst.
assert(status (App P1 P2) = Passive) by eapply2 closed_implies_passive. 
rewrite H6 in H10. 
congruence. auto.        
inversion H0; subst.
inversion H4; subst. 
assert(status (App t t0) = Passive) by eapply2 closed_implies_passive. 
rewrite H6 in H10. 
congruence. auto.
eapply2 IHP1. 
inversion H; subst. 
inversion H4; subst.
assert(status (App P1 P2) = Passive) by eapply2 closed_implies_passive. 
rewrite H6 in H10. 
congruence. 
unfold program. split.  auto. simpl in *; max_out.          
inversion H0; subst.
inversion H4; subst. 
assert(status (App t t0) = Passive) by eapply2 closed_implies_passive. 
rewrite H6 in H10. 
congruence. 
unfold program; split. 
inversion H4; auto. simpl in *; max_out. 
Qed. 



Lemma b_fn_normal: normal b_fn. 
Proof. 
unfold b_fn. 
match goal with 
| |- normal (star_opt (star_opt (star_opt ?M))) => 
replace (star_opt (star_opt (star_opt M))) with (multi_star 3 M)
end.
2: unfold multi_star; congruence. 
match goal with 
| |- normal (multi_star 3 ?M) => 
assert(maxvar M = 3) by eapply2 b_fn_body_maxvar 
end.
rewrite <- H at 1. clear H.  
apply bind_normal_to_normal.
eapply2 aux8.  
Qed.

Lemma b_op_program: program b_op. 
Proof.
unfold program.
split. 
eapply2 nf_compound. eapply2 nf_compound. eapply2 nf_compound. unfold_op; repeat eapply2 nf_compound. 
unfold_op; eapply2 nf_compound.  eapply2 nf_compound.  eapply2 nf_compound.  eapply2 nf_compound. 
 eapply2 b_fn_normal.  eapply2 nf_compound. eapply2 Y_k_normal.  
eapply2 b_op_closed.
Qed. 
 

Lemma b_j_red: forall M N, sf_red (App (App (App b_op M) N) j_op)M.
Proof.
intros. unfold b_op. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red.
eapply2 app_comb_red. all: auto.
eapply transitive_red. eapply2 Y4_fix.
unfold b_fn, j_op. 
eapply transitive_red. eapply preserves_app_sf_red. 
eapply2 star_opt_beta3. auto. 
unfold subst. rewrite ! subst_rec_preserves_extension.
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
eapply2 matchfail_app_comb_l. 
eapply2 matchfail_app_comb_l. 
eapply2 matchfail_app_comb_r. 
eapply2 matchfail_program.
eapply2 h_fn_program.
unfold program; split.  eapply2 omega_k_normal. eapply2 omega_k_closed.
discriminate .    
(* 1 *)  
eapply transitive_red. 
eapply2 extensions_by_matchfail. 
eapply2 matchfail_app_comb_l. 
eapply2 matchfail_app_comb_l. 
eapply2 matchfail_app_comb_l. 
eapply2 matchfail_program. 
unfold program; split.
eapply2 app_comb_normal.
rewrite maxvar_app_comb. rewrite ! omega_k_closed. auto. 
unfold program; split.
eapply2 A_k_normal. eapply2 A_k_closed. 
discriminate .    
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail. 
eapply2 matchfail_app_comb_l. 
eapply2 matchfail_app_comb_l. 
eapply2 matchfail_app_comb_r. 
eapply2 matchfail_program. 
unfold program; split. eapply2 omega_k_normal. eapply2 omega_k_closed.
unfold program; split. eapply2 omega_k_normal. eapply2 omega_k_closed.
eapply2 omega_3_not_omega_2. 
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matching.
eapply2 app_comb_matching.
eapply2 program_matching. 
eapply2 Y_k_program.   
unfold app. unfold map ; fold map.
unfold fold_left. 
rewrite ! pattern_size_app_comb. unfold pattern_size; fold pattern_size. 
rewrite ! pattern_size_closed. 
unfold subst_rec; fold subst_rec. insert_Ref_out. 
unfold subst_rec; fold subst_rec. insert_Ref_out. 
unfold plus, lift. rewrite ! lift_rec_lift_rec. 
unfold plus, subst. rewrite ! subst_rec_lift_rec. all: try omega . 
rewrite lift_rec_null.  auto. eapply2 Y_k_closed.
Qed. 
 
 

Lemma b_r_red: forall M N P, sf_red (App (App (App b_op M) N) (App r_op P)) (App N P).
Proof.
intros. unfold b_op. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red.
eapply2 app_comb_red. all: auto.
eapply transitive_red. eapply2 Y4_fix.
unfold b_fn, r_op. 
eapply transitive_red. eapply preserves_app_sf_red. 
eapply2 star_opt_beta3. auto. 
unfold subst. rewrite ! subst_rec_preserves_extension. 
eapply transitive_red. 
eapply preserves_app_sf_red. auto. 
eapply transitive_red. 
eapply2 app_comb_red. 
eapply2 r_aux. 
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_r.
eapply2 matchfail_program.
unfold program; unfold h_fn; split; auto.
unfold_op; simpl; unfold_op; repeat eapply2 nf_compound. 
unfold subst; simpl; auto.
unfold program; split. eapply2 omega_k_normal. eapply2 omega_k_closed.
apply h_fn_not_omega. 
(* 1 *) 
eapply transitive_red.
eapply2 extensions_by_matchfail.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_program.
unfold program; split. 
eapply2 app_comb_normal. 
rewrite maxvar_app_comb; rewrite ! omega_k_closed; auto. 
split. eapply2 omega_k_normal. eapply2 omega_k_closed.
discriminate.  
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matching. 
eapply2 app_comb_matching. 
eapply2 app_comb_matching. 
eapply2 program_matching. 
unfold program. split.  
eapply2 app_comb_normal. 
rewrite maxvar_app_comb. 
rewrite ! (omega_k_closed); cbv; auto. 
(* 1 *) 
rewrite ! app_nil_l.
unfold length; fold length. 
unfold fold_left, map, app, subst. 
rewrite ! subst_rec_app.
rewrite ! pattern_size_app_comb. 
rewrite ! pattern_size_ref. 
rewrite ! pattern_size_closed. 
2: eapply2 omega_k_closed. 
unfold plus. 
rewrite ! subst_rec_ref.  insert_Ref_out.
unfold plus, lift; rewrite ! lift_rec_lift_rec; try omega. 
unfold plus; rewrite ! subst_rec_lift_rec; try omega. 
rewrite ! lift_rec_null. 
rewrite ! subst_rec_ref.  insert_Ref_out.
rewrite ! subst_rec_ref.  insert_Ref_out.
rewrite ! subst_rec_ref.  insert_Ref_out.
rewrite ! subst_rec_ref.  insert_Ref_out.
 unfold lift; rewrite ! lift_rec_null. auto. 
Qed. 

Lemma Y_k_red4: forall M N, sf_red (App (App (Y_k 4) M) N) 
 (app_comb a_op (app_comb (app_comb (app_comb (omega_k 4) (omega_k 4)) M) N)).
Proof.
intros. unfold Y_k; fold Y_k. 
eapply transitive_red. eapply preserves_app_sf_red. 
eapply2 app_comb_red. auto. 
eapply transitive_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply2 app_comb_red. all: auto.
eapply transitive_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply2 A3_red. all: auto. 
eapply transitive_red. eapply preserves_app_sf_red. 
eapply2 app_comb_red. auto. 
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply2 A3_red. auto. 
eapply transitive_red. eapply2 app_comb_red.
eapply transitive_red. eapply2 A3_red.
unfold A_k. 
 auto. 
Qed. 


(* delete ? 
Lemma aux_big: 
matchfail
  (App
     (App (Op Node)
        (App (Op Node)
           (App (App (Op Node) (App (Op Node) (Op Node)))
              (App (Op Node) (Op Node)))))
     (App
        (App (Op Node) (App (Op Node) (App (App (Op Node) (Op Node)) h_fn)))
        (App (App (Op Node) (Op Node))
           (App
              (App (Op Node)
                 (App (Op Node)
                    (App (App (Op Node) (App (Op Node) (Op Node)))
                       (App (Op Node) (Op Node)))))
              (App
                 (App (Op Node)
                    (App (Op Node)
                       (App (App (Op Node) (Op Node)) (omega_k 4))))
                 (App (App (Op Node) (Op Node)) (omega_k 4)))))))
  (star_opt
     (App
        (App (Op Node)
           (App (Op Node)
              (star_opt
                 (App
                    (App (Op Node)
                       (App (Op Node) (App (App (Op Node) (Op Node)) (Ref 1))))
                    (star_opt (App b_op (Ref 0)))))))
        (App
           (App (Op Node)
              (App (Op Node)
                 (App
                    (App (Op Node)
                       (App (Op Node)
                          (subst (App (Op Node) (Op Node)) (Op Node))))
                    (App (App (Op Node) (Op Node)) (Op Node)))))
           (App (App (Op Node) (Op Node)) (Op Node))))).
Proof.
unfold star_opt at 3. 
rewrite occurs_closed.
2: eapply2 b_op_closed.  
unfold subst; rewrite subst_rec_closed.
2: rewrite b_op_closed; omega.  
rewrite (star_opt_occurs_false (App
                    (App (Op Node)
                       (App (Op Node) (App (App (Op Node) (Op Node)) (Ref 1))))
                    b_op)). 
all: cycle 1. 
rewrite ! occurs_app. 
replace (occurs0 b_op) with false.
2: rewrite occurs_closed; [auto |eapply2 b_op_closed]. 
simpl; auto. 
(* 1 *) 
unfold subst_rec; fold subst_rec. 
rewrite subst_rec_closed.
2: rewrite b_op_closed; auto. 
  insert_Ref_out. unfold pred.
rewrite (star_opt_occurs_true).
all: cycle 1. 
rewrite ! occurs_app. 
replace (occurs0 (Ref 0)) with true by auto. 
rewrite ! orb_true_r. 
simpl; auto. 
discriminate. 
(* 1 *) 
eapply2 matchfail_compound_l.  
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
rewrite star_opt_closed.
unfold_op; eapply2 matchfail_compound_l.
simpl; auto.
Qed.


Lemma aux_hb : forall P Q, 
matchfail
  (app_comb
     (app_comb (app_comb (app_comb (omega_k 4) (omega_k 4)) h_fn) (Ref 0))
     (Ref 1)) (app_comb (app_comb (ab_fn b_op) P) Q).
Proof.
intros. 
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
unfold ab_fn. 
rewrite star_opt_occurs_true.
3: discriminate. 
2: rewrite ! occurs_app.
2: unfold occurs0 at 2; rewrite orb_true_r; simpl; auto. 
(* 1 *) 
rewrite (star_opt_occurs_true (App b_op _)).
3: discriminate. 
2: rewrite ! occurs_app.
2: unfold occurs0 at 2; rewrite orb_true_r; simpl; auto. 
(* 1 *) 
unfold star_opt at 3 4 5.
rewrite occurs_closed. 
2: eapply2 b_op_closed. 
(* 1 *) 
rewrite star_opt_occurs_true. 
3: discriminate.
2: rewrite ! occurs_app.
2: unfold occurs0 at 4.  2: rewrite  orb_true_r at 1. 
2: rewrite  orb_true_r at 1. 
2: rewrite  orb_true_r at 1. 
2: simpl; auto. 
(* 1 *) 
rewrite (star_opt_occurs_true (Op Node)). 
2: cbv; auto. 
2: discriminate. 
unfold_op; unfold star_opt at 3 4. 
  unfold occurs0. 
rewrite ! orb_false_l. 
rewrite star_opt_occurs_true . 
all: cycle 1.
2: discriminate.  
rewrite star_opt_occurs_false.
2: rewrite ! occurs_app. 
2: replace (occurs0 (subst b_op (Op Node))) with false. 
2: cbv; auto. 
2: unfold subst; rewrite subst_rec_closed. 
2: rewrite occurs_closed. 2: auto. 
2: eapply2 b_op_closed. 
2: rewrite b_op_closed; auto. 
unfold subst_rec; fold subst_rec.
insert_Ref_out. 
rewrite ! occurs_app. 
replace (occurs0 (Ref (pred 1))) with true by auto.
replace (occurs0 (Op Node)) with false by auto.
rewrite occurs_closed. simpl. auto.
unfold_op; auto. 
(* 1 *)  
eapply2 matchfail_program. 
split. 
eapply2 nf_compound. 
repeat eapply2 nf_compound. 
eapply2 nf_compound. 
repeat eapply2 nf_compound. 
eapply2 nf_compound. 
eapply2 nf_compound.
eapply2 h_fn_normal. 
 
eapply2 nf_compound. 
eapply2 nf_compound. 





eapply2 aux_big.
Qed.  




Lemma aux_ab_fn: 
matchfail
  (App
     (App (Op Node)
        (App (Op Node)
           (App (App (Op Node) (App (Op Node) (Op Node)))
              (App (Op Node) (Op Node)))))
     (App
        (App (Op Node)
           (App (Op Node) (App (App (Op Node) (Op Node)) (Ref 0))))
        (App (App (Op Node) (Op Node))
           (App
              (App (Op Node)
                 (App (Op Node)
                    (App (App (Op Node) (App (Op Node) (Op Node)))
                       (App (Op Node) (Op Node)))))
              (App
                 (App (Op Node)
                    (App (Op Node)
                       (App (App (Op Node) (Op Node)) (omega_k 4))))
                 (App (App (Op Node) (Op Node)) (omega_k 4)))))))
  (ab_fn b_op).
Proof. 
unfold ab_fn.
(* 2 *) 
rewrite star_opt_occurs_true.
all: cycle 1 .
rewrite ! occurs_app. 
unfold occurs0 at 2.
rewrite orb_true_r. simpl . auto. congruence. 
unfold star_opt at 3. 
rewrite star_opt_occurs_true.
all: cycle 1.
rewrite ! occurs_app.
unfold occurs0 at 4.
rewrite orb_true_r at 1. 
rewrite orb_true_r at 1. 
rewrite orb_true_r at 1. 
simpl . auto.
rewrite star_opt_occurs_true.
congruence .
rewrite ! occurs_app.
unfold occurs0 at 2.
rewrite orb_true_r at 1. 
simpl . auto. congruence .
(* 1 *) 
rewrite (star_opt_occurs_true (App b_op (Ref 0))).
all: cycle 1. 
rewrite ! occurs_app.
unfold occurs0 at 2.
rewrite orb_true_r at 1. 
simpl . auto. congruence .
(* 1 *) 
unfold star_opt at 3 4. 
rewrite occurs_closed .
2: rewrite b_op_closed; auto.
unfold subst; rewrite subst_rec_closed. 
2:rewrite b_op_closed; auto.
rewrite (star_opt_occurs_false (App (App (Op Node) (App (Op Node) (App k_op (Ref 1)))) b_op)).
2: rewrite ! occurs_app. 
2: rewrite (occurs_closed b_op). 2: simpl; auto. 2: eapply2 b_op_closed.
unfold subst_rec. fold subst_rec. 
insert_Ref_out.
rewrite ! subst_rec_closed  . 2: rewrite b_op_closed; omega. 2: unfold_op; auto. 
rewrite star_opt_occurs_true. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r. 
unfold_op; unfold star_opt. unfold occurs0. 
rewrite ! orb_false_l.
unfold_op; unfold subst, subst_rec. 
eapply2 matchfail_compound_l.
rewrite ! occurs_app. 
unfold_op. unfold pred. unfold occurs0 at 1 2 3 4 5 6 7. simpl. auto. 
rewrite star_opt_occurs_true. congruence . 
simpl; auto. discriminate.
Qed.

Lemma aux_ab_fn2: 
matchfail
  (App
     (App (Op Node)
        (App (Op Node)
           (App (App (Op Node) (App (Op Node) (Op Node)))
              (App (Op Node) (Op Node)))))
     (App
        (App (Op Node)
           (App (Op Node) (App (App (Op Node) (Op Node)) (omega_k 3))))
        (App (App (Op Node) (Op Node)) (omega_k 3)))) (ab_fn b_op).
Proof.
unfold ab_fn.
rewrite star_opt_occurs_true.
all: cycle 1 .
rewrite ! occurs_app. 
unfold occurs0 at 2.
rewrite orb_true_r. simpl . auto. congruence. 
unfold star_opt at 3. 
rewrite star_opt_occurs_true.
all: cycle 1.
rewrite ! occurs_app.
unfold occurs0 at 4.
rewrite orb_true_r at 1. 
rewrite orb_true_r at 1. 
rewrite orb_true_r at 1. 
simpl . auto.
rewrite star_opt_occurs_true.
congruence .
rewrite ! occurs_app.
unfold occurs0 at 2.
rewrite orb_true_r at 1. 
simpl . auto. congruence .
rewrite (star_opt_occurs_true (App b_op (Ref 0))).
all: cycle 1. 
rewrite ! occurs_app.
unfold occurs0 at 2.
rewrite orb_true_r at 1. 
simpl . auto. congruence .
unfold star_opt at 3 4. 
rewrite occurs_closed .
2: rewrite b_op_closed; auto.
unfold subst; rewrite subst_rec_closed. 
2:rewrite b_op_closed; auto.
rewrite (star_opt_occurs_false (App (App (Op Node) (App (Op Node) (App k_op (Ref 1)))) b_op)).
2: rewrite ! occurs_app. 
2: rewrite (occurs_closed b_op). 2: simpl; auto. 2: eapply2 b_op_closed.
unfold subst_rec. fold subst_rec. 
insert_Ref_out.
rewrite ! subst_rec_closed  . 2: rewrite b_op_closed; omega. 2: unfold_op; auto. 
rewrite star_opt_occurs_true. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r. 
unfold_op; unfold star_opt. unfold occurs0. 
rewrite ! orb_false_l.
unfold_op; unfold subst, subst_rec. 
eapply2 matchfail_compound_l.
rewrite ! occurs_app. 
unfold_op. unfold pred. unfold occurs0 at 1 2 3 4 5 6 7. simpl. auto. 
rewrite star_opt_occurs_true. congruence . 
simpl; auto. discriminate.
Qed.

Lemma aux_ab_fn3: 
matchfail
  (App
     (App (Op Node)
        (App (Op Node)
           (App (App (Op Node) (App (Op Node) (Op Node)))
              (App (Op Node) (Op Node)))))
     (App
        (App (Op Node)
           (App (Op Node) (App (App (Op Node) (Op Node)) (omega_k 2))))
        (App (App (Op Node) (Op Node)) (A_k 3)))) (ab_fn b_op).
Proof.
unfold ab_fn.
rewrite star_opt_occurs_true.
all: cycle 1 .
rewrite ! occurs_app. 
unfold occurs0 at 2.
rewrite orb_true_r. simpl . auto. congruence. 
unfold star_opt at 3. 
rewrite star_opt_occurs_true.
all: cycle 1.
rewrite ! occurs_app.
unfold occurs0 at 4.
rewrite orb_true_r at 1. 
rewrite orb_true_r at 1. 
rewrite orb_true_r at 1. 
simpl . auto.
rewrite star_opt_occurs_true.
congruence .
rewrite ! occurs_app.
unfold occurs0 at 2.
rewrite orb_true_r at 1. 
simpl . auto. congruence .
rewrite (star_opt_occurs_true (App b_op (Ref 0))).
all: cycle 1. 
rewrite ! occurs_app.
unfold occurs0 at 2.
rewrite orb_true_r at 1. 
simpl . auto. congruence .
unfold star_opt at 3 4. 
rewrite occurs_closed .
2: rewrite b_op_closed; auto.
unfold subst; rewrite subst_rec_closed. 
2:rewrite b_op_closed; auto.
rewrite (star_opt_occurs_false (App (App (Op Node) (App (Op Node) (App k_op (Ref 1)))) b_op)).
2: rewrite ! occurs_app. 
2: rewrite (occurs_closed b_op). 2: simpl; auto. 2: eapply2 b_op_closed.
unfold subst_rec; fold subst_rec. 
insert_Ref_out.
rewrite ! subst_rec_closed  . 2: rewrite b_op_closed; omega. 2: unfold_op; auto. 
rewrite star_opt_occurs_true. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r.
cbv.  
eapply2 matchfail_compound_l.
rewrite ! occurs_app. 
unfold_op. unfold pred. unfold occurs0 at 1 2 3 4 5 6 7. simpl. auto. 
rewrite star_opt_occurs_true. congruence . 
simpl; auto. discriminate.
Qed.

*)


Lemma ab_fn_program: 
forall M, program M -> program (ab_fn M).
Proof.
intros. inversion H. unfold ab_fn; split.
all: cycle 1.
rewrite ! maxvar_star_opt. 
rewrite ! maxvar_app.
rewrite H1. 
cbv; auto.  
rewrite star_opt_occurs_true.
2: rewrite ! occurs_app. 
2: unfold occurs0 at 2 .
2: rewrite orb_true_r. 2: simpl; auto. 2: congruence. 
unfold star_opt at 3. 
rewrite (star_opt_occurs_true (App M _)). 
2: rewrite ! occurs_app. 
2: unfold occurs0 at 2.
2: rewrite orb_true_r. 2: simpl; auto. 2: congruence. 
unfold star_opt at 3 4. 
rewrite occurs_closed . 2: auto. 
unfold subst; rewrite subst_rec_closed. 2: rewrite H1; auto. 
(* 1 *) 
repeat eapply2 star_opt_normal.
repeat eapply2 nf_compound. 
all: unfold_op; auto. 
Qed. 

Lemma yk_not_a: forall k h, matchfail (app_comb (app_comb (omega_k k) (omega_k k)) h) (ab_fn b_op). 
Proof. 
unfold ab_fn. 
rewrite star_opt_occurs_true. 
2: rewrite ! occurs_app.  2: unfold occurs0 at 2.
2: rewrite orb_true_r; simpl; auto. 
2: discriminate. 
unfold star_opt at 3.
(* 1 *) 
rewrite (star_opt_occurs_true (App b_op _)). 
2: rewrite ! occurs_app.  2: unfold occurs0 at 2.
2: rewrite orb_true_r; simpl; auto. 
2: discriminate. 
unfold star_opt at 3 4.
rewrite occurs_closed. 
2: eapply2 b_op_closed.
(* 1 *)  
rewrite star_opt_occurs_true. 
2: rewrite ! occurs_app.  2: unfold occurs0 at 4.
2: replace (occurs0 (Op Node)) with false by auto. 
2: rewrite ! orb_false_l. 2: simpl; auto. 
2: congruence. 
(* 1 *) 
rewrite (star_opt_occurs_true (Op Node)).
2: cbv; auto. 2: congruence. 
(* 1 *) 
rewrite (star_opt_occurs_true (Op Node)).
2: cbv; auto. 2: congruence. 
(* 1 *) 
unfold_op; unfold star_opt at 3 4 5. 
unfold occurs0.  rewrite orb_false_l.
(* 1 *) 
rewrite (star_opt_occurs_false (App
                 (App (Op Node)
                    (App (Op Node) (App (App (Op Node) (Op Node)) (Ref 1))))
                 (subst b_op (Op Node)))). 
2: rewrite ! occurs_app. 
2: rewrite ! orb_false_l.
2: apply occurs_closed.
2: unfold subst; rewrite subst_rec_closed. 
2: eapply2 b_op_closed. 
2: rewrite b_op_closed; auto.
(* 1 *) 
rewrite ! subst_rec_app.
rewrite ! subst_rec_ref. insert_Ref_out. 
(* 1 *) 
unfold subst; rewrite ! subst_rec_closed. 
2: cbv; auto. 
2: rewrite b_op_closed; auto. 
2: rewrite subst_rec_closed. 
2: rewrite b_op_closed; auto. 
2: rewrite b_op_closed; auto. 
2: cbv; auto. 
(* 1 *) 
rewrite (star_opt_occurs_true).
rewrite star_opt_closed. 
all: cycle 1. 
cbv; auto. 
rewrite ! occurs_app. 
rewrite ! orb_false_l. 
simpl; auto.
congruence.
(* 1 *) 
intros. 
eapply2 matchfail_compound_l.
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
unfold_op; eapply2 matchfail_compound_l.
Qed. 
 
 
Lemma app_comb_not_a: forall M N, matchfail (app_comb M N) (ab_fn b_op). 
Proof. 
unfold ab_fn. 
rewrite star_opt_occurs_true. 
2: rewrite ! occurs_app.  2: unfold occurs0 at 2.
2: rewrite orb_true_r; simpl; auto. 
2: discriminate. 
unfold star_opt at 3.
(* 1 *) 
rewrite (star_opt_occurs_true (App b_op _)). 
2: rewrite ! occurs_app.  2: unfold occurs0 at 2.
2: rewrite orb_true_r; simpl; auto. 
2: discriminate. 
unfold star_opt at 3 4.
rewrite occurs_closed. 
2: eapply2 b_op_closed.
(* 1 *)  
rewrite star_opt_occurs_true. 
2: rewrite ! occurs_app.  2: unfold occurs0 at 4.
2: replace (occurs0 (Op Node)) with false by auto. 
2: rewrite ! orb_false_l. 2: simpl; auto. 
2: congruence. 
(* 1 *) 
rewrite (star_opt_occurs_true (Op Node)).
2: cbv; auto. 2: congruence. 
(* 1 *) 
rewrite (star_opt_occurs_true (Op Node)).
2: cbv; auto. 2: congruence. 
(* 1 *) 
unfold_op; unfold star_opt at 3 4 5. 
unfold occurs0.  rewrite orb_false_l.
(* 1 *) 
rewrite (star_opt_occurs_false (App
                 (App (Op Node)
                    (App (Op Node) (App (App (Op Node) (Op Node)) (Ref 1))))
                 (subst b_op (Op Node)))). 
2: rewrite ! occurs_app. 
2: rewrite ! orb_false_l.
2: apply occurs_closed.
2: unfold subst; rewrite subst_rec_closed. 
2: eapply2 b_op_closed. 
2: rewrite b_op_closed; auto.
(* 1 *) 
rewrite ! subst_rec_app.
rewrite ! subst_rec_ref. insert_Ref_out. 
(* 1 *) 
unfold subst; rewrite ! subst_rec_closed. 
2: cbv; auto. 
2: rewrite b_op_closed; auto. 
2: rewrite subst_rec_closed. 
2: rewrite b_op_closed; auto. 
2: rewrite b_op_closed; auto. 
2: cbv; auto. 
(* 1 *) 
rewrite (star_opt_occurs_true).
rewrite star_opt_closed. 
all: cycle 1. 
cbv; auto. 
rewrite ! occurs_app. 
rewrite ! orb_false_l. 
simpl; auto.
congruence.
(* 1 *) 
intros. 
eapply2 matchfail_compound_l.
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
unfold_op; eapply2 matchfail_compound_l.
Qed. 
 
 
 Lemma matchfail_app_comb_swap: forall M N P, matchfail (app_comb M N) (swap P). 
Proof.
intros. unfold app_comb, swap. 
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r. 
unfold_op; eapply2 matchfail_compound_l.
Qed. 
 

Lemma subst_rec_preserves_app_comb: 
forall M N P k, subst_rec (app_comb M N) P k = app_comb (subst_rec M P k) (subst_rec N P k).
Proof.
intros; unfold app_comb. unfold_op. unfold subst_rec; fold subst_rec. auto. 
Qed.

Lemma b_a_red: 
forall M N P Q, (* program P -> (* needed to drive matching *)  *) 
sf_red (App (App (App b_op M) N) (App (App abs_op P) Q)) 
(App (App abs_op (App (App (App b_op M) N) P)) Q).
Proof.
intros. 
unfold b_op at 1. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red.
eapply2 app_comb_red. all: auto.
eapply transitive_red. eapply2 Y4_fix.
eapply transitive_red. eapply preserves_app_sf_red. auto.
eapply2 abs2_red.  
unfold b_fn at 1. 
eapply transitive_red. eapply preserves_app_sf_red. 
eapply2 star_opt_beta3. auto. 
unfold subst. rewrite ! subst_rec_preserves_extension. 
(* 1 *) (* H *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail.
eapply2 matchfail_app_comb_l. 
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_swap. 
(* 1 *)   (* B *) 
eapply transitive_red.
eapply2 extensions_by_matchfail. 
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_swap. 
(* 1 *) (* R *) 
eapply transitive_red.
eapply2 extensions_by_matchfail.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_swap. 
(* 1 *) (* J , tricky to distinguish J from A *) 
eapply transitive_red.
eapply2 extensions_by_matchfail.
eapply2 matchfail_app_comb_l.
eapply2 matchfail_app_comb_r. 
eapply2 matchfail_program.
(* 4 *) 
split. eapply2 omega_k_normal. eapply2 omega_k_closed.
rewrite star_opt_occurs_true.
2: rewrite ! occurs_app. 2: rewrite orb_true_r; simpl; auto. 
2: discriminate. 
eapply2 app_comb_program.
split. eapply2 A_k_normal. eapply2 A_k_closed.
(* 3 *) 
split. 
repeat eapply2 star_opt_normal. 
eapply2 nf_compound. 
unfold star_opt. unfold_op.  repeat eapply2 nf_compound. 
unfold star_opt, occurs0. 
rewrite orb_true_r. 
rewrite occurs_closed. 
unfold_op; eapply2 nf_compound.
unfold subst; rewrite subst_rec_closed.
eapply2 b_op_program.
rewrite b_op_closed; auto. 
rewrite b_op_closed; auto. 
rewrite ! maxvar_star_opt.
rewrite ! maxvar_app. 
rewrite ! maxvar_star_opt.
rewrite ! maxvar_app. 
rewrite b_op_closed. simpl.  auto.
intro; discriminate. 
(* 1 *) (* A *) 
eapply transitive_red. 
eapply2 extensions_by_matching.
eapply2 match_app_comb.
eapply2 match_app_comb.
eapply2 match_app_comb.
eapply2 program_matching.
split. eapply2 A_k_normal. 
eapply2 A_k_closed. 
(* 1 *) 
rewrite ! app_nil_r. 
unfold length; fold length.
rewrite ! map_lift0. 
unfold map. 
unfold app; fold app.
rewrite ! pattern_size_app_comb.  
unfold pattern_size; fold pattern_size .
rewrite ! pattern_size_closed.
2: eapply2 A_k_closed. 
unfold plus, fold_left. 
unfold subst; rewrite ! subst_rec_app.
rewrite ! subst_rec_preserves_app_comb. 
rewrite (subst_rec_closed (A_k 3)) at 1. 
2: rewrite A_k_closed; auto. 
rewrite (subst_rec_closed (A_k 3)) at 1. 
2: rewrite A_k_closed; auto. 
rewrite (subst_rec_closed (A_k 3)) at 1. 
2: rewrite A_k_closed; auto. 
rewrite (subst_rec_closed (A_k 3)) at 1. 
2: rewrite A_k_closed; auto. 
rewrite (subst_rec_closed (A_k 3)) at 1. 
2: rewrite A_k_closed; auto. 
rewrite (subst_rec_closed (A_k 3)) at 1. 
2: rewrite A_k_closed; auto. 
rewrite ! subst_rec_ref; insert_Ref_out. 
rewrite ! subst_rec_ref; insert_Ref_out. 
rewrite ! subst_rec_ref; insert_Ref_out. 
unfold lift; rewrite ! lift_rec_lift_rec; try omega.
unfold plus. 
rewrite ! subst_rec_lift_rec; try omega.
rewrite ! lift_rec_null. 
rewrite subst_rec_ref at 1; insert_Ref_out. 
rewrite subst_rec_ref at 1; insert_Ref_out.
unfold lift; rewrite ! lift_rec_null. 
rewrite ! subst_rec_lift_rec; try omega.
rewrite subst_rec_ref at 1; insert_Ref_out. 
unfold lift; rewrite ! lift_rec_null. 
rewrite ! subst_rec_lift_rec; try omega. 
rewrite subst_rec_ref at 1; insert_Ref_out.
rewrite subst_rec_ref at 1; insert_Ref_out.
rewrite subst_rec_ref at 1; insert_Ref_out.
unfold lift; rewrite ! lift_rec_null.

eapply transitive_red. eapply preserves_app_sf_red.
 eapply2 app_comb_red. auto. 
eapply transitive_red. eapply preserves_app_sf_red.
eapply2 A3_red. auto. 
eapply transitive_red.
eapply2 app_comb_red.
unfold A_k. 
eapply transitive_red.
eapply2 a_op2_red. 
unfold abs_op. unfold ab_op. 


eval_tac. 



rewrite subst_rec_ref at 1; insert_Ref_out.
rewrite subst_rec_ref at 1; insert_Ref_out.
unfold lift; rewrite lift_rec_lift_rec; try omega.  unfold plus. 
rewrite ! subst_rec_lift_rec; try omega. 


 
rewrite subst_rec_ref at 1; insert_Ref_out. 



rewrite ! (subst_rec_closed (A_k 3)). 

rewrite ! lift_rec_null.
eapply2 preserves_app_sf_red. 
Qed. 
 



Lemma b_h_red: 
forall M N P Q, 
sf_red (App (App (App b_op M) N) (App (App h_op P) Q)) 
(App (App (App (App b_op M) N) P) (App (App (App b_op M) N) Q)).
Proof.
intros. unfold b_op. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red.
eapply2 app_comb_red. auto. auto.  
eapply transitive_red. eapply2 Y4_fix.
unfold b_fn at 1.
eapply transitive_red. eapply preserves_app_sf_red. 
eapply2 star_opt_beta3. auto. 
unfold subst. rewrite ! subst_rec_preserves_extension. 
eapply transitive_red. 
eapply preserves_app_sf_red. auto.  
unfold h_op. 
eapply transitive_red. eapply preserves_app_sf_red.
eapply2 app_comb_red.  auto.  
 eapply transitive_red. 
eapply preserves_app_sf_red.
eapply2 Y_k_red4. auto. 
eapply app_comb_red.  
 eapply transitive_red. 
eapply preserves_app_sf_red. auto. 
eapply2 a_op2_red. 
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matching.
eapply2 app_comb_matching.  
eapply2 app_comb_matching.
eapply2 program_matching. 
unfold program; split. 
repeat eapply2 app_comb_normal.
eapply2 h_fn_program.
rewrite ! maxvar_app_comb. 
rewrite ! omega_k_closed. 
unfold max. eapply2 h_fn_program. 
(* 1 *) 
rewrite ! pattern_size_app_comb. 
replace (pattern_size (omega_k 4)) with 0 by (rewrite pattern_size_closed; [auto| eapply2 omega_k_closed]). 
replace (pattern_size (h_fn)) with 0 . 
2: (rewrite pattern_size_closed; unfold h_fn; auto). 
unfold pattern_size. unfold plus. unfold length. unfold app. unfold map. 
unfold fold_left, subst. 
rewrite ! subst_rec_app. rewrite ! subst_rec_ref.  insert_Ref_out. 
rewrite ! subst_rec_ref.  insert_Ref_out. 
rewrite ! subst_rec_ref.  insert_Ref_out. 
rewrite ! subst_rec_ref.  insert_Ref_out. 
unfold lift. rewrite ! lift_rec_lift_rec; try omega. unfold plus.
rewrite ! subst_rec_lift_rec; try omega.
rewrite ! lift_rec_null. 
unfold subst_rec.  insert_Ref_out. unfold lift; rewrite lift_rec_null; auto. 
Qed.
 

Lemma b_b_red: 
forall M N P Q, 
sf_red (App (App (App b_op M) N) (App (App b_op P) Q)) 
(App (App b_op (App (App (App b_op M) N) P)) (App (App (App b_op M) N) Q)).
Proof.
intros. unfold b_op. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red.
eapply2 app_comb_red. auto. auto.  
eapply transitive_red. eapply2 Y4_fix.
unfold b_fn at 1.
eapply transitive_red. eapply preserves_app_sf_red. 
eapply2 star_opt_beta3. auto. 
unfold subst. rewrite ! subst_rec_preserves_extension. 
eapply transitive_red. 
eapply preserves_app_sf_red. auto.  
eapply transitive_red. eapply preserves_app_sf_red.
eapply2 app_comb_red.  auto.  
 eapply transitive_red. 
eapply preserves_app_sf_red.
eapply2 Y_k_red4. auto. 
eapply app_comb_red.  
 eapply transitive_red. 
eapply preserves_app_sf_red. auto. 
eapply2 a_op2_red. 
(* 1 *) 
eapply transitive_red.
eapply2 extensions_by_matchfail. 
eapply2 matchfail_app_comb_l. 
eapply2 matchfail_app_comb_l. 
eapply2 matchfail_app_comb_r.
eapply2 matchfail_program.
eapply2 h_fn_program.
split. eapply2 b_fn_normal. eapply2 b_fn_closed. 
assert(b_fn <> h_fn) by apply b_not_h.
intro. apply H. apply eq_sym. congruence.  auto. 
(* 1 *)    
eapply transitive_red. 
eapply2 extensions_by_matching.
eapply2 app_comb_matching.  
eapply2 app_comb_matching.
eapply2 app_comb_matching.
eapply2 app_comb_matching.
eapply2 program_matching. 
unfold program; split. 
eapply2 omega_k_normal. 
eapply2 omega_k_closed .
eapply2 program_matching. 
unfold program; split. 
eapply2 omega_k_normal. 
eapply2 omega_k_closed .
(* 1 *) 
rewrite ! pattern_size_app_comb. 
replace (pattern_size (omega_k 4)) with 0 by (rewrite pattern_size_closed; [auto| eapply2 omega_k_closed]). 
replace (pattern_size (h_fn)) with 0 . 
2: (rewrite pattern_size_closed; unfold h_fn; auto). 
unfold pattern_size. unfold plus. unfold length. unfold app, map, fold_left, subst. 
rewrite ! subst_rec_app. 
rewrite ! subst_rec_preserves_app_comb.
rewrite (subst_rec_closed (A_k _)) at 1.  2: rewrite A_k_closed; auto . 
rewrite (subst_rec_closed (A_k _)) at 1.  2: rewrite A_k_closed; auto . 
rewrite (subst_rec_closed (A_k _)) at 1.  2: rewrite A_k_closed; auto . 
rewrite (subst_rec_closed (A_k _)) at 1.  2: rewrite A_k_closed; auto . 
rewrite (subst_rec_closed (A_k _)) at 1.  2: rewrite A_k_closed; auto . 
rewrite (subst_rec_closed (A_k _)) at 1.  2: rewrite A_k_closed; auto . 
rewrite (subst_rec_closed (omega_k _)) at 1. 2: rewrite omega_k_closed; auto . 
rewrite (subst_rec_closed (omega_k _)) at 1. 2: rewrite omega_k_closed; auto . 
rewrite (subst_rec_closed (omega_k _)) at 1. 2: rewrite omega_k_closed; auto . 
rewrite (subst_rec_closed (omega_k _)) at 1. 2: rewrite omega_k_closed; auto . 
rewrite (subst_rec_closed (omega_k _)) at 1. 2: rewrite omega_k_closed; auto . 
rewrite (subst_rec_closed (omega_k _)) at 1. 2: rewrite omega_k_closed; auto . 
rewrite (subst_rec_closed (omega_k _)) at 1. 2: rewrite omega_k_closed; auto . 
rewrite (subst_rec_closed (omega_k _)) at 1. 2: rewrite omega_k_closed; auto . 
rewrite (subst_rec_closed (omega_k _)) at 1. 2: rewrite omega_k_closed; auto . 
rewrite (subst_rec_closed (omega_k _)) at 1. 2: rewrite omega_k_closed; auto . 
rewrite (subst_rec_closed (omega_k _)) at 1. 2: rewrite omega_k_closed; auto . 
rewrite (subst_rec_closed (omega_k _)) at 1. 2: rewrite omega_k_closed; auto . 
 rewrite subst_rec_ref at 1.  insert_Ref_out. 
 rewrite subst_rec_ref at 1.  insert_Ref_out. 
 rewrite subst_rec_ref at 1.  insert_Ref_out. 
 rewrite subst_rec_ref at 1.  insert_Ref_out. 
 rewrite subst_rec_ref at 1.  insert_Ref_out. 
 rewrite subst_rec_ref at 1.  insert_Ref_out. 
 rewrite subst_rec_ref at 1.  insert_Ref_out. 
 rewrite subst_rec_ref at 1.  insert_Ref_out. 
 rewrite subst_rec_ref at 1.  insert_Ref_out. 
 rewrite subst_rec_ref at 1.  insert_Ref_out. 
 rewrite subst_rec_ref at 1.  insert_Ref_out. 
 rewrite subst_rec_ref at 1.  insert_Ref_out. 
unfold lift. rewrite ! lift_rec_lift_rec; try omega.
unfold plus. rewrite ! subst_rec_lift_rec; try omega.
rewrite ! lift_rec_null. 
 rewrite ! subst_rec_ref.  insert_Ref_out. 
 rewrite ! subst_rec_ref.  insert_Ref_out. 
 rewrite ! subst_rec_ref.  insert_Ref_out. 
unfold lift. rewrite ! lift_rec_lift_rec; try omega.
unfold plus. 
rewrite ! subst_rec_lift_rec; try omega.
 rewrite ! subst_rec_ref.  insert_Ref_out. 
 rewrite ! subst_rec_ref.  insert_Ref_out. 
 rewrite ! subst_rec_ref.  insert_Ref_out. 
unfold lift; rewrite ! lift_rec_null.
auto. 
Qed. 


Lemma b_i_red: forall M N, sf_red (App (App (App b_op M) N) i_op) i_op. 
Proof.
intros; unfold_op. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red.
eapply2 app_comb_red. all: auto.
eapply transitive_red. eapply2 Y4_fix.
unfold b_fn, j_op. 
eapply transitive_red. eapply preserves_app_sf_red. 
eapply2 star_opt_beta3. auto. 
unfold subst. rewrite ! subst_rec_preserves_extension.
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail. 
unfold app_comb. 
eapply2 matchfail_compound_l.
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_op.
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail. 
unfold app_comb. 
eapply2 matchfail_compound_l.
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_op.
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail. 
unfold app_comb. 
eapply2 matchfail_compound_l.
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_op.
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail. 
unfold app_comb. 
eapply2 matchfail_compound_l.
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_op.
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail. 
unfold app_comb. 
eapply2 matchfail_compound_l.
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_op.
(* 1 *)
unfold_op. unfold subst_rec; fold subst_rec. 
repeat eval_tac. 
Qed. 
 