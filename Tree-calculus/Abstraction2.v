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
(*                   Abstraction2.v                                   *)
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
Require Import IntensionalLib.Wave_as_SF.Abstraction.  

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
assert(P1 = s \/ P1 <> s).  repeat decide equality.
inversion H2; subst. 
eapply2 matchfail_compound_r.
inversion H. inversion H3. 
assert(status (App s P2) = Passive) by eapply2 closed_implies_passive. 
rewrite H9 in H10. 
congruence. auto.        
inversion H0. inversion H3. 
assert(status (App s s0) = Passive) by eapply2 closed_implies_passive. 
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
assert(status (App s s0) = Passive) by eapply2 closed_implies_passive. 
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
assert(status (App s s0) = Passive) by eapply2 closed_implies_passive. 
rewrite H6 in H10. 
congruence. 
unfold program; split. 
inversion H4; auto. simpl in *; max_out. 
Qed. 


Lemma star_mono: forall M N, star M = star N -> M = N. 
Proof. 
induction M; split_all. 
gen_case H n; split_all.
gen_case H N. 
gen_case H n0. 
inversion H. inversion H. inversion H. 
gen_case H2 s. 
gen_case H2 n0. 
discriminate . discriminate . discriminate.
discriminate.
gen_case H N. 
gen_case H n1. discriminate.
inversion H; subst. auto. discriminate. 
discriminate. 
gen_case H N. 
gen_case H n. discriminate. discriminate. 
inversion H; subst. auto. 
inversion H; subst . 
gen_case H N. 
gen_case H n. all: try discriminate. inversion H. 
gen_case H1 M2. gen_case H1 n0.  all: try discriminate. 
inversion H; subst. 
rewrite (IHM1 s); auto. rewrite (IHM2 s0); auto. 
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
unfold app_comb. 
eapply2 matchfail_compound_r.
eapply2 program_matching.
unfold_op; unfold program; split; auto. 
repeat eapply2 nf_compound. 
eapply2 matchfail_compound_r.
eapply2 match_app.
eapply2 match_app.
unfold_op; eapply2 match_app.
unfold_op. 
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
unfold_op; eapply2 program_matching. 
unfold_op; unfold program; split; auto. 
repeat eapply2 nf_compound. 
eapply2 matchfail_compound_r.
eapply2 match_app. 
eapply2 match_app. 
unfold_op; eapply2 match_app. 
unfold_op; eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
eapply2 program_matching.
unfold_op; unfold program; split; auto. 
repeat eapply2 nf_compound. 
eapply2 matchfail_compound_l.
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
unfold h_fn, omega_k. simpl.
eapply2 matchfail_compound_l.
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
unfold_op; eapply2 matchfail_compound_l.
(* 1 *)  
eapply transitive_red. 
eapply2 extensions_by_matchfail. 
unfold app_comb. 
eapply2 matchfail_compound_r.
eapply2 program_matching.
unfold_op; unfold program; split; auto. 
repeat eapply2 nf_compound. 
eapply2 matchfail_compound_r.
eapply2 match_app.
eapply2 match_app.
unfold_op; eapply2 match_app.
unfold_op. 
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
unfold_op; eapply2 program_matching. 
unfold_op; unfold program; split; auto. 
repeat eapply2 nf_compound. 
eapply2 matchfail_compound_r.
eapply2 match_app. 
eapply2 match_app. 
unfold_op; eapply2 match_app. 
unfold_op; eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
eapply2 program_matching.
unfold_op; unfold program; split; auto. 
repeat eapply2 nf_compound. 
eapply2 matchfail_compound_r.
eapply2 match_app. 
eapply2 match_app. 
eapply2 matchfail_compound_r.
unfold_op; eapply2 matchfail_compound_l. unfold_op. 
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
unfold_op; eapply2 matchfail_compound_l.
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
eapply2 matchfail_op. 
unfold factorable; split_all. 
discriminate. 
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matchfail. 
unfold app_comb. 
eapply2 matchfail_compound_r.
eapply2 program_matching.
unfold_op; unfold program; split; auto. 
repeat eapply2 nf_compound. 
eapply2 matchfail_compound_r.
unfold_op; repeat eapply2 match_app. 
unfold_op; eapply2 matchfail_compound_r.
unfold_op;  eapply2 matchfail_compound_r.
unfold_op; repeat eapply2 match_app. 
 eapply2 matchfail_compound_r.
unfold_op; repeat eapply2 match_app. 
unfold_op; eapply2 matchfail_compound_r.
unfold_op; eapply2 matchfail_compound_r.
unfold_op; repeat eapply2 match_app. 
 eapply2 matchfail_compound_l.
eapply2 matchfail_program. 
unfold program; split.
repeat eapply2 nf_compound.
rewrite ! maxvar_app. rewrite omega_k_closed. auto. 
unfold program; split.
repeat eapply2 nf_compound.
rewrite ! maxvar_app. rewrite omega_k_closed. auto. 
intro; inversion H. (* slow *) 
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
eapply transitive_red. 
eapply2 extensions_by_matchfail.
eapply2 matchfail_compound_r.
eapply2 program_matching.
unfold_op; unfold program; split; auto. 
repeat eapply2 nf_compound. 
eapply2 matchfail_compound_r.
eapply2 match_app.
eapply2 match_app.
unfold_op; eapply2 match_app.
unfold_op. 
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
eapply2 program_matching.
unfold_op; unfold program; split; auto. 
repeat eapply2 nf_compound. 
eapply2 matchfail_compound_r.
eapply2 match_app. 
eapply2 match_app. 
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
eapply2 program_matching.
unfold_op; unfold program; split; auto. 
repeat eapply2 nf_compound. 
unfold_op; eapply2 matchfail_compound_l.
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
(* 2 *) 
eapply2 matchfail_program.
unfold program; unfold h_fn; split; auto.
unfold_op; simpl; repeat eapply2 nf_compound. 
all: try (unfold_op; auto).
unfold subst; simpl; auto.
unfold program; split. eapply2 omega_k_normal. eapply2 omega_k_closed.
unfold omega_k, h_fn.  intro. inversion H. 
(* 1 *)
eapply transitive_red.
eapply2 extensions_by_matchfail. 
eapply2 matchfail_compound_r. 
repeat eapply2 match_app.
eapply2 matchfail_compound_r. 
repeat eapply2 match_app.
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r. 
repeat eapply2 match_app.
eapply2 matchfail_compound_r. 
repeat eapply2 match_app.
eapply2 matchfail_compound_r. 
repeat eapply2 match_app.
eapply2 matchfail_compound_r. 
repeat eapply2 match_app.
eapply2 matchfail_compound_r. 
repeat eapply2 match_app.
eapply2 matchfail_compound_r. 
repeat eapply2 match_app.
eapply2 matchfail_compound_l. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r. 
repeat eapply2 match_app.
unfold_op. unfold occurs0. 
rewrite ! orb_false_r.
unfold subst, subst_rec.  
eapply2 matchfail_compound_l.
(* 1 *) 
eapply transitive_red. 
eapply2 extensions_by_matching. 
eapply2 match_app.
repeat eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
repeat eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
repeat eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
repeat eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
repeat eapply2 match_app.
eapply2 program_matching. 
unfold program. split.  
repeat eapply2 nf_compound. 
repeat eapply2 maxvar_app.
(* 1 *) 
rewrite ! app_nil_r. 
rewrite ! app_nil_l.
unfold length; fold length. 
rewrite ! map_lift0. 
unfold fold_left.
unfold map.  unfold app. 
rewrite ! subst_rec_app.
unfold pattern_size.
rewrite ! pattern_size_closed. unfold plus. 
rewrite ! subst_rec_ref.  insert_Ref_out. 
unfold subst; rewrite ! subst_rec_app.
unfold lift; rewrite ! lift_rec_lift_rec; try omega. 
unfold plus. rewrite ! subst_rec_lift_rec; try omega. 
unfold subst_rec; fold subst_rec.  insert_Ref_out. 
unfold subst_rec; fold subst_rec.  insert_Ref_out. 
 unfold subst_rec; fold subst_rec.  insert_Ref_out. 
 unfold subst_rec; fold subst_rec.  insert_Ref_out. 
 unfold lift; rewrite ! lift_rec_null. auto. 
rewrite omega_k_closed. auto. 
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



Lemma b_a_red: 
forall M N P Q, program P -> program Q -> 
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
eapply2 matchfail_compound_r.
eapply2 program_matching.
unfold_op; unfold program; split; auto. 
repeat eapply2 nf_compound. 
eapply2 matchfail_compound_r.
eapply2 match_app.
eapply2 match_app.
unfold_op; eapply2 match_app.
unfold_op. 
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
eapply2 program_matching.
unfold_op; unfold program; split; auto. 
repeat eapply2 nf_compound. 
eapply2 matchfail_compound_r.
repeat eapply2 match_app. 
eapply2 matchfail_compound_r.
unfold ab_fn. 
rewrite star_opt_occurs_true. 
rewrite star_opt_occurs_true. 
rewrite (star_opt_occurs_true (App b_op _)). 
unfold star_opt at 6 5 3.  unfold occurs0. 
unfold_op. 
rewrite ! orb_false_l. 
all: cycle 1. 
unfold occurs0. rewrite orb_true_r. simpl; auto. 
congruence . 
unfold star_opt at 1. unfold occurs0. 
rewrite orb_true_r at 1. 
rewrite orb_true_r at 1. 
rewrite orb_true_r at 1. 
rewrite orb_true_l. auto. 
rewrite (star_opt_occurs_true (App b_op _)) at 1.
congruence. 
unfold occurs0. rewrite orb_true_r. simpl; auto. 
congruence . 
unfold occurs0. rewrite orb_true_r. simpl; auto. 
congruence . 
all: cycle -1. 
unfold star_opt at 3. 
rewrite occurs_closed. 
unfold subst; rewrite subst_rec_closed. 
unfold subst_rec. 
rewrite (star_opt_occurs_false (App
                    (App (Op Node)
                       (App (Op Node) (App (App (Op Node) (Op Node)) (Ref 1))))
                    b_op)). 
unfold subst_rec; fold subst_rec. 
rewrite subst_rec_closed.  insert_Ref_out. unfold pred.  
rewrite (star_opt_occurs_true).
all: cycle 1. 
unfold_op; simpl; auto. congruence.
rewrite ? b_op_closed; auto.
unfold occurs0. rewrite occurs_closed. auto. 
rewrite b_op_closed; auto.
rewrite b_op_closed; auto.
rewrite b_op_closed; auto.
(* 2 *) 
all: cycle 1. 
eapply2 matchfail_compound_l.  
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
rewrite star_opt_closed.
unfold_op; eapply2 matchfail_compound_l.
simpl; auto. 
(* 1 *)   (* B *) 
eapply transitive_red.
eapply2 extensions_by_matchfail. 
eapply2 matchfail_compound_r.
repeat eapply2 match_app. 
all: unfold_op; auto.  
eapply2 matchfail_compound_r.
repeat eapply2 match_app. 
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
repeat eapply2 match_app. 
eapply2 matchfail_compound_r.
repeat eapply2 match_app. 
eapply2 matchfail_compound_r.
unfold ab_fn.
(* 2 *) 
rewrite star_opt_occurs_true.
all: cycle 1 .
rewrite ! occurs_app. 
unfold occurs0 at 2.
rewrite orb_true_r. simpl . auto. congruence. 
all: cycle -1. 
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
(* 2 *) 
all: cycle -1.
rewrite (star_opt_occurs_true (App b_op (Ref 0))).
all: cycle 1. 
rewrite ! occurs_app.
unfold occurs0 at 2.
rewrite orb_true_r at 1. 
simpl . auto. congruence .
(* 2 *) 
all: cycle -1.
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
(* 1 *) (* R *) 
eapply transitive_red.
eapply2 extensions_by_matchfail.
eapply2 matchfail_compound_r. 
repeat eapply2 match_app. 
eapply2 matchfail_compound_r. 
repeat eapply2 match_app. 
eapply2 matchfail_compound_r. 
eapply2 matchfail_compound_r. 
repeat eapply2 match_app. 
eapply2 matchfail_compound_r. 
repeat eapply2 match_app. 
eapply matchfail_compound_r. auto.  auto. 
repeat eapply2 match_app. 
(* 2 *) 
unfold ab_fn.
rewrite star_opt_occurs_true.
all: cycle 1 .
rewrite ! occurs_app. 
unfold occurs0 at 2.
rewrite orb_true_r. simpl . auto. congruence. 
all: cycle -1. 
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
(* 2 *) 
all: cycle 1.
rewrite (star_opt_occurs_true (App b_op (Ref 0))).
all: cycle 1. 
rewrite ! occurs_app.
unfold occurs0 at 2.
rewrite orb_true_r at 1. 
simpl . auto. congruence .
(* 2 *) 
all: cycle -1.
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
(* 1 *) (* J , tricky to distinguish J from A *) 
eapply transitive_red.
eapply2 extensions_by_matchfail.
eapply2 matchfail_compound_r. 
repeat eapply2 match_app. 
eapply2 matchfail_compound_r. 
repeat eapply2 match_app. 
eapply2 matchfail_compound_r. 
unfold Y_k. 
eapply2 matchfail_compound_r. 
repeat eapply2 match_app.
all: unfold_op; auto.
assert(matchfail (omega_k 2) P \/ exists sigma, matching (omega_k 2) P sigma).
apply match_program. eapply2 omega_k_normal. auto. 
inversion H1.
(* 3 *) 
eapply matchfail_compound_l. auto.  auto.
eapply2 matchfail_compound_r. 
(* 2 *) 
inversion H2; subst. 
eapply2 matchfail_compound_r.
repeat eapply2 match_app.
(* 2 *) 
eapply2 matchfail_compound_r. 
(* 2 *) 
unfold ab_fn.
rewrite star_opt_occurs_true.
all: cycle 1 .
rewrite ! occurs_app. 
unfold occurs0 at 2.
rewrite orb_true_r. simpl . auto. congruence. 
all: cycle -1. 
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
(* 2 *) 
all: cycle 1.
rewrite (star_opt_occurs_true (App b_op (Ref 0))).
all: cycle 1. 
rewrite ! occurs_app.
unfold occurs0 at 2.
rewrite orb_true_r at 1. 
simpl . auto. congruence .
(* 2 *) 
all: cycle -1.
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
(* 1 *) (* A *) 
eapply transitive_red. 
eapply2 extensions_by_matching.
eapply2 match_app.
repeat eapply2 match_app.
eapply2 match_app.
repeat eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
repeat eapply2 match_app.
eapply2 match_app.
repeat eapply2 match_app.
(* 
eapply2 match_app.
unfold ab_fn.
unfold star_opt at 3.  unfold occurs0. unfold_op. 
rewrite ! orb_false_l; rewrite ! orb_true_l.
unfold star_opt at 2.  unfold occurs0. 
rewrite ! orb_false_l. 
unfold subst, subst_rec; fold subst_rec. insert_Ref_out. 
unfold subst, subst_rec; fold subst_rec. insert_Ref_out. 
 unfold pred. 
unfold_op. unfold star_opt at 1. unfold occurs0. rewrite ! orb_false_l. rewrite ! orb_true_l.
unfold_op; unfold subst, subst_rec.   
rewrite star_opt_occurs_true. 
2: rewrite ! occurs_app.  2: rewrite occurs_closed. 2: simpl; auto. 2: eapply2 b_op_closed. 2: congruence. 
rewrite (star_opt_occurs_true (App b_op _)). 
2: rewrite ! occurs_app. 2: rewrite occurs_closed.  2:  simpl; auto. 2: eapply2 b_op_closed. 2:congruence.
unfold star_opt at 5. 
rewrite occurs_closed. 2: eapply2 b_op_closed. 
unfold subst; rewrite subst_rec_closed. 2: rewrite b_op_closed; auto. 
unfold star_opt at 4 3. 
rewrite (star_opt_occurs_true  (App (Op Node) (App (Op Node) (App k_op (Ref 0))))).
2: simpl; unfold_op; simpl. 2: auto. 2: simpl; congruence .
rewrite (star_opt_occurs_false (App (App (Op Node) (App (Op Node) (App k_op (Ref 1)))) b_op)). 
2: rewrite ! occurs_app. 2: rewrite occurs_closed.  2: unfold_op. 
2: rewrite ! orb_false_l. 2: apply occurs_closed. 2: eapply2 b_op_closed. 2:auto. 
unfold_op; unfold subst_rec; fold subst_rec. 
rewrite subst_rec_closed. 2: rewrite b_op_closed; auto.
insert_Ref_out. unfold pred.
rewrite (star_opt_occurs_true (App (Op Node)
           (App (Op Node)
              (App (App (Op Node) (Op Node))
                 (App
                    (App (Op Node)
                       (App (Op Node) (App (App (Op Node) (Op Node)) (Ref 0))))
                    b_op))))).
eapply2 match_app. 
eapply2 match_app. 
eapply2 match_app.
rewrite star_opt_occurs_true.  2: simpl; auto. 2: congruence. 
unfold star_opt. unfold occurs0.  rewrite ! orb_false_l.   
unfold subst, subst_rec; unfold_op. 
repeat eapply2 match_app.
all: cycle 1. 
rewrite ! occurs_app. 
rewrite (occurs_closed b_op). simpl; auto. eapply2 b_op_closed. 
simpl; auto. discriminate .
all: cycle 1. 
rewrite star_opt_occurs_true.  2: simpl; auto. 2: congruence. 
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
unfold occurs0. 
eapply2 match_app.
eapply2 match_app. rewrite ! orb_false_l.  rewrite occurs_closed. 
rewrite orb_true_l. 
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
rewrite star_opt_closed.
eapply2 match_app.
eapply2 match_app.
unfold_op ; auto.
unfold_op; eapply2 match_app.
eapply2 b_op_closed. 
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
eapply2 match_app.
unfold subst, subst_rec. 
eapply2 match_app.
unfold_op; eapply2 match_app.
all: unfold_op. 
eapply2 match_app.
eapply2 match_app.
all: unfold subst, subst_rec. 
eapply2 match_app.
eapply2 b_op_closed. 
eapply2 match_app.
eapply2 match_app.
unfold_op; auto. 
all: unfold_op.
eapply2 match_app.(
* 1 *) 
rewrite ! app_nil_r. 
unfold length; fold length.
rewrite ! map_lift0. 
unfold map. 
unfold app; fold app. 
insert_Ref_out. 
unfold fold_left.
unfold subst; rewrite ! subst_rec_app.
rewrite ! subst_rec_op.
unfold pattern_size; fold pattern_size . unfold plus. 
unfold lift; rewrite lift_rec_lift_rec; try omega. 
rewrite (lift_rec_closed (ab_fn b_op)) at 1.  
rewrite (lift_rec_closed (ab_fn b_op)) at 1.
rewrite subst_rec_ref at 1. insert_Ref_out. 
rewrite subst_rec_ref at 1. insert_Ref_out. 
rewrite subst_rec_ref at 1. insert_Ref_out. 
rewrite subst_rec_ref at 1. insert_Ref_out. 
rewrite subst_rec_ref at 1. insert_Ref_out. 
rewrite subst_rec_ref at 1. insert_Ref_out. 
rewrite subst_rec_ref at 1. insert_Ref_out. 
rewrite subst_rec_ref at 1. insert_Ref_out. 
rewrite subst_rec_ref at 1. insert_Ref_out. 
rewrite subst_rec_ref at 1. insert_Ref_out. 
rewrite subst_rec_ref at 1. insert_Ref_out. 
rewrite subst_rec_ref at 1. insert_Ref_out. 
unfold lift. rewrite lift_rec_lift_rec; try omega.
rewrite ! lift_rec_null.  
rewrite  (subst_rec_closed (ab_fn b_op)) at 1. 
rewrite  (subst_rec_closed (ab_fn b_op)) at 1. 
rewrite  (subst_rec_closed (A_k _)) at 1. 
rewrite  (subst_rec_closed (A_k _)) at 1. 
rewrite  (subst_rec_closed (A_k _)) at 1. 
rewrite  (subst_rec_closed (A_k _)) at 1. 
rewrite  (subst_rec_closed (A_k _)) at 1. 
rewrite  (subst_rec_closed (A_k _)) at 1. 
all: try (rewrite A_k_closed; omega).   
rewrite lift_rec_lift_rec; try omega. 
unfold plus. 
rewrite ! subst_rec_lift_rec; try omega.
rewrite lift_rec_null. 
rewrite ! subst_rec_ref.  insert_Ref_out. 
rewrite ! subst_rec_ref.  insert_Ref_out. 
rewrite ! subst_rec_ref.  insert_Ref_out. 
rewrite ! subst_rec_ref.  insert_Ref_out. 
rewrite ! subst_rec_ref.  insert_Ref_out. 
rewrite ! subst_rec_ref.  insert_Ref_out. 
unfold lift; rewrite ! lift_rec_null.
rewrite subst_rec_lift_rec; try omega. 
rewrite lift_rec_null. 
all: cycle 1. 
unfold ab_fn. rewrite ! maxvar_star_opt. 
rewrite ! maxvar_app.  rewrite b_op_closed. cbv; auto. 
unfold ab_fn. rewrite ! maxvar_star_opt. 
rewrite ! maxvar_app.  rewrite b_op_closed. cbv; auto. 
unfold ab_fn. rewrite ! maxvar_star_opt. 
rewrite ! maxvar_app.  rewrite b_op_closed. cbv; auto. 
unfold ab_fn. rewrite ! maxvar_star_opt. 
rewrite ! maxvar_app.  rewrite b_op_closed. cbv; auto. 
(* 1 *) 
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
unfold h_fn. repeat eapply2 star_opt_normal. 
unfold app_comb. unfold_op; rewrite ! maxvar_app. 
rewrite ! omega_k_closed. simpl. auto. 
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

Hypothesis b_op_program: program (App (Op Node) (App (Op Node) (App (App (Op Node) (Op Node)) b_fn))) .
Hypothesis b_not_h: b_fn <> h_fn. 


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
eapply2 matchfail_compound_r.
eapply2 program_matching.
unfold_op; unfold program; split; auto. 
repeat eapply2 nf_compound. 
eapply2 matchfail_compound_r.
eapply2 match_app.
eapply2 match_app.
unfold_op; eapply2 match_app.
unfold_op. 
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
eapply2 program_matching.
unfold_op; unfold program; split; auto. 
repeat eapply2 nf_compound. 
eapply2 matchfail_compound_r.
repeat eapply2 match_app. 
eapply2 matchfail_compound_r.
eapply2 matchfail_compound_r.
eapply2 program_matching.
unfold_op; unfold program; split; auto. 
repeat eapply2 nf_compound. 
eapply2 matchfail_compound_l.
eapply2 matchfail_program. 
unfold program; split. 
eapply2 nf_compound. 
eapply2 nf_compound. 
eapply2 nf_compound. 
unfold h_fn. 
repeat eapply2 star_opt_normal. 
rewrite ! maxvar_app. unfold h_fn. 
rewrite ! maxvar_star_opt. auto. 
eapply2 b_op_program.
assert(b_fn <> h_fn) by apply b_not_h.

Lemma app_mono: forall M N P, App M N = App M P -> N = P. 
Proof.  split_all. inversion H. auto. Qed. 
  
intro. apply H. eapply app_mono. eapply app_mono.  eapply app_mono. apply eq_sym. eexact H0.

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
unfold pattern_size. unfold plus. unfold length. unfold app. unfold map. 
unfold fold_left, subst. 
rewrite ! subst_rec_app. 
rewrite ! subst_rec_preserves_app_comb.
rewrite (subst_rec_closed (omega_k _)) at 1. 
rewrite (subst_rec_closed (omega_k _)) at 1. 
rewrite (subst_rec_closed (omega_k _)) at 1. 
rewrite (subst_rec_closed (omega_k _)) at 1. 
rewrite (subst_rec_closed (omega_k _)) at 1. 
rewrite (subst_rec_closed (omega_k _)) at 1. 
rewrite (subst_rec_closed (omega_k _)) at 1. 
rewrite (subst_rec_closed (omega_k _)) at 1. 
rewrite (subst_rec_closed (omega_k _)) at 1. 
rewrite (subst_rec_closed (omega_k _)) at 1. 
rewrite (subst_rec_closed (omega_k _)) at 1. 
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
rewrite ! subst_rec_lift_rec; try omega.
 rewrite ! subst_rec_ref.  insert_Ref_out. 
 rewrite ! subst_rec_ref.  insert_Ref_out. 
 rewrite ! subst_rec_ref.  insert_Ref_out. 
unfold lift, plus. rewrite ! subst_rec_lift_rec; try omega.
all: try (rewrite omega_k_closed; auto). 
rewrite ! lift_rec_null.
rewrite (subst_rec_closed (A_k _)) at 1.
rewrite (subst_rec_closed (A_k _)) at 1.
rewrite (subst_rec_closed (A_k _)) at 1.
rewrite (subst_rec_closed (A_k _)) at 1.
rewrite (subst_rec_closed (A_k _)) at 1.
rewrite (subst_rec_closed (A_k _)) at 1.
rewrite subst_rec_closed. 
all : try (rewrite A_k_closed; omega). 
auto. 
rewrite omega_k_closed. auto. 
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
 