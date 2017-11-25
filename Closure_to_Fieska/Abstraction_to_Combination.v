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
(*                   Abstraction_to_Combination                       *)
(*                                                                    *)
(*                          Barry Jay                                 *)
(*                                                                    *)
(**********************************************************************)


Add LoadPath ".." as IntensionalLib.

Require Import Arith Omega Max Bool List.

Require Import IntensionalLib.Closure_calculus.Closure_calculus.

Require Import IntensionalLib.Fieska_calculus.Test.
Require Import IntensionalLib.Fieska_calculus.General.
Require Import IntensionalLib.Fieska_calculus.Fieska_Terms.
Require Import IntensionalLib.Fieska_calculus.Fieska_Tactics.
Require Import IntensionalLib.Fieska_calculus.Fieska_reduction.
Require Import IntensionalLib.Fieska_calculus.Fieska_Normal.
Require Import IntensionalLib.Fieska_calculus.Fieska_Closed.
Require Import IntensionalLib.Fieska_calculus.Substitution.
Require Import IntensionalLib.Fieska_calculus.Fieska_Eval.
Require Import IntensionalLib.Fieska_calculus.Star.
Require Import IntensionalLib.Fieska_calculus.Fixpoints.
Require Import IntensionalLib.Fieska_calculus.Extensions.
Require Import IntensionalLib.Closure_to_Fieska.Tagging.
Require Import IntensionalLib.Closure_to_Fieska.Adding.


Fixpoint ref i := match i with 
| 0 => s_op 
| S i1 => App s_op (ref i1)
end. 

Lemma ref_program: forall i, program (ref i). 
Proof. 
induction i; unfold program, ref; fold ref; unfold_op; split_all. 
inversion IHi. split; auto. 
Qed. 



Lemma ref_monotonic: forall i j, ref i = ref j -> i = j. 
Proof. 
induction i; split_all; gen_case H j; split_all; try discriminate. 
inversion H; subst. assert (i = n) by eapply2 IHi. auto. 
Qed.

Lemma var_ref_program: forall i, program (var (ref i)). 
Proof. 
intros; split. unfold var, app_comb. nf_out. eapply2 omega3_program. eapply2 omega3_program.
eapply2 var_fn_program. eapply2 ref_program. 
rewrite var_maxvar. eapply2 ref_program. 
Qed.

Hint Resolve ref_program var_ref_program. 



Fixpoint closure_to_fieska (t: lambda) := 
match t with 
| Closure_calculus.Ref i => var (ref i)
| Tag s t => tag (closure_to_fieska s) (closure_to_fieska t)
| Closure_calculus.App t u => App (closure_to_fieska t) (closure_to_fieska u) 
| Closure_calculus.Iop => i_op
| Add sigma i u => add (pair (pair (closure_to_fieska sigma) (ref i)) (closure_to_fieska u))
| Abs sigma j t => abs (closure_to_fieska sigma) (ref j) (closure_to_fieska t) 
end.




Theorem closure_to_fieska_preserves_normal : forall M, Closure_calculus.normal M -> normal (closure_to_fieska M). 
Proof. 
intros M nf; induction nf; unfold closure_to_fieska; fold closure_to_fieska. 
eapply2 var_normal. eapply2 ref_program. 
unfold tag, app_comb. eapply2 var_normal. nf_out; auto.   nf_out. eapply2 add_normal.
unfold pair; nf_out; auto.  eapply ref_program. 
unfold abs, star_opt_app_comb, app_comb. 
apply nf_compound. 2: nf_out; auto. 2: auto. 
apply nf_compound. auto. 2: auto. 
apply nf_compound. 2: nf_out; auto. 2:  apply ref_program. 2: auto. 
apply nf_compound. auto. 2: auto. 
apply nf_compound. auto. 2: auto. 
apply nf_compound. auto. 2: auto.
apply nf_compound. 2: apply add_fn_normal. 2: auto. 
apply nf_compound.  auto.  2: auto. 
apply nf_compound. apply nf_compound. auto. apply omega3_program. auto. 
  apply omega3_program. auto.  
Qed. 

Lemma matchfail_k_var : forall M N, matchfail (App k_op M) (var N). 
Proof.
intros; unfold var, app_comb; unfold_op.  
eapply2 matchfail_compound_l. 
eapply2 matchfail_op. right; eauto. discriminate. 
Qed. 


Lemma closure_to_fieska_preserves_red1: 
forall M N, seq_red1 M N -> sf_red (closure_to_fieska M) (closure_to_fieska N).
Proof.
intros M N r; induction r; unfold closure_to_fieska; fold closure_to_fieska.
(* 18 *) 
unfold tag. repeat eapply2 preserves_app_sf_red. 
(* 17 *) 
unfold tag. repeat eapply2 preserves_app_sf_red. 
(* 16 *) 
unfold add, pair; unfold_op. repeat eapply2 preserves_app_sf_red. 
(* 15 *) 
repeat eapply2 preserves_app_sf_red. 
(* 14 *) 
unfold add, pair; repeat eapply2 preserves_app_sf_red. 
(* 13 *) 
unfold add, pair; repeat eapply2 preserves_app_sf_red. 
(* 12 *) 
unfold abs; repeat eapply2 preserves_app_sf_red. 
(* 11 *) 
unfold abs; repeat eapply2 preserves_app_sf_red. 
(* 10 *) 
apply var_red. 
(* 9 *) 
apply tag_red. 
(* 8 *)
apply abs_red. 
(* 7 *) 
eval_tac. 
(* 6 *) 
apply add_red_var_equal. 
eapply2 ref_program. 
unfold app_comb; case j; unfold_op; split_all; unfold_op. 
eapply2 matchfail_compound_op. 
eapply2 matchfail_compound_l. 
case j; unfold_op; split_all; unfold_op. 
eapply2 matchfail_compound_op. 
eapply2 matchfail_compound_l.
(* 5 *) 
apply add_red_var_unequal. 
eapply2 ref_program. 
eapply2 ref_program. 
intro. eapply2 H. eapply2 ref_monotonic.
unfold app_comb; case j; unfold_op; split_all; unfold_op. 
eapply2 matchfail_compound_op. 
eapply2 matchfail_compound_l. 
case j; unfold_op; split_all; unfold_op. 
eapply2 matchfail_compound_op. 
eapply2 matchfail_compound_l.
(* 4 *) 
apply add_red_tag. 
(* 3 *) 
eapply transitive_red. apply add_red_empty.
eapply2 preserves_app_sf_red. 
eapply transitive_red. eapply fst_preserves_sf_red. 
eapply2 fst_red.  eapply2 fst_red.   
(* 2 *) 
apply add_red_add. 
(* 1 *) 
apply add_red_abs. 
Qed. 

Definition implies_red (red1 : lambda -> lambda -> Prop) (red2: termred) := 
forall M N, red1 M N -> red2(closure_to_fieska M) (closure_to_fieska N). 

Lemma implies_red_multi_step: forall red1 red2, implies_red red1  (multi_step red2) -> 
                                                implies_red (Closure_calculus.multi_step red1) (multi_step red2).
Proof. red. 
intros red1 red2 IR M N R; induction R; split_all. 
apply transitive_red with (closure_to_fieska N); auto. 
Qed. 

Theorem closure_to_fieska_preserves_reduction: forall M N, Closure_calculus.seq_red M N -> sf_red (closure_to_fieska M) (closure_to_fieska N).
Proof. intros. eapply2 (implies_red_multi_step). red. apply closure_to_fieska_preserves_red1.
Qed. 

