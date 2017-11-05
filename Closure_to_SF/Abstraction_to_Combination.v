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

(*
Add LoadPath ".." as IntensionalLib.
*) 

Require Import Arith Omega Max Bool List.

Require Import IntensionalLib.Closure_calculus.Closure_calculus.

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
Require Import IntensionalLib.SF_calculus.Fixpoints.
Require Import IntensionalLib.SF_calculus.Extensions.
Require Import IntensionalLib.SF_calculus.Tagging.
Require Import IntensionalLib.SF_calculus.Adding.

Set Printing Depth 10000.

Fixpoint ref i := match i with 
| 0 => s_op 
| S i1 => App s_op (ref i1)
end. 

Fixpoint refs js := match js with 
| nil => s_op (* dummy value *) 
| j :: js1 => App (App s_op (ref j)) (refs js1)
end. 

Lemma ref_program: forall i, program (ref i). 
Proof. 
induction i; unfold program, ref; fold ref; unfold_op; split_all. 
inversion IHi. split; auto. 
Qed. 


Lemma refs_normal: forall js, normal (refs js). 
Proof. induction js; split_all. unfold_op; repeat eapply2 nf_compound. auto. 
unfold_op; apply nf_compound. eapply2 nf_compound.
eapply2 ref_program. auto. auto. 
 Qed. 

Lemma ref_monotonic: forall i j, ref i = ref j -> i = j. 
Proof. 
induction i; split_all; gen_case H j; split_all; try discriminate. 
inversion H; subst. assert (i = n) by eapply2 IHi. auto. 
Qed.

Lemma var_ref_program: forall i, program (var (ref i)). 
Proof. 
intros; split. unfold var. nf_out. eapply2 var_fix_normal. eapply2 ref_program. 
rewrite var_maxvar. eapply2 ref_program. 
Qed.

Hint Resolve ref_program var_ref_program. 



Fixpoint lambda_to_SF (t: lambda) := 
match t with 
| Closure_calculus.Ref i => var (ref i)
| Tag s t => tag (lambda_to_SF s) (lambda_to_SF t)
| Closure_calculus.App t u => App (lambda_to_SF t) (lambda_to_SF u) 
| Closure_calculus.Iop => i_op
| Add i u sigma => app_comb add (s_op2 (s_op2 (lambda_to_SF sigma) (ref i)) (lambda_to_SF u))
| Abs j js sigma t => abs (refs js) (s_op2 (lambda_to_SF sigma) (ref j))
                          (lambda_to_SF t) 
end.



Lemma lambda_to_SF_preserves_reduction: 
forall M N, seq_red1 M N -> sf_red (lambda_to_SF M) (lambda_to_SF N).
Proof.
intros M N r; induction r; unfold lambda_to_SF; fold lambda_to_SF.
(* 19 *) 
unfold tag. repeat eapply2 preserves_app_sf_red. 
(* 18 *) 
unfold tag. repeat eapply2 preserves_app_sf_red. 
(* 17 *) 
unfold add, s_op2; unfold_op. repeat eapply2 preserves_app_sf_red. 
(* 16 *) 
unfold add, s_op2; unfold_op. repeat eapply2 preserves_app_sf_red. 
(* 15 *) 
unfold abs, s_op2; unfold_op; repeat eapply2 preserves_app_sf_red. 
(* 14*) 
unfold abs, s_op2; unfold_op; repeat eapply2 preserves_app_sf_red. 
(* 13 *) 
split_all.  repeat eapply2 preserves_app_sf_red. 
(* 12 *) 
split_all.  repeat eapply2 preserves_app_sf_red. 
(* 11 *) 
split_all. apply var_red. 
(* 10 *) 
apply tag_red. 
(* 9 *)
unfold refs. eapply2 abs_red.
(* 8 *)
unfold refs; fold refs. apply abs_many_red. 
(* 7 *) 
repeat eval_tac. 
(* 6 *) 
eapply transitive_red. eapply2 app_comb_red. 
eapply2 add_red_var_equal. 
(* 5 *) 
eapply transitive_red. eapply2 app_comb_red. 
eapply2 add_red_var_unequal. 
intro. eapply2 H. eapply2 ref_monotonic.
(* 4 *)  
eapply transitive_red. eapply2 app_comb_red. 
eapply2 add_red_tag. 
(* 3 *) 
eapply transitive_red. eapply2 app_comb_red. 
eapply2 add_red_empty. 
(* 2 *)
eapply transitive_red. eapply2 app_comb_red. 
eapply2 add_red_add. 
(* 1 *) 
eapply transitive_red. eapply2 app_comb_red. 
eapply2 add_red_abs. 
Qed. 

Definition implies_red (red1 : lambda -> lambda -> Prop) (red2: termred) := 
forall M N, red1 M N -> red2(lambda_to_SF M) (lambda_to_SF N). 

Lemma implies_red_multi_step: forall red1 red2, implies_red red1  (multi_step red2) -> 
                                                implies_red (Closure_calculus.multi_step red1) (multi_step red2).
Proof. red. 
intros red1 red2 IR M N R; induction R; split_all. 
apply transitive_red with (lambda_to_SF N); auto. 
Qed. 

Lemma lambda_to_SF_preserves_seq_red: forall M N, Closure_calculus.seq_red M N -> sf_red (lambda_to_SF M) (lambda_to_SF N).
Proof. intros. eapply2 (implies_red_multi_step). red. apply lambda_to_SF_preserves_reduction.
Qed. 


Lemma lambda_to_SF_preserves_normal : forall M, Closure_calculus.normal M -> normal (lambda_to_SF M). 
Proof. 
intros M nf; induction nf; unfold lambda_to_SF; fold lambda_to_SF. 
eapply2 var_normal. eapply2 ref_program. 
eapply2 tag_normal. nf_out.  
apply app_comb_normal. eapply2 add_normal. 
unfold s_op2. unfold_op. eapply2 nf_compound. apply nf_compound. auto. 
apply nf_compound. apply nf_compound. auto. auto. auto. eapply ref_program. auto. auto. 
(* 1 *) 
unfold abs. apply app_comb_normal. apply app_comb_normal. apply app_comb_normal. apply app_comb_normal. 
auto. 
2: eapply refs_normal. 2: unfold_op; nf_out; auto.  2: apply ref_program. 2: auto. 
(* 1 *) 
apply abs_fn_normal. 
Qed. 



 