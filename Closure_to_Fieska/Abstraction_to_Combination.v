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
Require Import IntensionalLib.Fieska_calculus.Tagging.
Require Import IntensionalLib.Fieska_calculus.Adding.


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
intros; split. unfold var. nf_out. eapply2 ref_program. 
rewrite var_maxvar. eapply2 ref_program. 
Qed.

Hint Resolve ref_program var_ref_program. 



Fixpoint lambda_to_fieska (t: lambda) := 
match t with 
| Closure_calculus.Ref i => var (ref i)
| Tag s t => tag (lambda_to_fieska s) (lambda_to_fieska t)
| Closure_calculus.App t u => App (lambda_to_fieska t) (lambda_to_fieska u) 
| Closure_calculus.Iop => i_op
| Add sigma i u => App (App (Op Aop) 
                            (App (App (Op Aop) add) (s_op2 (lambda_to_fieska  sigma) (ref i))))
                       (lambda_to_fieska   u)
| Abs sigma j t => abs (lambda_to_fieska   sigma) (ref j) (lambda_to_fieska   t) 
end.



Lemma lambda_to_Fieska_preserves_reduction: 
forall M N, seq_red1 M N -> sf_red (lambda_to_fieska M) (lambda_to_fieska N).
Proof.
intros M N r; induction r; unfold lambda_to_fieska; fold lambda_to_fieska.
(* 18 *) 
unfold tag. repeat eapply2 preserves_app_sf_red. 
(* 17 *) 
unfold tag. repeat eapply2 preserves_app_sf_red. 
(* 16 *) 
unfold add, s_op2; unfold_op. repeat eapply2 preserves_app_sf_red. 
(* 15 *) 
unfold add, s_op2; unfold_op. repeat eapply2 preserves_app_sf_red. 
(* 14 *) 
unfold abs, s_op2; unfold_op; repeat eapply2 preserves_app_sf_red. 
(* 13*) 
unfold abs, s_op2; unfold_op; repeat eapply2 preserves_app_sf_red. 
(* 12 *) 
split_all.  repeat eapply2 preserves_app_sf_red. 
(* 11 *) 
split_all.  repeat eapply2 preserves_app_sf_red. 
(* 10 *) 
split_all. apply var_red. 
(* 9 *) 
apply tag_red. 
(* 8 *)
eapply2 abs_red.
(* 7 *) 
repeat eval_tac. 
(* 6 *) 
eval_tac. eval_tac. eapply2 add_red_var_equal. 
(* 5 *) 
eval_tac. eval_tac.  eapply2 add_red_var_unequal. 
intro. eapply2 H. eapply2 ref_monotonic.
(* 4 *)  
eval_tac. eval_tac. eapply2 add_red_tag. 
(* 3 *) 
eval_tac. eval_tac. eapply2 add_red_empty. 
(* 2 *)
eval_tac. eval_tac. eapply2 add_red_add. 
(* 1 *) 
eval_tac. eval_tac. eapply2 add_red_abs. 
Qed. 

Definition implies_red (red1 : lambda -> lambda -> Prop) (red2: termred) := 
forall M N, red1 M N -> red2(lambda_to_fieska M) (lambda_to_fieska N). 

Lemma implies_red_multi_step: forall red1 red2, implies_red red1  (multi_step red2) -> 
                                                implies_red (Closure_calculus.multi_step red1) (multi_step red2).
Proof. red. 
intros red1 red2 IR M N R; induction R; split_all. 
apply transitive_red with (lambda_to_fieska N); auto. 
Qed. 

Lemma lambda_to_fieska_preserves_seq_red: forall M N, Closure_calculus.seq_red M N -> sf_red (lambda_to_fieska M) (lambda_to_fieska N).
Proof. intros. eapply2 (implies_red_multi_step). red. apply lambda_to_Fieska_preserves_reduction.
Qed. 


Lemma lambda_to_fieska_preserves_normal : forall M, Closure_calculus.normal M -> normal (lambda_to_fieska M). 
Proof. 
intros M nf; induction nf; unfold lambda_to_fieska; fold lambda_to_fieska. 
eapply2 var_normal. eapply2 ref_program. 
eapply2 tag_normal. nf_out.  
nf_out; auto. apply add_normal. unfold s_op2; nf_out; auto.  eapply2 ref_program. 
(* 1 *) 
unfold abs, swap, s_op2. nf_out. apply add_normal. eapply2 ref_program.  
Qed. 



 