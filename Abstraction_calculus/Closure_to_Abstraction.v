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
(*                    Closure_to_Abstraction.v                        *)
(*                                                                    *)
(*                          Barry Jay                                 *)
(*                                                                    *)
(**********************************************************************)


Add LoadPath ".." as IntensionalLib.

Require Import Arith.
Require Import IntensionalLib.SF_calculus.General.
Require Import IntensionalLib.Closure_calculus.Closure_calculus. 
Require Import IntensionalLib.Abstraction_calculus.Abstraction_Terms. 
Require Import IntensionalLib.Abstraction_calculus.Abstraction_Tactics.
Require Import IntensionalLib.Abstraction_calculus.Abstraction_Reduction.
Require Import IntensionalLib.Abstraction_calculus.Abstraction_Normal.
Require Import IntensionalLib.Abstraction_calculus.Abstraction_Equal.

Ltac split_all := simpl; intros; 
match goal with 
| H : _ /\ _ |- _ => inversion_clear H; split_all
| H : exists _, _ |- _ => inversion H; clear H; split_all 
| _ =>  try (split; split_all); try contradiction
end; try congruence; auto.


Fixpoint ref i := match i with 
| 0 => Op (Sop) 
| S i1 => App (Op Sop) (ref i1)
end. 

Lemma ref_normal: forall i, normal (ref i). 
Proof. induction i; unfold ref; fold ref; unfold_op; split_all. Qed. 


Lemma ref_monotonic: forall i j, ref i = ref j -> i = j. 
Proof. 
induction i; split_all; gen_case H j; split_all; try discriminate. 
inversion H; subst. assert (i = n) by eapply2 IHi. auto. 
Qed.

Lemma var_ref_normal: forall i, normal (App (Op Var) (ref i)). 
Proof. split_all. eapply2 nf_compound. eapply2 ref_normal. Qed.

Hint Resolve ref_normal var_ref_normal. 



Fixpoint closure_to_abstraction (t: lambda) := 
match t with 
| Closure_calculus.Ref i => App (Op Var) (ref i)
| Closure_calculus.Tag s t => App (App (Op Tag) (closure_to_abstraction s)) (closure_to_abstraction t)
| Closure_calculus.App t u => App (closure_to_abstraction t) (closure_to_abstraction u) 
| Closure_calculus.Iop => Op Iop
| Closure_calculus.Add sigma i u => App (App (App (Op Add) (closure_to_abstraction sigma)) (ref i)) (closure_to_abstraction u)
| Closure_calculus.Abs sigma j t => App (App (App (Op Abs) (closure_to_abstraction sigma)) (ref j)) (closure_to_abstraction t)
end.


Lemma closure_to_abstraction_preserves_red1: forall M N, seq_red1 M N -> c_red (closure_to_abstraction M) (closure_to_abstraction N).
Proof.
intros M N r; induction r; split_all. 
(* 2 *)
eapply2 succ_red. eapply transitive_red. eapply preserves_app_c_red. eapply preserves_app_c_red. 
eapply2 equal_normal. auto. auto. one_step.
(* 1 *)
eapply2 succ_red. eapply transitive_red. eapply preserves_app_c_red. eapply preserves_app_c_red. 
eapply2 unequal_normal. intro. eapply2 H. eapply2 ref_monotonic. auto. auto.
eapply2 succ_red.
Qed.


Definition implies_red (red1 : lambda -> lambda -> Prop) (red2: termred) := 
forall M N, red1 M N -> red2(closure_to_abstraction M) (closure_to_abstraction N). 

Lemma implies_red_multi_step: forall red1 red2, implies_red red1  (multi_step red2) -> 
                                                implies_red (Closure_calculus.multi_step red1) (multi_step red2).
Proof. red. 
intros red1 red2 IR M N R; induction R; split_all. 
apply transitive_red with (closure_to_abstraction N); auto. 
Qed. 

Theorem closure_to_abstraction_preserves_reduction: forall M N, Closure_calculus.seq_red M N -> c_red (closure_to_abstraction M) (closure_to_abstraction N).
Proof. intros. eapply2 (implies_red_multi_step). red. apply closure_to_abstraction_preserves_red1.
Qed. 


Theorem closure_to_abstraction_preserves_normal : forall M, Closure_calculus.normal M -> normal (closure_to_abstraction M). 
Proof. intros M nf; induction nf; split_all.  Qed. 

