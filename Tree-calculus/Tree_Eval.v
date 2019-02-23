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
(*                     SF_Eval.v                                      *)
(*                                                                    *)
(*                      Barry Jay                                     *)
(*                                                                    *)
(**********************************************************************)

Require Import Arith Max.
Require Import IntensionalLib.SF_calculus.General.  
Require Import IntensionalLib.Wave_as_SF.SF_Terms.  
Require Import IntensionalLib.Wave_as_SF.SF_Tactics.  
Require Import IntensionalLib.Wave_as_SF.SF_reduction.  
Require Import IntensionalLib.Wave_as_SF.SF_Normal.  
Require Import IntensionalLib.Wave_as_SF.SF_Closed.  
Require Import IntensionalLib.Wave_as_SF.Substitution.  


Definition eval_app M N := 
match M with 
| App (App (Op Node) (Op Node)) M1  => M1
| App (App (Op Node) (App (Op Node) M1)) M2 => 
      App (App M2 N) (App M1 N)
| App (App (Op Node) (App (App (Op Node) M1) M2)) M3 => 
    App (App N M1) M2
| x => App x N
end.


Lemma eval_app_from_SF : forall M N, sf_red (App M N) (eval_app M N).
Proof. 
induction M; split_all. 
gen_case IHM1 M1. gen_case IHM1 s.  gen_case IHM1 o. 
gen_case IHM1 s0. 
(* 2 *) 
case o0; auto. red; one_step.
(* 1 *) 
case s1; split_all. 
(* 2 *) 
case o0; split_all. red; one_step. 
(* 1 *) 
case s3; split_all. case o0; split_all. red; one_step. 
Qed. 


Fixpoint eval0 (M: SF) :=
match M with 
| Ref i => Ref i 
| Op o => Op o
| App (Op Fop) M11 => App (Op Fop) (eval0 M11)
| App M1 M11 => eval_app (eval0 M1) M11
end. 

Lemma eval0_from_SF : forall M, sf_red M (eval0 M).
Proof. 
induction M; split_all.
eapply transitive_red. 
eapply preserves_app_sf_red. eapply2 IHM1. auto. 
eapply transitive_red. 
eapply2 eval_app_from_SF. 
case M1; split_all. 
case o; split_all. 
eapply preserves_app_sf_red. auto. eapply2 IHM2. 
Qed. 


Ltac eval_tac := unfold_op; 
match goal with 
| |-  sf_red ?M _ => red; eval_tac
| |-  multi_step sf_red1 ?M _ =>
  (apply transitive_red with (eval0 M); 
[eapply2 eval0_from_SF |  
  unfold eval0, eval_app;  unfold subst; split_all])
| _ => auto
end.


(* Boolean operations *) 

Definition not M := App (App M (App k_op i_op)) k_op.

Lemma not_true : sf_red (not k_op) (App k_op i_op).
Proof. unfold not; eval_tac. Qed. 

Lemma not_false : sf_red (not (App k_op i_op)) k_op.
Proof. eval_tac.  eval_tac.  Qed. 

Definition  iff M N := App (App M N) (not N). 

Lemma true_true : sf_red (iff k_op k_op) k_op. 
Proof. unfold iff; unfold not; eval_tac; split_all. Qed. 
Lemma true_false : sf_red (iff k_op (App k_op i_op)) (App k_op i_op). 
Proof. unfold iff; unfold not; eval_tac; split_all. Qed. 
Lemma false_true : sf_red (iff (App k_op i_op) k_op) (App k_op i_op). 
Proof. unfold iff; unfold not; eval_tac; eval_tac; eval_tac; eval_tac; split_all. Qed. 
Lemma false_false : sf_red (iff (App k_op i_op) (App k_op i_op)) k_op.
Proof. 
unfold iff, not. unfold_op. repeat eval_tac. Qed. 

