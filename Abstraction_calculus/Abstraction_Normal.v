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
(*                  Abstraction_Normal.v                              *)
(*                                                                    *)
(*                      Barry Jay                                     *)
(*                                                                    *)
(**********************************************************************)

(*
Add LoadPath ".." as IntensionalLib.
*) 

Require Import Arith.
Require Import IntensionalLib.SF_calculus.General.
Require Import IntensionalLib.Abstraction_calculus.Abstraction_Terms. 
Require Import IntensionalLib.Abstraction_calculus.Abstraction_Tactics.
Require Import IntensionalLib.Abstraction_calculus.Abstraction_Reduction.


Ltac split_all := simpl; intros; 
match goal with 
| H : _ /\ _ |- _ => inversion_clear H; split_all
| H : exists _, _ |- _ => inversion H; clear H; split_all 
| _ =>  try (split; split_all); try contradiction
end; try congruence; auto.

(* normal terms *) 

Inductive normal : Term -> Prop := 
| nf_op : forall o, normal (Op o)
| nf_compound : forall M1 M2, normal M1 -> normal M2 -> 
                              compound (App M1 M2) -> normal (App M1 M2)
.

Hint Constructors normal. 


Definition irreducible M (red:termred) := forall N, red M N -> False. 


Lemma normal_is_irreducible: 
forall M, normal M -> irreducible M c_red1. 
Proof. 
  intros M nor; induction nor; red; split_all; inv c_red1; inv1 compound; inv1 true_compound;
  subst;  try (eapply2 IHnor1; fail); try (eapply2 IHnor2; fail).
Qed.


(* 
The basic progress result, that all irreducible terms are normal.
 *) 

Theorem abstraction_progress : forall (M : Term), normal M \/ (exists N,c_red1 M N) .
Proof. 
induction M; try (inversion IHM); subst; split_all; eauto.
(* 1 *)
inversion IHM1; split_all.  2: right; exist (App x M2). 
inversion IHM2; split_all.  2: right; exist (App M1 x). 
gen_case H M1.
case o; split_all. right; eauto.
gen_case H t. inversion H; subst; case o; try (right; eauto; fail); try (left; eapply2 nf_compound; fail). 
gen_case H4 t0.
right. inversion H0; subst; eauto.
assert(o0=o1 \/ o0<> o1) by decide equality. 
inversion H1; subst; eauto.
exist (App k_op i_op). eapply2 e_op_factorable_red. unfold factorable; eauto. intro; subst.
invsub.
exist (App k_op i_op). eapply2 e_op_factorable_red. unfold factorable; eauto. intro; subst.
invsub.
right. inversion H0; subst; eauto.
exist (App k_op i_op). eapply2 e_compound_op_red. inversion H4; auto.
exist (App (App (App (App (Op Eop) (left_component (App t1 t2))) (left_component (App M0 M3)))
                      (App (App (Op Eop) (right_component (App t1 t2))) (right_component (App M0 M3))))
                 (App k_op i_op)). 
eapply2 e_compounds_red. inversion H4; auto. 
(* 1 *)
inversion H; subst. inversion H5; subst.
inversion H1; subst; try (left; eapply2 nf_compound; fail);try (right; eauto; fail). 
right; eauto.
inversion H3. inversion H8; subst; eauto. 
right; eauto. 
inversion H0; subst; eauto.
inversion H6; subst; eauto.
inversion H10; eauto. 
(* 1 *)
inv1 normal; subst; right; eauto.
Qed.
