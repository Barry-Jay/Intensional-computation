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
(* 02110-1301 USA                                                     *)


(**********************************************************************)
(*                 Abstraction_Equal.v                                *)
(*                                                                    *)
(*                     Barry Jay                                      *)
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
Require Import IntensionalLib.Abstraction_calculus.Abstraction_Normal.


Ltac split_all := simpl; intros; 
match goal with 
| H : _ /\ _ |- _ => inversion_clear H; split_all
| H : exists _, _ |- _ => inversion H; clear H; split_all 
| _ =>  try (split; split_all); try contradiction
end; try congruence; auto.



Theorem equal_normal : forall M, normal M -> c_red (App (App (Op Eop) M) M) k_op.
Proof. 
  intros M nf; induction nf; split_all.
  eapply2 succ_red. eapply transitive_red. eapply preserves_app_c_red. eapply preserves_app_c_red.
eexact IHnf1.   eexact IHnf2. auto. unfold_op. one_step. 
Qed.


Theorem unequal_normal : forall M, normal M -> forall N, normal N -> M<>N ->
                                       c_red (App (App (Op Eop) M) N) (App k_op i_op).

Proof. 
  intros M nf; induction nf; split_all.
  (* 2 *)
  red; one_step. eapply2 e_op_factorable_red. unfold factorable; inversion H; eauto. 
  (* 1 *)
  inversion H0; subst. red; one_step. 
  eapply2 succ_red.  
  assert (M1 = M0 \/ M1 <> M0) by repeat decide equality. inversion H5; subst.
  assert(M2<> M3) by (intro; eapply2 H1; congruence). 
  (* 2 *)
  eapply transitive_red. eapply preserves_app_c_red. eapply preserves_app_c_red.
  eapply2 equal_normal. eapply2 IHnf2. auto. one_step.
  (* 1 *)
  eapply transitive_red. eapply preserves_app_c_red. eapply preserves_app_c_red.
  eapply2 IHnf1. auto. auto. eapply2 succ_red. 
Qed.

  