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
(*                    Tree_Normal.v                                   *)
(*                                                                    *)
(*                      Barry Jay                                     *)
(*                                                                    *)
(**********************************************************************)

Require Import Arith Omega Max.
Require Import IntensionalLib.SF_calculus.General.  
Require Import IntensionalLib.Tree_calculus.Tree_Terms.  
Require Import IntensionalLib.Tree_calculus.Tree_Tactics.  
Require Import IntensionalLib.Tree_calculus.Tree_reduction.  


Inductive status_val := 
| Active : status_val 
| Passive : status_val
.

Fixpoint status M := 
match M with 
| Ref _ => Active  
| Op _ => Passive
| App (App (App (Op Node) M1) _ ) _ => status M1 
| App M1 _ => status M1 
end. 

(* normal terms *) 

Inductive normal : Tree -> Prop := 
| nf_ref : forall n, normal (Ref n)
| nf_op : forall o, normal (Op o)
| nf_active : forall M1 M2, normal M1 -> normal M2 -> 
                              status (App M1 M2) = Active -> 
                              normal (App M1 M2)  
| nf_compound : forall M1 M2, normal M1 -> normal M2 -> 
                              compound (App M1 M2) -> normal (App M1 M2)
.

Hint Constructors normal. 




Definition irreducible M (red:termred) := forall N, red M N -> False. 

Lemma ref_irreducible : forall n, irreducible (Ref n) sf_seqred1. 
Proof. intro n. red. split_all. inversion H; auto. Qed. 

Lemma normal_is_irreducible: 
forall M, normal M -> irreducible M sf_seqred1. 
Proof. 
intros M nor; induction nor; split_all.  
(* 4 *)
eapply2 ref_irreducible. 
(* 3 *) 
red; split_all. inversion H.
(* 2 *) 
intro. intro. inversion H0; subst; simpl in *; try discriminate. 
(* 4 *) 
eapply2 IHnor1. 
(* 3 *) 
eapply2 IHnor2.
(* 1 *)
intro. intro. inversion H0; subst; simpl in *; try (inversion H; fail).
eapply2 IHnor1. 
eapply2 IHnor2. 
Qed. 


Theorem Tree_progress : forall (M : Tree), normal M \/ (exists N, sf_seqred1 M N) .
Proof. 
induction M; try (inversion IHM); subst; split_all; eauto.
(* 1 *)
inversion IHM1; split_all. 2: right; inversion H; exist (App x M2). 
inversion IHM2; split_all.  2:right; inversion H0; exist (App M1 x). 
gen_case H M1. case o; try (right; eauto; fail); left; auto.  
inversion H; subst.
(* 2 *) 
left; auto. 
eapply2 nf_active. gen_case H5 t. gen_case H5 t1. discriminate. 
(* 1 *) 
gen2_case H3 H5 t.
left; case o; auto. 
gen2_case H3 H5 t1. 
gen2_case H3 H5 o; try (right; eauto; fail). 
inversion H3; subst. inversion H8. 
inversion H7; subst. left; eapply2 nf_active. 
right; eauto. left; eapply2 nf_active. 
right; eauto. inversion H5. 
(* 2 *) 
inversion H9; subst; eauto.
(* 1 *) 
inversion H5. 
Qed. 

