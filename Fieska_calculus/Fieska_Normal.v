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
(*                    Fieska_Normal.v                                 *)
(*                                                                    *)
(*                      Barry Jay                                     *)
(*                                                                    *)
(**********************************************************************)

Require Import Arith Omega Max Bool List.
Require Import IntensionalLib.Fieska_calculus.Test.
Require Import IntensionalLib.Fieska_calculus.General.
Require Import IntensionalLib.Fieska_calculus.Fieska_Terms.
Require Import IntensionalLib.Fieska_calculus.Fieska_Tactics.
Require Import IntensionalLib.Fieska_calculus.Fieska_reduction.

Inductive status_val := 
| Active : status_val 
| Passive : status_val
.

Fixpoint status M := 
match M with 
| Ref _ => Active  
| Op _ => Passive
| App (App (App (Op Fop) M1) _ ) _ => status M1 
| App (App (Op Eop) M1) M2  => match status M1 with Active => Active | _ => status M2 end
| App M1 _ => status M1 
end. 

(* normal terms *) 

Inductive normal : Fieska -> Prop := 
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
eapply2 ref_irreducible. 
red; split_all. inversion H. 
intro. intro. inversion H0; subst; simpl in *; try discriminate. 
(* 7 *) 
eapply2 IHnor1. 
(* 6 *) 
eapply2 IHnor2. 
(* 5 *) 
gen2_case H4 H P; subst; inv1 compound; subst; split_all; discriminate.  
(* 4 *) 
gen2_case H4 H M2; subst; inv1 compound; subst; split_all; discriminate.  
(* 3 *) 
gen2_case H4 H M; subst; inv1 compound; subst; split_all; discriminate.  
(* 2 *) 
gen2_case H3 H M; subst; inv1 compound; subst; split_all; discriminate.  
(* 1 *) 
intro. intro. inversion H0; subst; simpl in *; try (inversion H; fail).
eapply2 IHnor1. 
eapply2 IHnor2. 
Qed. 


Theorem Fieska_progress : forall (M : Fieska), normal M \/ (exists N, sf_seqred1 M N) .
Proof. 
induction M; try (inversion IHM); subst; split_all; eauto.
(* 1 *)
inversion IHM1; split_all. 2: right; inversion H; exist (App x M2). 
inversion IHM2; split_all. 2: right; inversion H0; exist (App M1 x). 
gen_case H M1. case o; try (right; eauto; fail); left; auto.  
inversion H; subst.
(* 2 *) 
left; auto. 
eapply2 nf_active. gen_case H5 f. discriminate.  gen_case H5 f1. gen_case H5 o.
discriminate.  
(* 1 *) 
gen2_case H3 H5 f.
gen2_case H3 H5 o; try (right; eauto; fail); try (left; auto; fail).  
inversion H4; subst; try (right; eauto; fail); try (left; auto; fail). 
inversion H0; subst; try (right; eauto; fail); try (left; auto; fail). 
right. assert(o0 = o1 \/ o0 <> o1) by decide equality. 
inversion H1; subst; eauto. 
left. eapply2 nf_active. simpl in *. rewrite H6. auto. 
inversion H0; subst; try (left; auto; fail); try (right; eauto; fail). 
left; eapply2 nf_active. inversion H6; simpl; auto. 
left; eapply2 nf_active. inversion H6; simpl; auto. 
inversion H5; subst; try (right;  eauto; fail). 
inversion H3; subst; inversion H7; subst; try (right;  eauto; fail); try (left; auto; fail). 
Qed. 

