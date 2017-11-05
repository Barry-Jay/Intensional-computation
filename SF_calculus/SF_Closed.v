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
(*                      SF_Closed.v                                   *)
(*                                                                    *)
(*                      Barry Jay                                     *)
(*                                                                    *)
(**********************************************************************)


Require Import Arith Omega Max.
Require Import IntensionalLib.SF_calculus.General.  
Require Import IntensionalLib.SF_calculus.SF_Terms.  
Require Import IntensionalLib.SF_calculus.SF_Tactics.  
Require Import IntensionalLib.SF_calculus.SF_reduction.  
Require Import IntensionalLib.SF_calculus.SF_Normal.  

(* closed terms *) 


Fixpoint maxvar (M: SF) := 
match M with 
| Ref i => S i
| Op o  => 0
| App M1 M2 => max (maxvar M1) (maxvar M2)
end.


Lemma maxvar_app : forall M N, maxvar (App M N) = max (maxvar M) (maxvar N).
Proof. split_all. Qed.


Definition decreases  (rank: SF  -> nat) (red:termred):= 
forall M N, red M N -> rank M >= rank N.

Lemma decreases_multi_step: 
forall rank red, decreases rank red -> decreases rank (multi_step red). 
Proof. 
red. intros rank red D M N R;  induction R; split_all. 
assert(rank M >= rank N) by eapply2 D. 
assert(rank N >= rank P) by eapply2 IHR. 
omega. 
Qed. 

Lemma left_component_preserves_maxvar : forall M, compound M -> 
maxvar(left_component M) <= maxvar M. 
Proof. 
split_all.
inversion H; split_all; try omega; eapply2 max_is_max.
Qed. 


Lemma right_component_preserves_maxvar : forall M, compound M -> 
maxvar(right_component M) <= maxvar M. 
Proof. split_all. inversion H; split_all; try omega; eapply2 max_is_max. 
Qed. 

Ltac max_l := 
match goal with 
| |- max ?m ?n >= ?p => 
assert(max m n >= m) by eapply2 max_is_max; 
cut(m >= p); split_all; try omega
end. 
Ltac max_r := 
match goal with 
| |- max ?m ?n >= ?p => 
assert(max m n >= n) by eapply2 max_is_max; 
cut(n >= p); split_all; try omega
end. 

Lemma closed_implies_passive : forall M, maxvar M = 0 -> status M = Passive. 
Proof. 
rank_tac. induction p; intros. 
match goal with | H: 0>= rank ?M |- _ => 
assert(rank M >0) by eapply2 rank_positive; noway end . 
induction M; split_all. discriminate.
generalize IHM1 H H0; clear IHM1 H H0; case M1; intros; try (auto; omega). 
simpl in *. gen_case H0 (maxvar M2); omega.  
(* 1 *)
rewrite IHM1. 
gen2_case H H0 s; split_all. gen2_case H H0  s1; split_all.
 case o; split_all. apply IHp. omega. max_out. max_out. 
simpl in *. omega. simpl in *;  max_out. 
Qed. 

Lemma decreases_maxvar_sf_seqred1: decreases maxvar sf_seqred1.
(* 
forall M N, lamF_red1 M N -> maxvar N <= maxvar M. 
*) 
Proof. 
cut(forall M N, sf_seqred1 M N -> maxvar N <= maxvar M). 
split_all; red. 

intros M N R; induction R; split_all; eauto; try (repeat (eapply2 max_monotonic); fail); 
try omega; repeat (eapply2 max_max2); try (max_r; fail); try (repeat max_l; fail). 
(* 5 *) 
assert(max(maxvar M) (maxvar N) >= maxvar N) by max_r. 
assert(max (max (maxvar M) (maxvar N)) (maxvar P) >= (max (maxvar M) (maxvar N))) by max_l. 
omega. 
assert(max(maxvar M) (maxvar N) >= maxvar M) by max_l. omega. 
(* 2 *) 
max_l. max_l. eapply2 left_component_preserves_maxvar.
max_l. max_l. eapply2 right_component_preserves_maxvar.
Qed. 

Lemma decreases_maxvar_lamF_red : decreases maxvar sf_seqred.
Proof. eapply2 decreases_multi_step. eapply2 decreases_maxvar_sf_seqred1. Qed. 


Definition program M := normal M /\ maxvar M = 0. 



Lemma components_monotonic: 
forall M N, program M -> program N ->  
left_component M = left_component N -> 
right_component M = right_component N -> M = N. 
Proof. 
induction M; unfold program; split_all. 
(* 3 *) 
inversion H; noway.  inversion H0. 
gen4_case H3 H4 H1 H2 N; try discriminate.  
subst. simpl in *. unfold i_op in *. unfold s_op in *. 
inversion H3. simpl in *. discriminate. 
inversion H7. 
(* 1 *) 
subst. 
gen2_case H H0 N. inversion H0; noway.   unfold i_op in *. 
unfold s_op in *. inversion H. inversion H1; simpl in *. 
discriminate.  inversion H7. 
Qed. 


Definition factorable M := (exists o, M = Op o) \/ compound M.

Theorem programs_are_factorable : forall M, program M  -> factorable M. 
Proof. 
unfold program, factorable; induction M;  split_all; eauto.  
right. inversion H; omega. 
assert((exists o : operator, M1 = Op o) \/ compound M1). eapply2 IHM1. 
inversion H; simpl in *.  split; split_all. inversion H0; auto. 
max_out. 
(* 1 *) 
inversion H0; split_all; subst; eauto. 
inversion H1; try inv1 compound; subst. 
inversion H. inversion H2. simpl in *; discriminate. auto. 
(* 1 *) 
inversion H. inversion H2. 
inversion H1; subst; simpl in *; try discriminate.  
assert(status M = Passive). eapply2 closed_implies_passive. 
max_out. max_out. 
rewrite H4 in H8; discriminate. auto. 
Qed. 
