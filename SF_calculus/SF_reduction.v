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
(*                   SF_reduction.v                                   *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)


Require Import Arith Omega.
Require Import IntensionalLib.SF_calculus.Test.  
Require Import IntensionalLib.SF_calculus.General.  
Require Import IntensionalLib.SF_calculus.SF_Terms.  
Require Import IntensionalLib.SF_calculus.SF_Tactics.  

Definition s_op := Op Sop.
Definition f_op := Op Fop.
Definition k_op := App f_op f_op. 
Definition i_op := App (App s_op k_op) k_op.
Ltac unfold_op := unfold i_op, k_op, f_op, s_op. 


(* compounds *) 

Fixpoint right_component (M : SF) := 
match M with 
| App _ M2 => M2
| _ => M
end.

Definition left_component (U : SF) := 
match U with 
| App U1 _ => U1 
| _ => i_op
end.

Lemma rank_component_app_l: 
forall M N, rank (left_component (App M N)) < rank (App M N). 
Proof. split_all; omega. Qed. 

Lemma rank_component_app_r: 
forall M N, rank (right_component (App M N)) < rank (App M N). 
Proof. split_all; omega. Qed. 


Inductive compound : SF -> Prop := 
| S1_compound : forall M, compound (App (Op Sop) M)
| S2_compound : forall M N, compound (App (App (Op Sop) M) N)
| F1_compound : forall M, compound (App (Op Fop) M)
| F2_compound : forall M N, compound (App (App (Op Fop) M) N)
.

Hint Constructors compound. 


Lemma rank_compound_l : forall M, compound M -> 
rank (left_component M) < rank M. 
Proof. 
split_all. inversion H; subst;  
eapply2 rank_component_app_l ||
split_all. 
Qed. 

Lemma rank_compound_r : forall M, compound M -> 
rank (right_component M) < rank M. 
Proof. 
split_all. inversion H; subst;  
eapply2 rank_component_app_r || 
inv1 compound.
Qed. 


Definition preserves_compound (red:termred) := 
forall M, compound M -> forall N, red M N -> 
compound N /\ red (left_component M) (left_component N) /\ red(right_component M) (right_component N).


Lemma preserves_compound_multi_step : 
forall (red:termred), preserves_compound red -> preserves_compound (multi_step red). 
Proof. 
red. intros red p M c N R; induction R; split_all. repeat split. 
eapply2 IHR. eapply2 p.
apply succ_red with (left_component N); auto. 
 eapply2 p. eapply2 IHR. eapply2 p.
apply succ_red with (right_component N); auto. 
 eapply2 p. eapply2 IHR. eapply2 p.
Qed. 

Hint Resolve preserves_compound_multi_step.



(* SF-reduction  *) 


Inductive sf_red1 : termred :=
  | ref_sf_red : forall i, sf_red1 (Ref i) (Ref i)
  | op_sf_red : forall o, sf_red1 (Op o) (Op o)
  | app_sf_red :
      forall M M' ,
      sf_red1 M M' ->
      forall N N' : SF, sf_red1 N N' -> sf_red1 (App M N) (App M' N')  
  | s_red: forall (M M' N N' P P' : SF),
             sf_red1 M M' -> sf_red1 N N' -> sf_red1 P P' ->                  
             sf_red1 
                   (App (App (App (Op Sop) M) N) P) 
                  (App (App M' P') (App N' P'))
  | f_op_red : forall M  M' N o,  sf_red1 M M' -> 
               sf_red1 (App (App (App (Op Fop) (Op o)) M) N) M' 
  | f_compound_red: forall (P P' M N N': SF), compound P -> 
             sf_red1 P P' -> sf_red1 N N' -> 
             sf_red1 (App (App (App (Op Fop) P) M) N)
                     (App (App N' (left_component P')) (right_component P'))  
.
 

Hint Constructors sf_red1. 


Definition sf_red := multi_step sf_red1. 

Lemma reflective_sf_red1 : reflective sf_red1.
Proof. red; induction M; split_all. Qed. 
Hint Resolve reflective_sf_red1. 

Lemma reflective_sf_red : reflective sf_red.
Proof. unfold sf_red; eapply2 refl_multi_step. Qed. 
Hint Resolve reflective_sf_red. 



Lemma preserves_app_sf_red : preserves_app sf_red.
Proof. eapply2 preserves_app_multi_step. red; split_all. Qed.
Hint Resolve  preserves_app_sf_red. 



Lemma  preserves_compound_sf_red1: 
forall M, compound M -> forall N, sf_red1 M N -> 
compound N /\ 
sf_red1 (left_component M) (left_component N) /\ 
sf_red1(right_component M) (right_component N). 
Proof. induction M; split_all; inv1 compound; subst; inv sf_red1. Qed. 

Hint Resolve preserves_compound_sf_red1 .

Lemma  preserves_compound_sf_red: preserves_compound sf_red.
Proof. 
eapply2 preserves_compound_multi_step. 
split_all; split; eapply2 preserves_compound_sf_red1. 
Qed.
Hint Resolve preserves_compound_sf_red .


Ltac app_op := unfold_op; 
match goal with 
| |- sf_red _ _ => red; app_op
| |- multi_step sf_red1 (Op _) (Op _) => red; one_step; app_op
| |- multi_step sf_red1 (App _ _) (App _ _) => eapply2 preserves_app_sf_red ; app_op
| |- multi_step sf_red1 (left_component _) (left_component _) => eapply2 preserves_compound_sf_red; app_op 
| |- multi_step sf_red1 (right_component _) (right_component _) => eapply2 preserves_compound_sf_red; app_op
| |- sf_red1 (App _ _) (App _ _) => eapply2 app_sf_red ; app_op
| |- sf_red1 (left_component _) (left_component _) => eapply2 preserves_compound_sf_red1; app_op 
| |- sf_red1 (right_component _) (right_component _) => eapply2 preserves_compound_sf_red1; app_op
| H : sf_red1 _ _ |- compound _ => eapply2 preserves_compound_sf_red1
| |- sf_red1 (left_component _) _ => eapply2 preserves_compound_sf_red1
| |- sf_red1 (right_component _) _ => eapply2 preserves_compound_sf_red1
| _ => try red; split_all
end.




Ltac sf_red_compound := 
fold sf_red in *; 
match goal with 
| H : sf_red   (App (App (Op ?o) ?M1) ?M2) ?N |- _ => 
assert(sf_red  (right_component (App (App (Op o) M1) M2))
          (right_component N)) by 
eapply2 preserves_compound_sf_red;
assert(sf_red  (left_component (App (App (Op o) M1) M2))
          (left_component N)) by 
eapply2 preserves_compound_sf_red; simpl in *; clear H; sf_red_compound
| H : sf_red (App (Op ?o) ?M1) ?N  |- _ => 
assert(sf_red  (right_component (App (Op o) M1))
          (right_component N)) by 
eapply2 preserves_compound_sf_red; clear H; sf_red_compound
| _ => simpl in *
end;
simpl in *.


(* Diamond Lemmas *) 


Lemma diamond_sf_red1_sf_red1 : diamond sf_red1 sf_red1. 
Proof.  
red; intros M N OR; induction OR; split_all; eauto.

(* 4 subgoals *)
inversion H; clear H; subst; inv sf_red1; inv sf_red1; eauto. 

(* 7 subgoals *) 
elim(IHOR1 M'0); elim(IHOR2 N'0); split_all; 
inversion H; inversion H0; eauto.
(* 6 *)
unfold s_op in *. elim(IHOR1 (App (App s_op M'0) N'0)); 
elim(IHOR2 P'); split_all;
inversion H; inversion H0; eauto. inv sf_red1. 
invsub. exist(App (App N'4 x) (App N'3 x)). 
(* 5 *) 
elim (IHOR1 (App (App (Op Fop) (Op o)) P)); split_all. 
inversion H. inv sf_red1. invsub. exist N'1. 
(* 4 *) 
elim (IHOR1 (App (App (Op Fop) P') N'1)); elim (IHOR2 N'0); 
split_all;  inversion H; inversion H0; eauto. 
inv sf_red1.  invsub. 
exist(App (App x (left_component N'4)) (right_component N'4)). 
split. 
eapply2 f_compound_red. 
eapply2 preserves_compound_sf_red1. 
app_op. 
(* 3 *)  
inversion H; subst. clear H. inv sf_red1. 
elim(IHOR1 N'2); elim(IHOR2 N'1); elim(IHOR3 N'0); split_all. 
inversion H; inversion H0; inversion H1. 
exist (App (App x1 x) (App x0 x)). 
elim(IHOR1 M'0); elim(IHOR2 N'0); elim(IHOR3 P'0); split_all. 
inversion H0; inversion H1; inversion H2. 
exist (App (App x1 x) (App x0 x)).
(* 2 *) 
inversion H; subst. clear H. inv sf_red1. 
elim(IHOR N'0); split_all. inversion H. 
exist x.
elim(IHOR P); split_all. inversion H3. 
(* 1 *)  
inversion H0; subst; clear H0; inv sf_red1. 
elim(IHOR1 N'2); elim(IHOR2 N'0); split_all. 
inversion H0; inversion H1. 
exist(App (App x (left_component x0)) (right_component x0)). split. 
eapply2 app_sf_red. eapply2 app_sf_red. eapply2 preserves_compound_sf_red1. 
eapply2 preserves_compound_sf_red1. 
eapply2 preserves_compound_sf_red1. 
eapply2 preserves_compound_sf_red1. 
eapply2 f_compound_red. 
eapply2 preserves_compound_sf_red1. 
 inv1 compound.
elim(IHOR1 P'0); elim(IHOR2 N'0); split_all. 
inversion H0; inversion H1. 
exist(App (App x (left_component x0)) (right_component x0)). split. 
eapply2 app_sf_red. eapply2 app_sf_red. eapply2 preserves_compound_sf_red1. 
eapply2 preserves_compound_sf_red1. 
eapply2 preserves_compound_sf_red1. 
eapply2 preserves_compound_sf_red1. 
eapply2 app_sf_red. eapply2 app_sf_red. eapply2 preserves_compound_sf_red1. 
eapply2 preserves_compound_sf_red1. 
eapply2 preserves_compound_sf_red1. 
eapply2 preserves_compound_sf_red1. 
Qed. 


Hint Resolve diamond_sf_red1_sf_red1.

Lemma diamond_sf_red1_sf_red : diamond sf_red1 sf_red.
Proof. eapply2 diamond_strip. Qed. 

Lemma diamond_sf_red : diamond sf_red sf_red.
Proof.  eapply2 diamond_tiling. Qed. 
Hint Resolve diamond_sf_red.


(* Confluence *)

Definition confluence (A : Set) (R : A -> A -> Prop) :=
  forall x y : A,
  R x y -> forall z : A, R x z -> exists u : A, R y u /\ R z u.

Theorem confluence_sf_red: confluence SF sf_red. 
Proof. red; split_all; eapply2 diamond_sf_red. Qed. 


(* SF-sequential-reduction *) 

Inductive sf_seqred1 : SF -> SF -> Prop := 
  | appl_sf_seqred :  forall M M' N, sf_seqred1 M M' -> 
                                      sf_seqred1 (App M N) (App M' N)  
  | appr_sf_seqred :  forall M N N', sf_seqred1 N N' -> 
                                      sf_seqred1 (App M N) (App M N')  
  | s_sf_seqred: forall (M N P : SF),
             sf_seqred1 
                   (App (App (App (Op Sop) M) N) P) 
                  (App (App M P) (App N P))
  | f_op_sf_seqred : forall M N o,  
               sf_seqred1 (App (App (App (Op Fop) (Op o)) M) N) M 
  | f_compound_sf_seqred : forall (P M N: SF), compound P -> 
             sf_seqred1 (App (App (App f_op P) M) N) 
                     (App (App N (left_component P)) (right_component P))
.

Definition sf_seqred := multi_step sf_seqred1. 

Hint Constructors sf_seqred1 .


Lemma reflective_sf_seqred: reflective sf_seqred. 
Proof. red; red; reflect. Qed. 
Hint Resolve reflective_sf_seqred.


Definition preserves_apl (red : termred) := 
forall M M' N, red M M' -> red (App M N) (App M' N).

Definition preserves_apr (red : termred) := 
forall M N N', red N N' -> red (App M N) (App M N').

Lemma preserves_apl_multi_step : forall (red: termred), preserves_apl red -> preserves_apl (multi_step red). 
Proof. red. induction 2; split_all. apply succ_red with (App N0 N); auto. Qed. 

Lemma preserves_apr_multi_step : forall (red: termred), preserves_apr red -> preserves_apr (multi_step red). 
Proof. red. induction 2; split_all. apply succ_red with (App M N); auto. Qed. 


Lemma preserves_apl_sf_seqred: preserves_apl sf_seqred. 
Proof. eapply2 preserves_apl_multi_step. red; split_all.  Qed.
Hint Resolve preserves_apl_sf_seqred.

Lemma preserves_apr_sf_seqred: preserves_apr sf_seqred. 
Proof. eapply2 preserves_apr_multi_step. red; split_all.  Qed.
Hint Resolve preserves_apr_sf_seqred.

Lemma preserves_app_sf_seqred: preserves_app sf_seqred. 
Proof. 
red; split_all. 
apply transitive_red with (App M' N); split_all. 
eapply2 preserves_apl_sf_seqred. 
eapply2 preserves_apr_sf_seqred. 
Qed. 
Hint Resolve preserves_app_sf_seqred.

Lemma preserves_compound_sf_seqred1: forall M N : SF,
   sf_seqred1 M N ->
   compound M ->
   compound N /\
   sf_seqred (left_component M) (left_component N) /\
   sf_seqred (right_component M) (right_component N).
Proof. 
intros M N R; induction R; intro c; inversion c; split_all; split; subst; 
inv sf_seqred1; auto; split; auto; 
red; one_step; unfold_op; eapply2 abs_sf_seqred. 
Qed. 



Definition preserves_components_l (red: termred) := 
forall M, compound M -> forall N, red M N -> compound N /\ 
multi_step red (left_component M) (left_component N).

Lemma preserves_components_l_multi_step : 
forall red, preserves_components_l red -> 
forall M, compound M -> forall N, multi_step red M N -> compound N /\ 
multi_step red (left_component M) (left_component N).
Proof. 
intros red p M c N R; induction R; split_all. split. 
eapply2 IHR. eapply2 p. 
apply transitive_red with (left_component N); split_all. 
eapply2 p. eapply2 IHR. eapply2 p. 
Qed. 




Definition preserves_components_r (red: termred) := 
forall M, compound M -> forall N, red M N -> compound N /\ 
multi_step red (right_component M) (right_component N).


Lemma preserves_components_r_multi_step : 
forall red, preserves_components_r red -> 
forall M, compound M -> forall N, multi_step red M N -> compound N /\ 
multi_step red (right_component M) (right_component N).
Proof. 
intros red p M c N R; induction R; split_all. split. 
eapply2 IHR. eapply2 p. 
apply transitive_red with (right_component N); split_all. 
eapply2 p. eapply2 IHR. eapply2 p. 
Qed. 


Lemma preserves_components_l_sf_seqred1 :  preserves_components_l sf_seqred1. 
Proof. 
red; split_all.  gen_inv H H0; inv1 compound; subst; split_all; split;  
inv sf_seqred1; inversion H8; subst; one_step.
Qed. 


Lemma preserves_components_r_sf_seqred1 :  preserves_components_r sf_seqred1. 
Proof. 
red; split_all.  gen_inv H H0; inv1 compound; subst; split_all; split;  
inv sf_seqred1; one_step.
Qed. 





Lemma sf_seqred1_to_sf_red1 : implies_red sf_seqred1 sf_red1. 
Proof. red. intros M N B; induction B; split_all. Qed. 


Lemma sf_seqred_to_sf_red: implies_red sf_seqred sf_red. 
Proof. 
eapply2 implies_red_multi_step. 
red; split_all; one_step; eapply2 sf_seqred1_to_sf_red1. 
Qed. 

Lemma to_sf_seqred_multi_step: forall red, implies_red red sf_seqred -> implies_red (multi_step red) sf_seqred. 
Proof. 
red.  intros red B M N R; induction R; split_all.
red; split_all. 
assert(sf_seqred M N) by eapply2 B. 
apply transitive_red with N; auto. 
eapply2 IHR. 
Qed. 


Lemma sf_red1_to_sf_seqred: implies_red sf_red1 sf_seqred .
Proof. 
red.  intros M N OR; induction OR; split_all.
(* 3 *) 
apply succ_red with (App (App M P) (App N P)). eapply2 s_sf_seqred. 
eapply2 preserves_app_sf_seqred. 
apply succ_red with M. 
eapply2 f_op_sf_seqred. auto. 
red; apply succ_red with  (App (App N (left_component P)) (right_component P))
; split_all. 
eapply2 preserves_app_sf_seqred.
eapply2 preserves_app_sf_seqred.
eapply2 preserves_components_l_multi_step. 
eapply2 preserves_components_l_sf_seqred1. 
eapply2 preserves_components_r_multi_step. 
eapply2 preserves_components_r_sf_seqred1. 
Qed. 


Hint Resolve sf_red1_to_sf_seqred.

Lemma sf_red_to_sf_seqred: implies_red sf_red sf_seqred. 
Proof. eapply2 to_sf_seqred_multi_step. Qed.


Lemma diamond_sf_seqred: diamond sf_seqred sf_seqred. 
Proof. 
red; split_all. 
assert(sf_red M N) by eapply2 sf_seqred_to_sf_red.  
assert(sf_red M P) by eapply2 sf_seqred_to_sf_red.  
elim(diamond_sf_red M N H1 P); split_all. 
inversion H3. 
exist x; split; eapply2 sf_red_to_sf_seqred. 
Qed. 
Hint Resolve diamond_sf_seqred. 

