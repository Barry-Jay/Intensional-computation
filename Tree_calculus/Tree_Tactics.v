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
(*                  Tree_Tactics.v                                    *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)

Require Import Omega. 
Require Import IntensionalLib.SF_calculus.Test.  
Require Import IntensionalLib.SF_calculus.General.  
Require Import IntensionalLib.Tree_calculus.Tree_Terms. 

Definition termred := Tree -> Tree -> Prop.

Definition preserve (R : termred) (P : Tree -> Prop) :=
  forall x : Tree, P x -> forall y : Tree, R x y -> P y.


Inductive multi_step : termred -> termred :=
  | zero_red : forall red M, multi_step red M M
  | succ_red : forall (red: Tree-> Tree -> Prop) M N P, 
                   red M N -> multi_step red N P -> multi_step red M P
.

Hint Constructors multi_step.  

Definition reflective red := forall (M: Tree), red M M.

Lemma refl_multi_step : forall (red: termred), reflective (multi_step red).
Proof. red; split_all. Qed.



Ltac reflect := match goal with 
| |- reflective (multi_step _) => eapply2 refl_multi_step
| |- multi_step _ _ _ => try (eapply2 refl_multi_step)
| _ => split_all
end.


Ltac one_step := 
match goal with 
| |- multi_step _ _ ?N => apply succ_red with N; auto; try red; try reflect
end.


Definition transitive red := forall (M N P: Tree), red M N -> red N P -> red M P. 

Lemma transitive_red : forall red, transitive (multi_step red). 
Proof. red; induction 1; split_all. 
apply succ_red with N; auto. 
Qed. 


Definition preserves_app (red : termred) := 
forall M M' N N', red M M' -> red N N' -> red (App M N) (App M' N').


Lemma preserves_app_multi_step : forall (red: termred), reflective red -> preserves_app red -> preserves_app (multi_step red). 
Proof.
red. induction 3; split_all. generalize H0; induction 1. 
reflect. 
apply succ_red with (App M N); auto.
assert( transitive (multi_step red)) by eapply2 transitive_red.  
apply X0 with (App N0 N); auto. 
one_step. 
Qed.

Hint Resolve preserves_app_multi_step.


Ltac inv1 prop := 
match goal with 
| H: prop _ |- _ => inversion H; clear H; inv1 prop
| H: prop (App  _ _) |- _ => inversion H; clear H; inv1 prop
| H: prop Op _ |- _ => inversion H; clear H; inv1 prop
| _ => split_all
 end.


Definition implies_red (red1 red2: termred) := forall M N, red1 M N -> red2 M N. 

Lemma implies_red_multi_step: forall red1 red2, implies_red red1  (multi_step red2) -> 
                                                implies_red (multi_step red1) (multi_step red2).
Proof. red. 
intros red1 red2 IR M N R; induction R; split_all. 
apply transitive_red with N; auto. 
Qed. 

Ltac inv red := 
match goal with 
| H: multi_step red (App _ _) _ |- _ => inversion H; clear H; inv red
| H: multi_step red (Ref _) _ |- _ => inversion H; clear H; inv red
| H: multi_step red (Op _) _ |- _ => inversion H; clear H; inv red
| H: red (Ref _) _ |- _ => inversion H; clear H; inv red
| H: red (App _ _) _ |- _ => inversion H; clear H; inv red
| H: red (Op _) _ |- _ => inversion H; clear H; inv red
| H: multi_step red _ (Ref _) |- _ => inversion H; clear H; inv red
| H: multi_step red _ (App _ _) |- _ => inversion H; clear H; inv red
| H: multi_step red _ (Op _) |- _ => inversion H; clear H; inv red
| H: red _ (Ref _) |- _ => inversion H; clear H; inv red
| H: red _ (App _ _) |- _ => inversion H; clear H; inv red
| H: red _ (Op _) |- _ => inversion H; clear H; inv red
| _ => subst; split_all 
 end.



Definition diamond (red1 red2 : termred) := 
forall M N, red1 M N -> forall P, red2 M P -> exists Q, red2 N Q /\ red1 P Q. 

Lemma diamond_flip: forall red1 red2, diamond red1 red2 -> diamond red2 red1. 
Proof. 
unfold diamond; split_all. elim (H M P H1 N H0); split_all. inversion H2. 
 exist x. 
Qed.

Lemma diamond_strip : 
forall red1 red2, diamond red1 red2 -> diamond red1 (multi_step red2). 
Proof. intros. 
eapply2 diamond_flip. 
red; induction 1; split_all.
exist P.
elim (H M P0 H2 N); split_all. inversion H3. 
elim(IHmulti_step H x); split_all. inversion H6.
exist x0. split. auto. 
apply succ_red with x; auto. 
Qed. 


Definition diamond_star (red1 red2: termred) := forall  M N, red1 M N -> forall P, red2 M P -> 
  exists Q, red1 P Q /\ multi_step red2 N Q. 

Lemma diamond_star_strip: forall red1 red2, diamond_star red1 red2 -> diamond (multi_step red2) red1 .
Proof. 
red. induction 2; split_all. 
exist P.
elim(H M P0 H2 N H0); split_all. inversion H3. 
elim(IHmulti_step H x); split_all. inversion H6. 
exist x0. split. auto. 
apply transitive_red with x; auto. 
Qed. 

Lemma diamond_tiling : 
forall red1 red2, diamond red1 red2 -> diamond (multi_step red1) (multi_step red2).
Proof. 
red.  induction 2; split_all.
exist P.
elim(diamond_strip red red2 H M N H0 P0); split_all.
inversion H3. 
elim(IHmulti_step H x H4); split_all. inversion H6. 
exist x0. split. auto. 
apply succ_red with x; auto.
Qed. 

Hint Resolve diamond_tiling. 

Fixpoint rank (M: Tree) := 
match M with 
| Ref _ => 1
| Op _ => 1
| App M1 M2 => S((rank M1) + (rank M2))
end.

Lemma rank_positive: forall M, rank M > 0. 
Proof. 
induction M; split_all; try omega. 
Qed. 



Ltac rank_tac := match goal with 
| |- forall M, ?P  => 
  cut (forall p M, p >= rank M -> P )
; [ intros H M;  eapply2 H | ]
end .
