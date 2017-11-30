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
(*                            Size                                    *)
(*                                                                    *)
(*                          Barry Jay                                 *)
(*                                                                    *)
(**********************************************************************)

(*
Add LoadPath ".." as IntensionalLib.
*)

Require Import Arith Omega Max Bool List.
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
Require Import IntensionalLib.Closure_to_Fieska.Tagging.
Require Import IntensionalLib.Closure_to_Fieska.Adding.
Require Import IntensionalLib.Closure_to_Fieska.Abstraction_to_Combination.

(* 
From Bignums Require Import BigN. 

Delimit Scope bigN_scope with bigN.
Local Open Scope bigN_scope.
*) 


Set Printing Depth 10000.

Fixpoint size M := 
match M with 
| Ref _ => 1
| Op _ => 1
| App M1 M2 => size M2 + size M1
end . 



Lemma size_Y2: size (Y_k 2) = 28. 
Proof. cbv. auto. Qed. 

Lemma size_Y3: size (Y_k 3) = 46. 
Proof. cbv. auto. Qed. 

Lemma size_Y4: size (Y_k 4) = 64. 
Proof. cbv. auto. Qed. 

Lemma size_var : size (var (Op Sop)) = 48. 
Proof. cbv; auto. Qed. 


Lemma size_add: size (add i_op) = 3144.
Proof. cbv. auto. Qed.  


Require Import IntensionalLib.Closure_calculus.Closure_calculus.


Lemma size_identity_abs: size (closure_to_fieska (Abs Iop 0 (Ref 0))) = 3199.
Proof. cbv. auto. Qed. 



Notation "A ~ B" := (Fieska_Terms.App A B) (at level 79, left associativity). 
Notation S := (Op Sop).
Notation F := (Op Fop).
Notation K := (Op Kop).
Notation I := (Fieska_Terms.Op Fieska_Terms.Iop). 
Notation A := (Op Aop). 

Lemma identity_abs_combinator:
(closure_to_fieska (Abs Closure_calculus.Iop 0%nat (Closure_calculus.Ref 0%nat))) = s_op. 
Proof.
cbv. 


