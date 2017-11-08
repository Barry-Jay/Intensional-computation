(**********************************************************************)
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

(**********************************************************************)
(*                      SF_size.v                                     *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)

(* 
Add LoadPath ".." as IntensionalLib.
*) 

Require Import Arith Omega Max Bool List.
Require Import IntensionalLib.SF_calculus.General.  
Require Import IntensionalLib.SF_calculus.SF_Terms.  
Require Import IntensionalLib.SF_calculus.SF_Tactics.  
Require Import IntensionalLib.SF_calculus.SF_reduction.  
Require Import IntensionalLib.SF_calculus.SF_Normal.  
Require Import IntensionalLib.SF_calculus.SF_Closed.  
Require Import IntensionalLib.SF_calculus.Substitution.  
Require Import IntensionalLib.SF_calculus.SF_Eval.  
Require Import IntensionalLib.SF_calculus.Star.  
Require Import IntensionalLib.SF_calculus.Fixpoints.  
Require Import IntensionalLib.SF_calculus.Equal.  
Require Import IntensionalLib.SF_calculus.Extensions.  
Require Import IntensionalLib.SF_calculus.Tagging.  
Require Import IntensionalLib.SF_calculus.Adding.  

From Bignums Require Import BigN. 


Delimit Scope bigN_scope with bigN.
Local Open Scope bigN_scope.


Fixpoint size M := 
match M with 
| Ref _ => 2 
| Op _ => 1
| App M1 M2 => (size M2) + (size M1)
end .


Lemma tag_size: size (tag s_op s_op) = 950 . 
Proof. cbv. auto.  Qed.

Lemma var_size: size (var s_op) = 1723 . 
Proof. cbv. auto.  Qed.

Lemma size_var_fn : size var_fn = 1079. 
Proof. cbv. auto. Qed. 

Lemma size_add: size add = 56680.
Proof. cbv. auto. Qed. 



