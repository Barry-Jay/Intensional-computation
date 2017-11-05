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
Require Import IntensionalLib.Fieska_calculus.Tagging.
Require Import IntensionalLib.Fieska_calculus.Adding.


From Bignums Require Import BigN. 

Delimit Scope bigN_scope with bigN.
Local Open Scope bigN_scope.

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

Lemma size_tag : size (star_opt (star_opt (tag (Ref 1) (Ref 0)))) = 78. 
Proof. 
unfold tag. rewrite star_opt_eta. 2: cbv; auto. 
unfold subst, subst_rec; fold subst_rec. 
rewrite subst_rec_closed. 2: cbv; auto. insert_Ref_out.   cbv. auto.
Qed.


Lemma size_var : size (star_opt (var (Ref 0))) = 133. 
Proof. 
unfold var. rewrite star_opt_eta. 2: cbv; auto. 
unfold subst; rewrite subst_rec_closed. 2: cbv; auto.  cbv. auto.
Qed.
 

Lemma size_add: size add = 3767.
Proof. cbv; auto. Qed.  


