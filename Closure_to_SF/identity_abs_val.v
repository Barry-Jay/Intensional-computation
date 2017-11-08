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
(*                       identity_abs_val                             *)
(*                                                                    *)
(*                          Barry Jay                                 *)
(*                                                                    *)
(**********************************************************************)


(*
Add LoadPath ".." as IntensionalLib.
*)

Require Import Arith Omega Max Bool List.

From Bignums Require Import BigN. 

Require Import IntensionalLib.Closure_calculus.Closure_calculus.

Require Import IntensionalLib.SF_calculus.Test.
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
Require Import IntensionalLib.SF_calculus.Extensions.
Require Import IntensionalLib.SF_calculus.Tagging.
Require Import IntensionalLib.SF_calculus.Adding.
Require Import IntensionalLib.SF_calculus.SF_size.

Require Import IntensionalLib.Closure_to_SF.Abstraction_to_Combination.


Lemma size_identity_abs: 
size (lambda_to_SF (Abs Closure_calculus.Iop 0%nat (Closure_calculus.Ref 0))) = 58444%bigN.
Proof. cbv. auto. Qed. 
