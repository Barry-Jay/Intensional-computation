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
(*                      Fieska_Terms                                  *)
(*                                                                    *)
(*                      Barry Jay                                     *)
(*                                                                    *)
(**********************************************************************)


Require Import Arith Omega Max Bool List.
Require Import IntensionalLib.Fieska_calculus.Test.
Require Import IntensionalLib.Fieska_calculus.General.


(* Fieska-terms using de Bruijn's indices *)


Inductive operator := | Sop | Fop | Aop | Kop | Iop | Eop .

Inductive Fieska:  Set :=
  | Ref : nat -> Fieska 
  | Op  : operator -> Fieska 
  | App : Fieska -> Fieska -> Fieska
.

