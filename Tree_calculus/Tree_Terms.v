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
(*                     Tree-Calculus                                  *)
(*                                                                    *)
(*                      Barry Jay                                     *)
(*                                                                    *)
(**********************************************************************)


(* See "Trees not Numbers.pdf" *)

(** More operators may be added in future. Strictly, 
the operator ~ is called the kernel, whose instances are nodes, perhaps leaves. *) 

Inductive operator := | Node . 

(** The terms of Tree-calculus are either variables (given as de Bruijn indices), operators or applications. 
Terms are called combinations if they do not use any variables. *) 

Inductive Tree:  Set :=
  | Ref : nat -> Tree        
  | Op  : operator -> Tree   
  | App : Tree -> Tree -> Tree   
.

