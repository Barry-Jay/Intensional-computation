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
(*                     SF-Calculus                                    *)
(*                  as Wave Calculus                                  *)
(*                                                                    *)
(*                      Barry Jay                                     *)
(*                                                                    *)
(**********************************************************************)


(** The operators S and F are enough, but more may be added in future. *) 

Inductive operator := | Node . 

(** The terms of SF-calculus are either variables (given as de Bruijn indices), operators or applications. 
Terms are called combinations if they do not use any variables. *) 

Inductive SF:  Set :=
  | Ref : nat -> SF        
  | Op  : operator -> SF   
  | App : SF -> SF -> SF   
.

