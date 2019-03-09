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
(*                Abstraction_Reduction.v                             *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)

(* 
Add LoadPath ".." as IntensionalLib.
*) 
Require Import Arith.
Require Import IntensionalLib.SF_calculus.General.
Require Import IntensionalLib.Tree_calculus.Abstraction_Terms. 
Require Import IntensionalLib.Tree_calculus.Abstraction_Tactics.


Ltac split_all := simpl; intros; 
match goal with 
| H : _ /\ _ |- _ => inversion_clear H; split_all
| H : exists _, _ |- _ => inversion H; clear H; split_all 
| _ =>  try (split; split_all); try contradiction
end; try congruence; auto.




(* true compounds *) 

Fixpoint right_component (M : Abs_Term) := 
match M with 
| App _ M2 => M2
| _ => M
end.

Definition left_component (U : Abs_Term) := 
match U with 
| App U1 _ => U1 
| _ => Op Iop
end.


Inductive true_compound : Abs_Term -> Prop := 
| h_compound : forall M, true_compound (App (Op Hop) M) 
| a_compound : forall M, true_compound (App (Op Aop) M)
| b_compound : forall M, true_compound (App (Op Bop) M)
. 


(* Abstraction-reduction  *) 


Inductive abs_red1 : termred :=
  | app_abs_red :
      forall M M' ,
      abs_red1 M M' ->
      forall N N' : Abs_Term, abs_red1 N N' -> abs_red1 (App M N) (App M' N')  
  | j_red: forall M, abs_red1 (App (Op Jop) M) (App (App (Op Hop) (Op Jop)) M) 
  | r_red : forall M N, abs_red1 (App (App (Op Rop) M) N) (App (App (Op Hop) (App (Op Rop) M)) N)
  | h_red : forall M N P, abs_red1 (App (App (App (Op Hop) M) N) P) 
                (App (App (Op Hop) (App (App (Op Hop) M) N)) P)
  | a_red : forall M N P, abs_red1 (App (App (App (Op Aop) M) N) P) (App (App (App (Op Bop) P) M) N)
  | i_red : forall M, abs_red1 (App (Op Iop) M) M
  | b_j_red : forall M N, abs_red1 (App (App (App (Op Bop) M) N) (Op Jop)) M
  | b_r_red : forall M N P, abs_red1 (App (App (App (Op Bop) M) N) (App (Op Rop) P)) (App N P)
  | b_h_red : forall M N P Q, abs_red1 (App (App (App (Op Bop) M) N) (App (App (Op Hop) P) Q))
                            (App (App (App (App (Op Bop) M) N) P) (App (App (App (Op Bop) M) N) Q))
  | b_a_red : forall M N P Q, abs_red1 (App (App (App (Op Bop) M) N) (App (App (Op Aop) P) Q))
                                (App (App (Op Aop) (App (App (App (Op Bop) M) N) P)) Q)
  | b_i_red : forall M N, abs_red1 (App (App (App (Op Bop) M) N) (Op Iop)) (Op Iop)
  | b_b_red : forall M N P Q, abs_red1 (App (App (App (Op Bop) M) N) (App (App (Op Bop) P) Q))
                               (App (App (Op Bop) (App (App (App (Op Bop) M) N) P))
                                    (App (App (App (Op Bop) M) N) Q))
  | b_op_red : forall M N o, o<> Jop -> abs_red1 (App (App (App (Op Bop) M) N) (Op o)) (Op o)
  | b_compound_red: forall M N P Q, true_compound (App P Q) -> 
                   abs_red1 (App (App (App (Op Bop) M) N) (App P Q))
                            (App (App (App (App (Op Bop) M) N) P) (App (App (App (Op Bop) M) N) Q))
.




