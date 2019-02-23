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
(*                         Wave_Types.v                               *)
(*                                                                    *)
(*                          Barry Jay                                 *)
(*                                                                    *)
(**********************************************************************)



Require Import Omega Max Bool List.
Require Import IntensionalLib.SF_calculus.Test.  
Require Import IntensionalLib.SF_calculus.General.  
Require Import IntensionalLib.Wave_as_SF.SF_Terms.  
Require Import IntensionalLib.Wave_as_SF.SF_Tactics.  
Require Import IntensionalLib.Wave_as_SF.SF_reduction.  
Require Import IntensionalLib.Wave_as_SF.SF_Normal.  
Require Import IntensionalLib.Wave_as_SF.SF_Closed.  
Require Import IntensionalLib.Wave_as_SF.Substitution.  
Require Import IntensionalLib.Wave_as_SF.SF_Eval.  
Require Import IntensionalLib.Wave_as_SF.Star.  
Require Import IntensionalLib.Wave_as_SF.Fixpoints.  
Require Import IntensionalLib.Wave_as_SF.Wave_Factor.  
Require Import IntensionalLib.Wave_as_SF.Wave_Factor2.  
Require Import IntensionalLib.Wave_as_SF.Equal.  
Require Import IntensionalLib.Wave_as_SF.Extensions.  

(* the plan 

Old approach T :: = Leaf  | Stem T | Fork T T | T -> T 

Fork Leaf T < K T 
Fork (Stem (U-> V)) (U-> V -> T) < U -> T 
Fork (Fork P Q) T < (P-> Q-> U) -> U

New approach: 

 - types are terms 

t : T   u : U 
-----------------
t u : T U 

Here, T is a function that is applied to U. 
If type-checking fails then T U returns an error, say, ~

Let E be the equality function. Define  

U -> V = \*x. EUxV~
       = S(S(EU)(KV))(K~)
       =  ~(~(K~))(~(~(KV))(EU))

so that (U -> V) U' -->  EUU'V~  (the final ~ is the error). 

~ : Node  where Node is a (non-recursive) function that satisfies 

Node Node T U --> T
Node (Node (U -> V)) (U -> V -> T) U --> T 
Node (Node P Q) T (P-> Q-> U) -> U

Now, Node P Q must be a function, 
so that it can be passed as an argument in, say Node (U-> V). 
So Node is unary or binary. Simplest is unary. 
Thus Node is a pattern-matching function which, in general, 
produces pattern-matching functions as results. 

To Do: 

Define R
Define E. 
Define the pattern-matching functions in the result of Node. 
Determine the patterns for Node (U->V) and Node P Q.
Define Node (some circularity here ?!)

Define Node 
 
*) 


Definition Funty U T := star_opt (App (App (App (App equal_comb (lift 1 U)) (Ref 0)) (lift 1 T)) (Op Node)).

Lemma funty_ok : 
forall U T, program U -> sf_red (App (Funty U T) U) T. 
Proof. 
intros. unfold Funty. 
eapply transitive_red. eapply2 star_opt_beta.  
unfold subst, lift; rewrite ! subst_rec_app.
rewrite subst_rec_closed. 2: rewrite equal_comb_closed; omega. 
rewrite ! subst_rec_lift_rec; try omega. 
rewrite lift_rec_null. unfold subst_rec. insert_Ref_out. 
unfold lift; rewrite ! lift_rec_null.
eapply transitive_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. eapply2 equal_programs. all: auto. 
eval_tac. 
Qed. 

Lemma funty_fail: 
forall U V T, program U -> program V -> U <> V -> sf_red (App (Funty U T) V) (Op Node).
Proof.
intros. unfold Funty. 
eapply transitive_red. eapply2 star_opt_beta.  
unfold subst, lift; rewrite ! subst_rec_app.
rewrite subst_rec_closed. 2: rewrite equal_comb_closed; omega. 
rewrite ! subst_rec_lift_rec; try omega. 
rewrite lift_rec_null. unfold subst_rec. insert_Ref_out. 
unfold lift; rewrite ! lift_rec_null.
eapply transitive_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. eapply2 unequal_programs. all: auto. 
eval_tac. eval_tac.  
Qed.

Definition Nty := 

extension (Op Node) k_op (
extension (App (App (Op Node) (Ref 0)) (Ref 1)) 
          (App k_op (extension (Funty (Ref 0) (Funty (Ref 1) (Ref 2)))  
                               (App (App (App (App equal_comb (Ref 4)) (Ref 2)) 
                               (App (App (App (App equal_comb (Ref 3)) (Ref 1)) 
                                         (Ref 0))
                               (Op Node))) (Op Node)) (App k_op (Op Node)))) (
extension (App (Op Node) (Funty (Ref 0) (Ref 1)))
          (extension (Funty (Ref 0) (Funty (Ref 1) (Ref 2)))  
                               (App (App (App (App equal_comb (Ref 4)) (Ref 2)) 
                               (App (App (App (App equal_comb (Ref 3)) (Ref 1)) 
                                         (Funty (Ref 2) (Ref 0)))
                               (Op Node))) (Op Node))
                      (App k_op (Op Node)))
           (App k_op (Op Node))))
.


Inductive derive : SF -> SF -> Prop := 
| op_ty : derive (Op Node) Nty 
| app_ty : forall t T u U, derive t T -> derive u U -> derive (App t u) (App T U)
| red_ty : forall t T0 T, derive t T0 -> sf_red T0 T -> derive t T.

Lemma derive_K : derive k_op  

(App


extension  < dynamic pattern > 

Node Node T U --> T
Node (Node (U -> V)) (U -> V -> T) U --> T 
Node (Node P Q) T (P-> Q-> U) -> U




