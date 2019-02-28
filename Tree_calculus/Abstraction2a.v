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
(* 021101301 USA                                                     *)
(**********************************************************************)

(**********************************************************************)
(*                   Abstraction2a.v                                  *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)


Require Import Omega Nat Max Bool List.
Require Import IntensionalLib.SF_calculus.Test.  
Require Import IntensionalLib.SF_calculus.General.  
Require Import IntensionalLib.Tree_calculus.Tree_Terms.  
Require Import IntensionalLib.Tree_calculus.Tree_Tactics.  
Require Import IntensionalLib.Tree_calculus.Tree_reduction.  
Require Import IntensionalLib.Tree_calculus.Tree_Normal.  
Require Import IntensionalLib.Tree_calculus.Tree_Closed.  
Require Import IntensionalLib.Tree_calculus.Substitution.  
Require Import IntensionalLib.Tree_calculus.Tree_Eval.  
Require Import IntensionalLib.Tree_calculus.Star.  
Require Import IntensionalLib.Tree_calculus.Wait.  
Require Import IntensionalLib.Tree_calculus.Fixpoints.  
Require Import IntensionalLib.Tree_calculus.Wave_Factor.  
Require Import IntensionalLib.Tree_calculus.Wave_Factor2.  
Require Import IntensionalLib.Tree_calculus.Equal.  
Require Import IntensionalLib.Tree_calculus.Extensions.  
Require Import IntensionalLib.Tree_calculus.Wait2.  
Require Import IntensionalLib.Tree_calculus.Abstraction.  
Require Import IntensionalLib.Tree_calculus.Abstraction2.  


Lemma aux9: bind_normal
  (App
     (app_comb (app_comb (app_comb (A_k 5) (omega_k 4)) (omega_k 4)) (Ref 0))
     (App (App (App (Ref 5) (Ref 4)) (Ref 3)) (Ref 1))).
Proof.
apply bn_app.
apply bn_normal. 
repeat eapply2 app_comb_normal. 
eapply2 bn_normal.
rewrite maxvar_app. rewrite ! maxvar_app_comb. 
rewrite A_k_closed.
rewrite omega_k_closed.
unfold maxvar. simpl. omega. 
Qed. 



Lemma aux8: 
bind_normal
  (extension
     (app_comb
        (app_comb (app_comb (app_comb (omega_k 4) (omega_k 4)) h_fn) (Ref 0))
        (Ref 1))
     (App (App (App (App (Ref 4) (Ref 3)) (Ref 2)) (Ref 0))
        (App (App (App (Ref 4) (Ref 3)) (Ref 2)) (Ref 1)))
     (extension
        (app_comb
           (app_comb (app_comb (app_comb (omega_k 4) (omega_k 4)) (Ref 0))
              (Ref 1)) (Ref 2))
        (App
           (App
              (app_comb (app_comb (app_comb (A_k 5) (omega_k 4)) (omega_k 4))
                 (Ref 0)) (App (App (App (Ref 5) (Ref 4)) (Ref 3)) (Ref 1)))
           (App (App (App (Ref 5) (Ref 4)) (Ref 3)) (Ref 2)))
        (extension
           (app_comb (app_comb (app_comb (omega_k 3) (omega_k 3)) (Ref 0))
              (Ref 1)) (App (Ref 2) (Ref 1))
           (extension (app_comb (Y_k 2) (Ref 0)) (Ref 2)
              (extension (app_comb (app_comb (Ref 0) (Ref 1)) (Ref 2))
                 (App
                    (App (app_comb (A_k 3) (Ref 0))
                       (App (App (App (Ref 5) (Ref 4)) (Ref 3)) (Ref 1)))
                    (Ref 2)) i_op))))).
Proof.
apply bind_normal_extension. 
apply bn_normal. 
repeat eapply2 nf_active. 
apply bind_normal_extension.
2: eapply2 aux7.  
apply bn_app.
all: cycle 1. 
eapply2 bn_normal. 
rewrite ! maxvar_app.
match goal with 
| |- Nat.max ?m ?n >0 => assert(Nat.max m n >= n) by eapply2 max_is_max end. 
assert(Nat.max
      (Nat.max (Nat.max (maxvar (Ref 5)) (maxvar (Ref 4))) (maxvar (Ref 3)))
      (maxvar (Ref 2)) >= maxvar (Ref 2)) by eapply2 max_is_max.
assert(maxvar (Ref 2) >0) by (cbv; omega). 
omega.  
apply aux9.
Qed. 


Lemma aux10: 3 = 3.
Proof. auto. Qed. 
(* 

Lemma star_opt_bind_normal_mono: 
forall M N, bind_normal M -> bind_normal N -> star_opt M = star_opt N -> M = N. 
Proof. 
induction M; split_all. 

Qed.
*)

