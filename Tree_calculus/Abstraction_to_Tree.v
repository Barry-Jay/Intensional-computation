(**********************************************************************)
(* This Program is free sofut even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 021101301 USA                                                     *)
(**********************************************************************)

(**********************************************************************)
(*                 Abstraction_to_Tree.v                              *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)


Require Import Omega Max Bool List.
Require Import IntensionalLib.SF_calculus.Test.  
Require Import IntensionalLib.SF_calculus.General.  
Require Import IntensionalLib.Tree_calculus.Abstraction_Terms.  
Require Import IntensionalLib.Tree_calculus.Abstraction_Reduction.  
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
Require Import IntensionalLib.Tree_calculus.Case.  
Require Import IntensionalLib.Tree_calculus.Extensions.  
Require Import IntensionalLib.Tree_calculus.Wait2.  
Require Import IntensionalLib.Tree_calculus.Abstraction.  
Require Import IntensionalLib.Tree_calculus.Abstraction2.  
Require Import IntensionalLib.Tree_calculus.Abstraction2a.  
Require Import IntensionalLib.Tree_calculus.Abstraction3.  
Require Import IntensionalLib.Tree_calculus.Abstraction4.  



Definition op_to_tree o := 
match o with 
| Jop => j_op
| Rop => r_op 
| Hop => h_op 
| Aop => abs_op 
| Iop => i_op 
| Bop => b_op
end.
 

Fixpoint abs_to_tree M := 
match M with 
| Abstraction_Terms.Op o => op_to_tree o
| Abstraction_Terms.App M1 M2 => App (abs_to_tree M1) (abs_to_tree M2)
end.

Theorem translation_preserves_abs_reduction:
forall M N, abs_red1 M N -> sf_red (abs_to_tree M) (abs_to_tree N). 
Proof. 
intros M N r; induction r; intros; 
unfold abs_to_tree; fold abs_to_tree; unfold op_to_tree. 
(* 14 *) 
auto. 
eapply2 j_red. 
eapply2 r_red. 
eapply2 h_red. 
eapply2 abs_red.
unfold_op. repeat eval_tac. 
eapply2 b_j_red.
eapply2 b_r_red. 
eapply2 b_h_red.
eapply2 b_a_red. 
eapply2 b_i_red.
eapply2 b_b_red.
(* 2 *) 
generalize H; case o; intro. 
congruence. 
eapply2 b_r_op_red.
eapply2 b_h_op_red. 
eapply2 b_abs_op_red. 
eapply2 b_i_op_red. 
eapply2 b_b_op_red. 
(* 1 *)  
inversion H; subst; unfold abs_to_tree; fold abs_to_tree; 
unfold op_to_tree; subst.
eapply2 b_h1_red.
eapply2 b_a1_red.
eapply2 b_b1_red.
Qed. 
  



Ltac eval1 := 
unfold sf_red; 
match goal with 
| |- multi_step sf_red1  (App (App (App (App _ _) _) _) _) _ =>  
eapply transitive_red; [eapply preserves_app_sf_red ; [eval1 |]|]
| |- multi_step sf_red1  (App (App (App (Op Node) (Op Node)) _) _) _ => 
  eapply succ_red; [eapply2 k_red |]
| |- multi_step sf_red1  (App (App (App (Op Node) (App (Op Node) _)) _) _) _ => 
  eapply succ_red; [eapply2 s_red |]
| |- multi_step sf_red1  (App (App (App (Op Node) (App (App (Op Node) _) _)) _) _) _ => 
  eapply succ_red; [eapply2 f_red |]
| |- multi_step sf_red1  (App (App (Op Node) _) _) _ => eapply transitive_red; [eapply preserves_app_sf_red ; eval1 |]
| |- multi_step sf_red1  (App (Op Node) _) _ => eapply transitive_red; [eapply preserves_app_sf_red ; [auto|eval1 ]|]
| _ => auto
end.

Definition s_op := 
star (star (star (App (App (Ref 2) (Ref 0)) 
                                  (App (Ref 1) (Ref 0))))).

(* s_opt rule takes 11 steps *) 

Lemma s_op_rule : forall M N P, sf_red (App (App (App s_op M) N) P) (App (App M P) (App N P)).
Proof.
intros; unfold s_op; simpl; unfold_op; simpl.  
eval1. eval1. eval1. auto.  eval1. eval1. auto. eval1. eval1. eval1. auto.  eval1. eval1. auto.  eval1. eval1. eval1. 
 auto. eval1. eval1. auto.  eval1. eval1. eval1. auto. eval1. auto. auto.  eval1. eval1. auto.  eval1.
auto.  auto. auto. auto. 
 eval1. eval1. eval1. auto. 
eval1. eval1. auto.  eval1. eval1. eval1. auto. eval1. auto. auto.  eval1. auto. auto. auto. auto. 
  eval1. eval1. eval1. auto. eval1. auto. auto. eval1. auto. auto. auto. auto. auto. auto.   
eval1. eval1. auto.  eval1. eval1. eval1. auto. eval1. auto. auto.  eval1. auto. auto. 
 eval1. auto.  eval1. eval1. auto.  eval1.  eval1. eval1. auto.  eval1. eval1. auto. eval1. eval1. eval1. auto. eval1. 
eval1. auto. eval1. eval1. eval1. auto. eval1. eval1. auto. eval1. eval1. eval1. auto.  eval1. 
auto. auto. eval1. auto. auto. auto. auto.  eval1. eval1. eval1. auto. eval1. auto. auto.  eval1. auto. 
auto. auto. auto. auto.  eval1.  eval1. eval1. auto.  eval1. eval1. auto.  eval1. eval1.  eval1.  auto.   
eval1. eval1. auto.  eval1. eval1.  eval1. auto. eval1. auto. auto.  eval1. auto. auto. auto. auto. 
 eval1. eval1. eval1. auto.  eval1. all: auto. 
 eval1. eval1. eval1.  eval1. auto. eval1. eval1. auto. eval1. eval1. eval1. auto.
(* 100 steps *) 
 eval1. eval1. auto.  eval1. eval1. eval1. auto.  eval1.
eval1. auto. eval1. eval1. eval1. auto.  eval1. eval1. auto. eval1. eval1. eval1. auto. eval1. eval1. auto.
eval1. all: auto.
 eval1. eval1. eval1. eval1. auto. eval1. all:auto.
 eval1. eval1. auto. eval1. eval1.
eval1. eval1. auto. eval1. all: auto. 
(* 1 *) 
eapply transitive_red; [eapply preserves_app_sf_red ; [eval1 |]|].
eval1. auto.  eval1. eval1.  eval1. eval1. auto. eval1. eval1. auto. 
eval1. eval1. eval1. auto. eval1. eval1. auto. eval1. eval1. eval1. auto. 
eval1. eval1. all: auto. 
 eval1. eval1. eval1. auto. eval1. eval1. eval1. eval1. all: auto. 
eval1. eval1. eval1. eval1. eval1. auto. eval1. all: auto. 
eval1. eval1. eval1. auto. eval1. eval1. eval1. eval1. all: auto.
(* 68 steps *) 
(* 1 *) 
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. auto. 
eval1. eval1. eval1. eval1. eval1. eval1. auto.  eval1. auto. auto. eval1. auto. auto. auto.   
eval1. auto.  eval1. eval1. eval1. auto.  eval1. auto. auto.  auto. eval1. eval1. auto. 
eval1. auto. auto. auto. eval1. auto. eval1. auto. eval1. auto. eval1. auto. eval1. auto. eval1.
auto.  eval1. auto. 
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. auto. 
eval1. auto.  eval1. auto. auto. auto.  eval1. auto. auto. auto.  eval1. eval1. eval1. auto.
  eval1. auto. auto. eval1. auto. auto. auto.
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. auto. 
eval1. eval1. eval1. eval1. eval1. auto. eval1. eval1. auto. eval1. eval1. eval1. auto. 
eval1. eval1. auto.  eval1. eval1.  eval1.  auto. eval1.  auto.  auto. eval1. auto. auto. auto. 
auto.  eval1. eval1. eval1. auto. eval1. auto. auto. eval1. all: auto. 
eval1. eval1. auto. eval1. eval1. auto. auto. eval1.
eapply2 preserves_app_sf_red. 
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. auto. 
eval1. eval1. eval1. eval1. eval1. auto. eval1. auto. auto.  eval1. auto. auto. auto.  eval1. auto. eval1.
 eval1. auto. eval1. auto. auto. auto.  eval1. eval1. eval1. auto.  eval1. eval1.  auto. eval1.
eval1. eval1. auto. eval1. auto. auto. eval1. auto. auto. auto. auto.
eval1. eval1. eval1. auto. eval1. auto. auto. eval1. auto. auto. auto. auto. 
eval1. eval1.  auto. eval1. auto. auto. auto.
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red.
eapply preserves_app_sf_red. auto. 
eval1. auto.  eval1. auto. auto. auto. eval1. auto. auto. auto. eval1. eval1. eval1.
eval1. auto. eval1. eval1. auto. eval1. eval1. eval1. auto. eval1. all: auto. 
(* 100 steps *) 
eval1. eval1. eval1. eval1. eval1. auto. eval1. auto. auto. eval1. auto. auto. auto.  
eval1. auto. eval1. eval1. auto. auto. eval1. eval1.
eval1. auto.  eval1. all: auto. 
eval1. eval1. auto.  eval1. eval1. auto. auto.
(* 18 steps *) 
Qed. 



Definition s_opt := 
star_opt (star_opt (star_opt (App (App (Ref 2) (Ref 0)) 
                                  (App (Ref 1) (Ref 0))))).

(* s_opt rule takes 11 steps *) 

Lemma s_opt_rule : forall M N P, sf_red (App (App (App s_opt M) N) P) (App (App M P) (App N P)).
Proof.
intros; unfold s_opt. simpl. unfold_op; unfold subst; simpl.
eapply succ_red. eapply app_sf_red.  eapply app_sf_red.  eapply2 s_red. auto. auto.  
eapply succ_red. eapply app_sf_red. eapply app_sf_red.  eapply app_sf_red.  eapply2 s_red.
eapply2 k_red.  auto.  auto. auto.
eapply succ_red. eapply app_sf_red. eapply app_sf_red. eapply app_sf_red.  eapply app_sf_red.  eapply2 k_red.
eapply2 s_red.  auto. auto. auto. 
eapply succ_red. eapply app_sf_red.  eapply app_sf_red.  eapply app_sf_red.  eapply app_sf_red.   auto.  eapply app_sf_red.  eapply2 k_red. auto. auto. auto. auto.
eapply succ_red. eapply app_sf_red.  eapply2 s_red. auto. 
eapply succ_red. eapply app_sf_red.  eapply app_sf_red.  eapply s_red. auto. auto. auto. 
eapply2 k_red. auto.
eapply succ_red.   eapply app_sf_red.  eapply app_sf_red. eapply app_sf_red.   eapply2 k_red. auto. auto. auto.
eapply succ_red.  eapply s_red. all: auto. 
Qed. 



  eapply app_sf_red.   auto.  eapply app_sf_red.  eapply2 k_red. auto. auto. auto. auto.
   
  
  
