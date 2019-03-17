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
  
