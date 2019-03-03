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
(* 13 *)  
eapply2 j_red. 
(* 12 *) 
eapply2 r_red. 
(* 11 *) 
eapply2 h_red. 
(* 10 *) 
eapply2 abs_red.
(* 9 *) 
unfold_op. repeat eval_tac. 
(* 8 *) 
eapply2 b_j_red.
(* 7 *) 
eapply2 b_r_red. 
(* 6 *) 
eapply2 b_h_red.
(* 5 *) 
eapply2 b_a_red.  
 
 

