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
(*                      Tree-Calculus                                 *)
(*                                                                    *)
(* is implemented in Coq by adapting the implementation of            *) 
(* Lambda Calculus from Project Coq                                   *)
(* 2015                                                               *)
(**********************************************************************)

(**********************************************************************)
(*                          Wait.v                                    *)
(*                                                                    *)
(*                        Barry Jay                                   *)
(*                                                                    *)
(**********************************************************************)

Require Import Arith Omega List Max.
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


Lemma maxvar_op: forall o, maxvar (Op o) = 0.  Proof. split_all. Qed. 


(* delayed application *) 

Definition app_comb M N := 

App (App (Op Node) (App (Op Node) i_op))
    (App (App (Op Node) (App (Op Node) (App k_op N))) (App k_op M)).

Lemma app_comb_red : forall M N P, sf_red (App (app_comb M N) P) (App (App M N) P).
Proof.
unfold app_comb; unfold_op; split_all. 
eapply succ_red. eapply2 s_red. 
eapply succ_red.  eapply app_sf_red.   
 eapply2 s_red.  eapply2 s_red. all: auto. 
eapply succ_red. eapply app_sf_red.   
 eapply app_sf_red. eapply2 k_red. all: auto.
eapply2 preserves_app_sf_red.
eapply2 preserves_app_sf_red. eval_tac. eval_tac.   
Qed. 


Lemma lift_rec_preserves_app_comb: 
forall M1 M2 n k, lift_rec (app_comb M1 M2) n k = app_comb (lift_rec M1 n k) (lift_rec M2 n k).
Proof. intros; unfold app_comb; unfold_op; split_all. Qed. 

Lemma subst_rec_preserves_app_comb: 
forall i M N k, subst_rec (app_comb i M) N k = app_comb (subst_rec i N k) (subst_rec M N k). 
Proof. intros; unfold app_comb; unfold_op; split_all.  Qed. 

Lemma app_comb_normal: forall i M, normal i -> normal M -> normal (app_comb i M). 
Proof. intros; unfold app_comb; unfold_op. repeat eapply2 nf_compound. Qed. 

Lemma maxvar_app_comb : forall M N,  maxvar (app_comb M N) = max(maxvar M) (maxvar N).
Proof. intros; unfold app_comb. unfold_op; split_all. rewrite max_swap. auto. Qed.

Lemma app_comb_program: forall M N, program M -> program N -> program (app_comb M N). 
Proof. 
intros; inversion H; inversion H0; split.  
eapply2 app_comb_normal. 
rewrite maxvar_app_comb. rewrite H2; rewrite H4; auto. 
Qed. 
 


Lemma rank_app_comb: forall M N, rank (app_comb M N) > rank (App M N).
Proof. intros; unfold app_comb; split_all. omega. Qed.


Lemma program_app_comb2 : forall M N, program (app_comb M N) -> program M /\ program N.
Proof.
  unfold app_comb; unfold_op; intros. inversion H. simpl in H1.  max_out.
assert(normal M /\ normal N). clear - H0. 
  inversion H0. inversion H4. clear - H3.  inversion H3; subst. inversion H4.
clear - H1 H2. inversion H1; inversion H2; subst. 
inversion H10. inversion H5. inversion H10. split; auto. 
clear - H4. inversion H4. inversion H3. inversion H2. auto. auto. 
inversion H1; split; unfold program; auto. 
Qed.




Lemma app_comb_preserves_sf_red: 
forall M M' N N', 
sf_red M M' -> sf_red N N' -> 
sf_red (app_comb M N) (app_comb M' N'). 
Proof.  intros; unfold app_comb. repeat eapply2 preserves_app_sf_red.  Qed. 

Definition a_op := star_opt (star_opt (app_comb (Ref 1) (Ref 0))). 

Ltac unfold_op := unfold a_op, app_comb, i_op, k_op, node. 

Lemma a_op1_red : forall M, sf_red (App a_op M) (star_opt (app_comb (lift 1 M) (Ref 0))).
Proof.
intros. unfold a_op. 
eapply transitive_red. 
eapply2 star_opt_beta.
unfold subst; rewrite subst_rec_preserves_star_opt.
rewrite subst_rec_preserves_app_comb.
unfold subst_rec. insert_Ref_out. auto. 
Qed. 
  

Lemma a_op2_red: forall M N, sf_red (App (App a_op M) N) (app_comb M N). 
Proof.
unfold a_op; intros. eapply transitive_red. eapply2 star_opt_beta2. 
unfold subst. repeat rewrite subst_rec_preserves_app_comb. 
unfold subst_rec; fold subst_rec. insert_Ref_out. 
unfold subst_rec; fold subst_rec. insert_Ref_out. unfold lift. 
repeat rewrite lift_rec_null. 
rewrite subst_rec_lift_rec; try omega. 
repeat rewrite lift_rec_null. 
auto.
Qed. 

Lemma a_op_red: forall M N P, sf_red (App (App (App a_op M) N) P) (App (App M N) P).
Proof.
unfold a_op; intros. eapply transitive_red. eapply preserves_app_sf_red. 
eapply2 star_opt_beta2. auto. 
unfold subst. repeat rewrite subst_rec_preserves_app_comb. 
eapply transitive_red. eapply2 app_comb_red. 
unfold subst_rec; fold subst_rec. insert_Ref_out. 
unfold subst_rec; fold subst_rec. insert_Ref_out. unfold lift.  
repeat rewrite lift_rec_null. 
rewrite subst_rec_lift_rec; try omega. 
repeat rewrite lift_rec_null. 
auto.
Qed. 

Fixpoint A_k k := 
match k with 
| 0 => i_op 
| 1 => i_op 
| 2 => a_op 
| S k1 => star (star (app_comb (A_k k1) (app_comb (Ref 1) (Ref 0))))
end.

Lemma A3_closed: forall k, maxvar (A_k (S (S (S k)))) = 0.
Proof. 
induction k; intros. split_all.  
replace (A_k (S (S (S (S k))))) with 
(star (star (app_comb (A_k (S (S (S k)))) (app_comb (Ref 1) (Ref 0))))).
2: unfold A_k; auto.  
rewrite ! maxvar_star.
rewrite ! maxvar_app_comb.
rewrite IHk. split_all. 
Qed.

Lemma A_k_closed: forall k, maxvar (A_k k) = 0. 
Proof.
induction k; intros. split_all. clear IHk.   
induction k; intros. split_all.  clear IHk.
induction k; intros. split_all. 
eapply2 A3_closed. 
Qed. 


Lemma A_k_normal: forall k, normal (A_k k). 
Proof. 
intros.  case k; intros. unfold A_k; unfold_op; split_all. 
case n; intros. unfold A_k; unfold_op; split_all.
case n0; intros. unfold A_k; unfold_op; split_all.
unfold subst; unfold_op; simpl. 
repeat eapply2 nf_compound. 
unfold A_k; fold A_k.
eapply2 star_normal. 
Qed.


  
Hint Resolve A_k_closed A_k_normal.

Lemma A3_red: forall k M N, sf_red (App (App (A_k (S(S(S k)))) M) N) (app_comb (A_k (S(S k))) (app_comb M N)).
Proof. 
induction k; intros.  
(* 2 *) 
unfold A_k at 1. 
eapply transitive_red. 
eapply2 star_beta2. 
unfold subst; rewrite ! subst_rec_preserves_app_comb. 
unfold subst_rec; fold subst_rec. insert_Ref_out. 
unfold lift; rewrite lift_rec_null. 
rewrite subst_rec_lift_rec; try omega.
unfold subst_rec; fold subst_rec. insert_Ref_out. 
unfold lift; rewrite ! lift_rec_null.
rewrite ! (subst_rec_closed a_op). 
unfold A_k; split_all. 
unfold_op; auto.
(* 1 *) 
replace (A_k (S (S(S(S k))))) with 
(star (star (app_comb (A_k (S(S(S k)))) (app_comb (Ref 1) (Ref 0))))).
2: unfold A_k; auto.  
eapply transitive_red. 
eapply2 star_beta2. 
unfold subst; rewrite ! subst_rec_preserves_app_comb.
rewrite ! (subst_rec_closed (A_k _)). 
2: rewrite A_k_closed; auto. 
2: rewrite A_k_closed; auto. 
unfold subst_rec; fold subst_rec. insert_Ref_out. 
unfold lift; rewrite lift_rec_null. 
rewrite subst_rec_lift_rec; try omega.
unfold subst_rec; fold subst_rec. insert_Ref_out. 
unfold lift; rewrite ! lift_rec_null.
auto. 
Qed.

(* delete ? 
Definition A31 M := star_opt (app_comb a_op (app_comb (lift 1 M) (Ref 0))).

Lemma A3_red1: forall M, sf_red (App (A_k 3) M) (A31 M).
Proof.
intros; unfold A_k. 
eapply transitive_red. 
eapply2 star_opt_beta. 
unfold subst. 
rewrite subst_rec_preserves_star_opt.
rewrite subst_rec_preserves_app_comb. 
rewrite subst_rec_closed. 
2: unfold a_op; split_all. 
rewrite subst_rec_preserves_app_comb.
eapply2 zero_red. 
Qed .

Definition A32 M N := app_comb a_op (app_comb M N). 

Lemma A3_red2: forall M N, sf_red (App (A31 M) N) (A32 M N).
Proof.
intros; unfold A31. 
eapply transitive_red. 
apply star_opt_beta.
unfold subst.
rewrite ! subst_rec_preserves_app_comb.
rewrite subst_rec_closed.
2: split_all. 
unfold lift; rewrite subst_rec_lift_rec; try omega. 
unfold subst_rec. insert_Ref_out. 
unfold lift; rewrite ! lift_rec_null.
eapply2 zero_red.
Qed.    
  

Definition A33 M N P := app_comb (app_comb M N) P.

Lemma A3_red3: forall M N P, sf_red (App (A32 M N) P) (A33 M N P).
Proof.
intros; unfold A32.
eapply transitive_red. 
eapply app_comb_red.
eapply2 a_op2_red.
Qed. 
  
 
Lemma A3_red4 : forall M N P Q, 
sf_red (App (A33 M N P) Q) (App (App (App M N) P) Q). 
Proof. 
intros. unfold A33. 
eapply transitive_red. 
eapply2 app_comb_red. 
eapply transitive_red. 
eapply preserves_app_sf_red.
eapply2 app_comb_red. auto.  auto.  
Qed. 


(* A4 *) 


Definition A41 M := (star_opt (app_comb (A_k 3) (app_comb (lift 1 M) (Ref 0)))).


Lemma A4_red1: forall M, sf_red (App (A_k 4) M) (A41 M).
Proof.
intros. 
replace (A_k 4) with (star_opt (star_opt (app_comb (A_k 3) (app_comb (Ref 1) (Ref 0)))))
by (unfold A_k; auto).
eapply transitive_red. 
eapply2 star_opt_beta. 
unfold subst. 
rewrite subst_rec_preserves_star_opt.
rewrite ! subst_rec_preserves_app_comb.
rewrite subst_rec_closed. 
2: rewrite A_k_closed; split_all.
unfold subst_rec.  insert_Ref_out. 
eapply2 zero_red. 
Qed. 


Definition A42 M N := app_comb (A_k 3) (app_comb M N).
 
Lemma A4_red2: forall M N, sf_red (App (A41 M) N) (A42 M N).
Proof.
intros; unfold A41.  
eapply transitive_red. 
eapply2 star_opt_beta.
unfold subst; rewrite ! subst_rec_preserves_app_comb.
unfold lift; 
rewrite subst_rec_lift_rec; try omega.
rewrite subst_rec_ref. 
rewrite subst_rec_closed. 
2: rewrite A_k_closed; auto. 
insert_Ref_out. 
unfold lift; rewrite ! lift_rec_null.
eapply2 zero_red.
Qed. 

 
Definition A43 M N P :=  A32 (app_comb M N) P. 

Lemma A4_red3: forall M N P, sf_red (App (A42 M N) P) (A43 M N P).
Proof.
intros; unfold A42.
eapply transitive_red.
eapply2 app_comb_red. 
eapply transitive_red. 
eapply preserves_app_sf_red.
eapply2 A3_red1. auto. 
eapply2 A3_red2.   
Qed. 

  
Definition A44 M N P Q := A33 (app_comb M N) P Q.

Lemma A4_red4 : forall M N P Q, 
sf_red (App (A43 M N P) Q) (A44 M N P Q). 
Proof. 
intros. unfold A43. 
eapply2 A3_red3. 
Qed. 

Lemma A4_red5 : forall M N P Q R, 
sf_red (App (A44 M N P Q) R) (App (App (App (App M N) P) Q) R).
Proof. 
intros. unfold A44.
eapply transitive_red.
eapply2 A3_red4.  
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply2 app_comb_red. auto. auto. auto. 
Qed. 

Lemma A5_red: forall M N P Q R, 
sf_red (App (App (App (App (App (A_k 5) M) N) P) Q) R) (App (App (App (App M N) P) Q) R) .
Proof. 
intros. 
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
instantiate(1:= app_comb (A_k 4) (app_comb M N)).
unfold A_k; auto.
eapply transitive_red.  
eapply star_opt_beta2. 
unfold subst; 
rewrite ! subst_rec_preserves_app_comb.
rewrite ! subst_rec_preserves_star_opt.
rewrite ! subst_rec_preserves_app_comb.
rewrite ! subst_rec_preserves_star_opt.
rewrite ! subst_rec_preserves_app_comb.
unfold subst_rec; fold subst_rec. 
insert_Ref_out. 
unfold subst_rec; fold subst_rec. 
insert_Ref_out. 
unfold lift; rewrite ! lift_rec_null. 
rewrite subst_rec_lift_rec; try omega. 
rewrite ! subst_rec_closed. 
2: unfold_op; simpl; auto. 
2: unfold_op; simpl; auto. 
all: auto. 
rewrite lift_rec_null. auto. 
(* 1 *) 
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply2 app_comb_red. 
all: auto. 
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply2 A4_red1.
all: auto. 
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply2 A4_red2.
all: auto. 
eapply transitive_red. 
eapply preserves_app_sf_red. 
eapply2 A4_red3.  all: auto. 
eapply transitive_red.
 eapply2 A4_red4.
unfold A44. unfold A33.  preserves_app_sf_red. 
instantiate(1:= app_comb (A_k 4) (app_comb M N)).
unfold A_k; auto.
eapply transitive_red.  
eapply star_opt_beta2. 
unfold subst; 
rewrite ! subst_rec_preserves_app_comb.
rewrite ! subst_rec_preserves_star_opt.
rewrite ! subst_rec_preserves_app_comb.
rewrite ! subst_rec_preserves_star_opt.
rewrite ! subst_rec_preserves_app_comb.
unfold subst_rec; fold subst_rec. 
insert_Ref_out. 
unfold subst_rec; fold subst_rec. 
insert_Ref_out. 
unfold lift; rewrite ! lift_rec_null. 
rewrite subst_rec_lift_rec; try omega. 
rewrite ! subst_rec_closed. 
2: unfold_op; simpl; auto. 
2: unfold_op; simpl; auto. 
all: auto. 
rewrite lift_rec_null. auto. 




unfold A_k; fold A_k. 

*) 

Ltac nf_out :=
  unfold a_op; unfold_op;
  match goal with
    | |- normal ?M =>
      match M with
        | star_opt _ => apply star_opt_normal; nf_out
        | app_comb _ _ => apply app_comb_normal; nf_out
        | App (App (Op _) _) _ => apply nf_compound; [| |auto]; nf_out
        | App (Op _) _ => apply nf_compound; [| |auto]; nf_out
        | lift _ _ => unfold lift; nf_out
        | lift_rec _ _ _ => eapply2 lift_rec_preserves_normal; nf_out
        | _ => split_all
      end
    | _ => auto
        end.

