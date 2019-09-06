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
(* 02110-1301 USA                                                     *)


(**********************************************************************)
(*                      Equal.v                                       *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)


Require Import ArithRing Bool Max Omega.
Require Import IntensionalLib.SF_calculus.Test.  
Require Import IntensionalLib.SF_calculus.SF_Terms.  
Require Import IntensionalLib.SF_calculus.General.  
Require Import IntensionalLib.SF_calculus.SF_Tactics.  
Require Import IntensionalLib.SF_calculus.SF_reduction.  
Require Import IntensionalLib.SF_calculus.SF_Normal.  
Require Import IntensionalLib.SF_calculus.SF_Closed.  
Require Import IntensionalLib.SF_calculus.Substitution.  
Require Import IntensionalLib.SF_calculus.SF_Eval.  
Require Import IntensionalLib.SF_calculus.Star.  
Require Import IntensionalLib.SF_calculus.Fixpoints.  


(* General equality *)



Definition S_not_F M :=
  App (App (App (App M (Op Fop)) (App (Op Fop) (Op Fop))) (App (Op Fop) (Op Fop)))
      (App (App (Op Sop) (App (Op Fop) (Op Fop))) (App (Op Fop) (Op Fop))).

Lemma S_not_F_S: sf_red (S_not_F (Op Sop)) k_op. 
Proof. unfold_op; repeat eval_tac . 
eapply transitive_red. eapply succ_red. eapply2 f_compound_red.  
repeat eval_tac. repeat eval_tac. 
Qed.

Lemma S_not_F_F: sf_red (S_not_F (Op Fop)) (App k_op i_op). 
Proof. repeat eval_tac . Qed. 

Definition eq_op M N := iff (S_not_F M) (S_not_F N). 

Lemma eq_op_true: forall o, sf_red (eq_op (Op o) (Op o)) k_op. 
Proof. unfold eq_op; unfold_op; split_all; case o; repeat eval_tac .
eapply transitive_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. eapply succ_red. eapply2 f_compound_red. 
repeat eval_tac.  repeat eval_tac. repeat eval_tac.  repeat eval_tac.
eapply succ_red. eapply2 f_compound_red. 
repeat eval_tac. 
 Qed. 

Lemma eq_op_false: forall o1 o2, o1<>o2 -> sf_red(eq_op(Op o1) (Op o2)) (App k_op i_op). 
Proof. 
  unfold eq_op; unfold_op; intros.  
  gen_case H o1; gen_case H o2; try discriminate; repeat eval_tac.
assert False by eapply2 H; noway. 
3: assert False by eapply2 H; noway.
(* 2 *)  
eapply transitive_red.  eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply succ_red. eapply2 f_compound_red. repeat eval_tac.
repeat eval_tac. repeat eval_tac. repeat eval_tac.
(* 1 *) 
eapply transitive_red.  eapply preserves_app_sf_red.  eapply preserves_app_sf_red. 
eapply succ_red. eapply2 f_compound_red. repeat eval_tac. auto. auto. 
repeat eval_tac. 
Qed. 

(*
Lemma eq_op_val : forall M, eq_op M = App
     (App (Op Sop)
        (App
           (App (Op Sop)
              (App (App (Op Fop) (Op Fop))
                 (App
                    (App (App (App M (Op Fop)) (App (Op Fop) (Op Fop)))
                       (App (Op Fop) (Op Fop)))
                    (App (App (Op Sop) (App (Op Fop) (Op Fop)))
                       (App (Op Fop) (Op Fop))))))
           (App
              (App (Op Sop)
                 (App
                    (App (Op Sop)
                       (App
                          (App (Op Sop)
                             (App
                                (App (Op Sop)
                                   (App
                                      (App (Op Sop) (App (Op Fop) (Op Fop)))
                                      (App (Op Fop) (Op Fop))))
                                (App (App (Op Fop) (Op Fop)) (Op Fop))))
                          (App (App (Op Fop) (Op Fop))
                             (App (Op Fop) (Op Fop)))))
                    (App (App (Op Fop) (Op Fop)) (App (Op Fop) (Op Fop)))))
              (App (App (Op Fop) (Op Fop))
                 (App (App (Op Sop) (App (Op Fop) (Op Fop)))
                    (App (Op Fop) (Op Fop)))))))
     (App
        (App (Op Sop)
           (App
              (App (Op Sop)
                 (App
                    (App (Op Sop)
                       (App
                          (App (Op Sop)
                             (App
                                (App (Op Sop)
                                   (App
                                      (App (Op Sop)
                                         (App
                                            (App (Op Sop)
                                               (App (Op Fop) (Op Fop)))
                                            (App (Op Fop) (Op Fop))))
                                      (App (App (Op Fop) (Op Fop)) (Op Fop))))
                                (App (App (Op Fop) (Op Fop))
                                   (App (Op Fop) (Op Fop)))))
                          (App (App (Op Fop) (Op Fop))
                             (App (Op Fop) (Op Fop)))))
                    (App (App (Op Fop) (Op Fop))
                       (App (App (Op Sop) (App (Op Fop) (Op Fop)))
                          (App (Op Fop) (Op Fop))))))
              (App (App (Op Fop) (Op Fop))
                 (App (App (Op Fop) (Op Fop))
                    (App (App (Op Sop) (App (Op Fop) (Op Fop)))
                       (App (Op Fop) (Op Fop)))))))
        (App (App (Op Fop) (Op Fop)) (App (Op Fop) (Op Fop)))). 
Proof. 
intro. unfold eq_op, iff, not; unfold_op.  simpl. 
replace (lift_rec M 0 1) with (lift 1 M) by auto. 
rewrite star_opt_opt2. auto.  
Qed. 

*)


Lemma maxvar_eq_op: forall M N, maxvar (eq_op M N) = max (maxvar M) (maxvar N).
Proof. 
intros; split_all. repeat rewrite max_zero.
assert(Nat.max (Nat.max (maxvar M) (maxvar N)) (maxvar N) >= Nat.max (maxvar M) (maxvar N)).
eapply2 max_max2. max_l. max_l. max_r. 
assert(Nat.max (maxvar M) (maxvar N) >= Nat.max (Nat.max (maxvar M) (maxvar N)) (maxvar N)).
eapply2 max_max2. max_r. omega. 
Qed. 

Hint Resolve maxvar_eq_op. 

Definition equal_body:=  
  App
     (App (App (Op Fop) (Ref 1))
        (App (App (App (Op Fop) (Ref 0)) (eq_op (Ref 1) (Ref 0))) 
             (App k_op (App k_op (App k_op i_op))))) 
     (star_opt (star_opt (App (App (App (Op Fop) (Ref 2)) (App k_op i_op))
        (star_opt (star_opt (App (App (App (App (Ref 6) (Ref 3)) (Ref 1))
                                      (App (App (Ref 6) (Ref 2)) (Ref 0)))
                                 (App k_op i_op)))))))
. 

  

Definition equal_fn := star_opt (star_opt (star_opt equal_body)). 

Lemma equal_fn_closed: maxvar equal_fn = 0.
Proof. cbv; auto.   Qed. 

Definition equal_comb := Y3 equal_fn. 

Lemma equal_comb_closed : maxvar equal_comb = 0.
Proof. cbv; omega. Qed. 

Lemma equal_comb_normal: normal equal_comb.
Proof. cbv;  nf_out. Qed. 
 
Lemma equal_comb_op : forall o, sf_red (App (App equal_comb (Op o)) (Op o)) k_op.
Proof. 
  intros; cbv.
  do 131 eval_tac. case o; eval_tac.
  (* 2 *)
  eval_tac.
  eapply transitive_red. eapply preserves_app_sf_red. 
  eapply preserves_app_sf_red. eapply succ_red. eapply2 f_compound_red.
  all: eval_tac. repeat eval_tac. 
  eapply succ_red. eapply2 f_compound_red. repeat eval_tac.
  (* 1 *)
  repeat eval_tac. 
Qed.


Lemma unequal_op_compound : 
forall M o, compound M -> 
              sf_red (App (App equal_comb (Op o)) M) (App k_op i_op). 
Proof. 
  intros; cbv.
  do 102 eval_tac.
 eapply transitive_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
auto. eval_tac. eval_tac. eval_tac.
eapply succ_red. eapply2 f_compound_red.
repeat eval_tac. 
Qed.


Lemma unequal_op : 
forall M o, factorable M-> M <> (Op o) -> 
              sf_red (App (App equal_comb (Op o)) M) (App k_op i_op). 
Proof. 
  intros.
  unfold factorable in *. inversion H. inversion H1; subst. 
  2: eapply2 unequal_op_compound. 
  (* 1 *)
  cbv. do 130 eval_tac.
  gen_case H0 o.
  (* 2 *)
  do 20 eval_tac.   
 eapply transitive_red. eapply preserves_app_sf_red. 
 eapply preserves_app_sf_red.
 eapply succ_red. eapply2 f_compound_red. all: eval_tac. 
 do 16 eval_tac.
 gen_case H0 x; eval_tac.
 congruence. 
 repeat eval_tac.  
 (* 1 *)
 do 20 eval_tac. eval_tac. eval_tac. 
 gen_case H0 x; eval_tac.
 2: congruence. 
 repeat eval_tac.  
 eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red. 
 eapply succ_red. eapply2 f_compound_red. 
 all: repeat eval_tac.
Qed. 



Lemma unequal_compound_op : 
forall M o, compound M -> 
              sf_red (App (App equal_comb M) (Op o))(App k_op i_op).
Proof.
  intros. cbv.  do 91 eval_tac.
 eapply transitive_red. eapply preserves_app_sf_red. 
 eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
 auto.  eval_tac. eval_tac. eval_tac.
  eapply succ_red. eapply2 f_compound_red. repeat eval_tac. 
Qed. 



Lemma unequal_op2 : 
forall M o, normal M -> maxvar M = 0 -> M <> (Op o) -> 
              sf_red (App (App equal_comb M) (Op o))(App k_op i_op).
Proof. 
split_all.
assert((exists o, M = (Op o)) \/ compound M) .
eapply2 programs_are_factorable. 
unfold program; auto.
inversion H2. 
2: eapply2 unequal_compound_op. 
split_all. inversion H3; subst. eapply2 unequal_op.
unfold factorable; eauto.   
Qed. 


Lemma equal_compounds : 
forall M N, compound M -> compound N -> 
sf_red (App (App equal_comb M) N) 
        (App (App 
                (App (App equal_comb (left_component M)) 
                     (left_component N))
                (App (App equal_comb (right_component M)) 
                     (right_component N)))
             (App k_op i_op))
.
Proof.
  split_all. 
eapply transitive_red.  unfold equal_comb; unfold_op.  eapply2 Y3_fix. 
replace (Y3 equal_fn) with equal_comb by auto. 
unfold equal_fn, equal_body, star_opt, occurs0, eq_op, subst; simpl.
do 13 eval_tac. eapply succ_red. eapply2 f_compound_red. 
do 19 eval_tac. eapply succ_red. eapply2 f_compound_red. 
do 59 eval_tac. 
eapply2 preserves_app_sf_red. eapply2 preserves_app_sf_red. all: repeat eval_tac.
Qed.

Theorem equal_programs : forall M, program M -> sf_red (App (App equal_comb M) M) k_op.
Proof. 
cut(forall p M, p >= rank M -> program M -> 
sf_red (App (App equal_comb M) M) k_op)
.
unfold program; split_all. eapply2 H. 
induction p; split_all. 
assert(rank M >0) by eapply2 rank_positive. noway. 
(* p > 0 *)
assert(factorable M) . eapply2 programs_are_factorable.  
inversion H1; split_all; subst.  inversion H2; subst. 
eapply2 equal_comb_op.
apply transitive_red with 
(App (App (App (App equal_comb (left_component M)) (left_component M))
          (App (App equal_comb (right_component M)) (right_component M))) 
     (App k_op i_op))
.
eapply2 equal_compounds. 

apply transitive_red with (App (App k_op k_op) (App k_op i_op)).
eapply2 preserves_app_sf_red. 
eapply2 preserves_app_sf_red. 
(* left *) 
eapply2 IHp.  
assert(rank (left_component M) < rank M) by eapply2 rank_compound_l. 
omega. 
unfold program in *; split_all. inversion H0. split. 
inversion H3; cbv; auto.
assert(maxvar (left_component M) <= maxvar M) by 
(eapply2 left_component_preserves_maxvar). 
omega. 
(* right *) 
eapply2 IHp.  
assert(rank (right_component M) < rank M) .  eapply2 rank_compound_r. 
omega. 
unfold program in *; split_all. inversion H0.  split. 
inversion H2; subst; split_all; inversion H3; auto; inversion H6; auto. 
assert(maxvar (right_component M) <= maxvar M) by 
(eapply2 right_component_preserves_maxvar). 
omega. 
(* 1*)
repeat eval_tac; auto. 
Qed. 



Theorem unequal_programs : forall M N, program M -> program N -> M<>N ->
                                       sf_red (App (App equal_comb M) N) (App k_op i_op).

Proof. 
cut(forall p  M N, p >= rank M -> program M -> program N -> M<>N ->  
sf_red (App (App equal_comb M) N) (App k_op i_op)
). 
split_all. eapply2 H. 
induction p; split_all. 
assert(rank M >0) by eapply2 rank_positive. noway. 
(* p > 0 *)
assert(factorable M) by eapply2 programs_are_factorable.  
assert(factorable N) by eapply2 programs_are_factorable.  
unfold program in *. 
inversion H3; inversion H4; split_all. inversion H5; inversion H6; subst.   
eapply2 unequal_op.
inversion H5; subst. inversion H1. eapply2 unequal_op.
inversion H6; inversion H0; subst. eapply2 unequal_compound_op.
(* both compounds *) 
apply transitive_red with 
(App (App (App (App equal_comb (left_component M)) (left_component N))
          (App (App equal_comb (right_component M)) (right_component N)))
     (App k_op i_op))
.
eapply2 equal_compounds.  inversion H0; inversion H1. 

assert(left_component M = left_component N \/ left_component M <> left_component N) 
by repeat (decide equality). 
assert(right_component M = right_component N \/ right_component M <> right_component N) 
by repeat (decide equality). 
inversion H11. 
inversion H12. 
(* 3 *) 
assert False. eapply2 H2. 
eapply2 components_monotonic; split_all. noway. 
(* 2 *) 
apply transitive_red with (App (App k_op (App k_op i_op)) (App k_op i_op)).
eapply2 preserves_app_sf_red. 
eapply2 preserves_app_sf_red. 
rewrite H13. eapply2 equal_programs.
unfold program; split. 
inversion H9; subst; split_all;  unfold_op; auto. 
assert(maxvar (left_component N) <= maxvar N) by 
(eapply2 left_component_preserves_maxvar). 
omega. 
eapply2 IHp.  
assert(rank (right_component M) < rank M) by eapply2 rank_compound_r. 
omega. 
split. 
inversion H7; subst; split_all. 
assert(maxvar (right_component M) <= maxvar M) by 
(eapply2 right_component_preserves_maxvar). 
omega. 
split. 
inversion H9; subst; split_all. 
assert(maxvar (right_component N) <= maxvar N) by 
(eapply2 right_component_preserves_maxvar). 
omega. 
eval_tac. 
(* 1 *) 
apply transitive_red with (App (App (App k_op i_op) (App (App equal_comb (right_component M)) (right_component N))) (App k_op i_op)).
eapply2 preserves_app_sf_red. 
eapply2 preserves_app_sf_red. 
eapply2 IHp.  
assert(rank (left_component M) < rank M) by eapply2 rank_compound_l. 
omega. 
split. 
inversion H7; subst; split_all. 
unfold_op; auto. unfold_op; auto. 
assert(maxvar (left_component M) <= maxvar M) by 
(eapply2 left_component_preserves_maxvar). 
omega. 
split. 
inversion H9; subst; split_all. 
unfold_op; auto. unfold_op; auto. 
assert(maxvar (left_component N) <= maxvar N) by 
(eapply2 left_component_preserves_maxvar). 
omega.  
repeat eval_tac.  
Qed. 


Fixpoint size M := 
match M with 
| Ref _ => 1 
| Op _ => 1
| App M1 M2 => S(size M2 + size M1)
end . 

Lemma size_equal_comb : size equal_comb = 1709. 
Proof. cbv; auto. Qed. 

