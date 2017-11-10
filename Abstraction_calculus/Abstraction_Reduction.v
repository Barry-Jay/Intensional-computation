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

Add LoadPath ".." as IntensionalLib.

Require Import Arith.
Require Import IntensionalLib.SF_calculus.General.
Require Import IntensionalLib.Abstraction_calculus.Abstraction_Terms. 
Require Import IntensionalLib.Abstraction_calculus.Abstraction_Tactics.


Ltac split_all := simpl; intros; 
match goal with 
| H : _ /\ _ |- _ => inversion_clear H; split_all
| H : exists _, _ |- _ => inversion H; clear H; split_all 
| _ =>  try (split; split_all); try contradiction
end; try congruence; auto.

Definition s_op := Op Sop.
Definition k_op := Op Kop. 
Definition i_op := Op Iop. 
Ltac unfold_op := unfold i_op, id, k_op, s_op. 



(* compounds *) 

Fixpoint right_component (M : Term) := 
match M with 
| App _ M2 => M2
| _ => M
end.

Definition left_component (U : Term) := 
match U with 
| App U1 _ => U1 
| _ => i_op
end.


Inductive true_compound : Term -> Prop := 
| s2_compound : forall M N, true_compound (App (App (Op Sop) M) N)
| s_compound : forall M, true_compound (App (Op Sop) M) 
| k_compound : forall M, true_compound (App (Op Kop) M) 
| e_compound : forall M, true_compound (App (Op Eop) M) 
| t_compound : forall M, true_compound (App (Op Tag) M) 
| add2_compound : forall x u, true_compound (App (App (Op Add) x) u)
| add_compound : forall x, true_compound (App (Op Add) x)
| abs2_compound : forall sigma x, true_compound (App (App (Op Abs) sigma) x)
| abs_compound : forall sigma, true_compound (App (Op Abs) sigma)
. 

Inductive compound : Term -> Prop := 
| is_true_compound: forall M, true_compound M -> compound M
| t_lam : forall M N, compound (App (App (Op Tag) M) N)
| v_lam : forall M, compound (App (Op Var) M) 
| add_lam : forall x u sigma, compound (App (App (App (Op Add) x) u) sigma)
| abs_lam : forall x u sigma, compound (App (App (App (Op Abs) sigma) x) u) 
.


Hint Constructors true_compound compound. 

Definition preserves_true_compound (red:termred) := 
forall M, true_compound M -> forall N, red M N -> 
true_compound N /\ red (left_component M) (left_component N) /\ red(right_component M) (right_component N).


Lemma preserves_true_compound_seq : 
forall (red1 red2:termred), preserves_true_compound red1 -> preserves_true_compound red2 -> 
                            preserves_true_compound (sequential red1 red2). 
Proof. 
red; split_all.  
inversion H2. 
elim(H M H1 N0); split_all.  
eapply2 H0. 
inversion H2. 
elim(H M H1 N0); split_all. 
elim(H0 N0 H9 N); split_all. 
eapply2 seq_red. 
inversion H2. 
elim(H M H1 N0); split_all. 
elim(H0 N0 H9 N); split_all. 
eapply2 seq_red. 
Qed. 


Lemma preserves_true_compound_multi_step : 
forall (red:termred), preserves_true_compound red -> preserves_true_compound (multi_step red). 
Proof. 
red. intros red p M c N R; induction R; split_all. 
eapply2 IHR. eapply2 p.
apply succ_red with (left_component N); auto. 
 eapply2 p. eapply2 IHR. eapply2 p.
apply succ_red with (right_component N); auto. 
 eapply2 p. eapply2 IHR. eapply2 p.
Qed. 

Hint Resolve preserves_true_compound_multi_step.

Definition preserves_compound (red:termred) := 
forall M, compound M -> forall N, red M N -> 
compound N /\ red (left_component M) (left_component N) /\ red(right_component M) (right_component N).


Lemma preserves_compound_multi_step : 
forall (red:termred), preserves_compound red -> preserves_compound (multi_step red). 
Proof. 
red. intros red p M c N R; induction R; split_all. 
eapply2 IHR. eapply2 p.
apply succ_red with (left_component N); auto. 
 eapply2 p. eapply2 IHR. eapply2 p.
apply succ_red with (right_component N); auto. 
 eapply2 p. eapply2 IHR. eapply2 p.
Qed. 

Hint Resolve preserves_compound_multi_step.




Definition factorable M := (exists o, M = Op o) \/ compound M.




(* Term-reduction  *) 


Inductive c_red1 : Term -> Term -> Prop := 
  | appl_c_red :  forall M M' N, c_red1 M M' -> c_red1 (App M N) (App M' N)  
  | appr_c_red :  forall M N N', c_red1 N N' -> c_red1 (App M N) (App M N')  
  | s_red: forall (M N P : Term),
             c_red1 
                   (App (App (App (Op Sop) M) N) P) 
                  (App (App M P) (App N P))
  | k_red : forall M N, c_red1 (App (App (Op Kop) M) N) M
  | i_red : forall M, c_red1 (App (Op Iop) M) M
  | e_K_red: forall o, c_red1 (App (App (Op Eop) (Op o)) (Op o)) k_op 
  | e_op_factorable_red: forall o N, factorable N -> Op o <> N -> 
                             c_red1 (App (App (Op Eop) (Op o)) N) (App k_op i_op)
  | e_compound_op_red: forall M o , compound M -> 
                             c_red1 (App (App (Op Eop) M) (Op o)) (App k_op i_op)
  | e_compounds_red : forall M N, compound M -> compound N -> 
     c_red1 (App (App (Op Eop) M) N) 
            (App (App (App (App (Op Eop) (left_component M)) (left_component N))
                      (App (App (Op Eop) (right_component M)) (right_component N)))
                 (App k_op i_op))
  | tag_red: forall (M N P : Term),
             c_red1 (App (App (App (Op Tag) M) N) P) 
                    (App (App (Op Tag) (App (App (Op Tag) M) N)) P)
  | var_red: forall M N, c_red1 (App (App (Op Var) M) N) 
                                (App (App (Op Tag) (App (Op Var) M)) N)
  | add_op_red: forall x u sigma o, 
                  c_red1 (App (App (App (App (Op Add) sigma) x) u) (Op o)) (App sigma (Op o))
  | add_true_compound_red: forall x u sigma M, true_compound M -> 
                  c_red1 (App (App (App (App (Op Add) sigma) x) u) M)
                         (App (App (App (App (App (Op Add) sigma) x) u)(left_component M))
                              (App (App (App (App (Op Add) sigma) x) u)(right_component M)))
  | add_tag_red: forall x u sigma M N, 
                  c_red1 (App (App (App (App (Op Add) sigma) x) u)
                              (App (App (Op Tag) M) N))
                         (App (App (App (App (App (Op Add) sigma) x) u)M)
                              (App (App (App (App (Op Add) sigma) x) u)N))
  | add_var_red: forall x u sigma M, 
                  c_red1 (App (App (App (App (Op Add) sigma) x) u)(App (Op Var) M))
                         (App (App (App (App (Op Eop) x) M) u) (App sigma (App (Op Var) M)))
  | add_add_red: forall x u sigma y v sigma2, 
                  c_red1 (App (App (App (App (Op Add) sigma) x) u)
                               (App (App (App (Op Add) sigma2) y) v))
                         (App (App (App (Op Add) 
                                        (App (App (App (App (Op Add) sigma) x) u) sigma2))
                                   y) 
                              (App (App (App (App (Op Add) sigma) x) u)v))
  | add_abs_red: forall x u sigma y sigma2 t, 
                  c_red1 (App (App (App (App (Op Add) sigma)  x) u)
                               (App (App (App (Op Abs) sigma2) y) t))
                         (App (App (App (Op Abs) 
                                        (App (App (App (App (Op Add) sigma) x) u)sigma2))
                                   y)
                               t)
  | beta_red : forall x sigma t u,  
                 c_red1 (App (App (App (App (Op Abs) sigma) x) t) u)
                        (App (App (App (App (Op Add) sigma) x) u) t)
.

Definition c_red := multi_step c_red1. 

Hint Constructors c_red1 .



Lemma reflective_c_red: reflective c_red. 
Proof. red; red; reflect. Qed. 
Hint Resolve reflective_c_red.

Definition preserves_apl (red : termred) := 
forall M M' N, red M M' -> red (App M N) (App M' N).

Definition preserves_apr (red : termred) := 
forall M N N', red N N' -> red (App M N) (App M N').

Lemma preserves_apl_multi_step : forall (red: termred), preserves_apl red -> preserves_apl (multi_step red). 
Proof. red. induction 2; split_all. apply succ_red with (App N0 N); auto. Qed. 

Lemma preserves_apr_multi_step : forall (red: termred), preserves_apr red -> preserves_apr (multi_step red). 
Proof. red. induction 2; split_all. apply succ_red with (App M N); auto. Qed. 


Lemma preserves_apl_c_red: preserves_apl c_red. 
Proof. eapply2 preserves_apl_multi_step. red; split_all.  Qed.
Hint Resolve preserves_apl_c_red.

Lemma preserves_apr_c_red: preserves_apr c_red. 
Proof. eapply2 preserves_apr_multi_step. red; split_all.  Qed.
Hint Resolve preserves_apr_c_red.

Lemma preserves_app_c_red: preserves_app c_red. 
Proof. 
red; split_all. 
apply transitive_red with (App M' N); split_all. 
eapply2 preserves_apl_c_red. 
eapply2 preserves_apr_c_red. 
Qed. 
Hint Resolve preserves_app_c_red.


Lemma preserves_true_compound_c_red1: forall M N : Term,
   c_red1 M N ->
   true_compound M ->
   true_compound N /\
   c_red (left_component M) (left_component N) /\
   c_red (right_component M) (right_component N).
Proof. 
intros M N R; induction R; intro c; inversion c; split_all; subst; 
inv c_red1; try (eapply2 zero_red; fail); try (red; one_step; fail). 
Qed. 

Lemma preserves_compound_c_red1: forall M N : Term,
   c_red1 M N ->
   compound M ->
   compound N /\
   c_red (left_component M) (left_component N) /\
   c_red (right_component M) (right_component N).
Proof. 
  intros M N R; induction R; intro c; inversion c; split_all; subst; inv c_red1;
  try (inv1 true_compound; fail); 
  try (eapply2 zero_red; fail); try (red; one_step; fail).
  match goal with | H: true_compound ?P |- compound ?Q => 
                         apply is_true_compound;
                              elim(preserves_true_compound_c_red1 P Q); split_all
       end. 
Qed.

Lemma preserves_compound0_c_red:
  forall red M N, multi_step red M N -> red = c_red1 -> compound M -> compound N.
Proof.
  intros red M N r; induction r; split_all; subst. eapply2 IHr. eapply2 preserves_compound_c_red1. 
Qed.

Lemma preserves_compound_l_c_red:
  forall red M N, multi_step red M N -> red = c_red1 -> compound M ->
                  c_red (left_component M) (left_component N).
Proof.
  intros red M N r; induction r; split_all; subst. 
  eapply transitive_red. eapply2 preserves_compound_c_red1. eapply2 IHr.
  eapply2 preserves_compound_c_red1. 
Qed.

Lemma preserves_compound_r_c_red:
  forall red M N, multi_step red M N -> red = c_red1 -> compound M ->
                  c_red (right_component M) (right_component N).
Proof.
  intros red M N r; induction r; split_all; subst. 
  eapply transitive_red. eapply2 preserves_compound_c_red1. eapply2 IHr.
  eapply2 preserves_compound_c_red1. 
Qed.



Inductive p_red1 : Term -> Term -> Prop := 
  | op_p_red :  forall o, p_red1 (Op o) (Op o)
  | app_p_red :  forall M M' N N', p_red1 M M' -> p_red1 N N' -> p_red1 (App M N) (App M' N')  
  | s_p_red: forall (M M' N N' P P': Term), p_red1 M M' -> p_red1 N N' -> p_red1 P P' ->
             p_red1 
                   (App (App (App (Op Sop) M) N) P) 
                  (App (App M' P') (App N' P'))
  | k_p_red : forall M M' N, p_red1 M M' -> p_red1 (App (App (Op Kop) M) N) M'
  | i_p_red : forall M M', p_red1 M M' -> p_red1 (App (Op Iop) M) M'
  | e_K_p_red: forall o, p_red1 (App (App (Op Eop) (Op o)) (Op o)) k_op 
  | e_op_factorable_p_red: forall o N, factorable N -> Op o <> N -> 
                             p_red1 (App (App (Op Eop) (Op o)) N) (App k_op i_op)
  | e_compound_op_p_red: forall M o , compound M -> 
                             p_red1 (App (App (Op Eop) M) (Op o)) (App k_op i_op)
  | e_compounds_p_red : forall M M' N N', compound M -> compound N -> p_red1 M M' -> p_red1 N N' -> 
     p_red1 (App (App (Op Eop) M) N) 
            (App (App (App (App (Op Eop) (left_component M')) (left_component N'))
                      (App (App (Op Eop) (right_component M')) (right_component N')))
                 (App k_op i_op))
  | tag_p_red: forall (M M' N N' P P': Term), p_red1 M M' -> p_red1 N N' -> p_red1 P P' ->
             p_red1 (App (App (App (Op Tag) M) N) P) 
                    (App (App (Op Tag) (App (App (Op Tag) M') N')) P')
  | var_p_red: forall (M M' N N': Term), p_red1 M M' -> p_red1 N N' ->
                                         p_red1 (App (App (Op Var) M) N) 
                                                (App (App (Op Tag) (App (Op Var) M')) N')
  | add_op_p_red: forall x u sigma sigma' o, p_red1 sigma sigma' -> 
                  p_red1 (App (App (App (App (Op Add) sigma)  x) u)(Op o)) (App sigma' (Op o))
  | add_true_compound_p_red: forall x x' u u' sigma sigma' M M', true_compound M ->
                             p_red1 x x' -> p_red1 u u' -> p_red1 sigma sigma' -> p_red1 M M' -> 
                  p_red1 (App (App (App (App (Op Add) sigma)  x) u)M)
                         (App (App (App (App (App (Op Add)  sigma') x') u')(left_component M'))
                              (App (App (App (App (Op Add) sigma') x') u') (right_component M')))
  | add_tag_p_red: forall x x' u u' sigma sigma' M M' N N', 
                   p_red1 x x' -> p_red1 u u' -> p_red1 sigma sigma' -> p_red1 M M' -> p_red1 N N' ->
                  p_red1 (App (App (App (App (Op Add) sigma)  x) u)
                              (App (App (Op Tag) M) N))
                         (App (App (App (App (App (Op Add)  sigma') x') u') M')
                              (App (App (App (App (Op Add) sigma') x') u')  N'))
  | add_var_p_red: forall x x' u u' sigma sigma' M M', 
                             p_red1 x x' -> p_red1 u u' -> p_red1 sigma sigma' -> p_red1 M M' -> 
                  p_red1 (App (App (App (App (Op Add) sigma)  x) u)(App (Op Var) M))
                         (App (App (App (App (Op Eop) x') M') u') (App sigma' (App (Op Var) M')))
  | add_add_p_red: forall x x' u u' sigma sigma' y y' v v' sigma2 sigma2', 
                     p_red1 x x' -> p_red1 u u' -> p_red1 sigma sigma' -> p_red1 y y' ->
                     p_red1 v v' -> p_red1 sigma2 sigma2' ->
                     p_red1 (App (App (App (App (Op Add) sigma)  x) u)
                               (App (App (App (Op Add) sigma2) y) v))
                         (App (App (App (Op Add) 
                                        (App (App (App (App (Op Add) sigma') x') u') sigma2'))
                                    y')
                               (App (App (App (App (Op Add) sigma') x') u') v'))
  | add_abs_p_red: forall x x' u u' sigma sigma' y y' sigma2 sigma2' t t', 
                     p_red1 x x' -> p_red1 u u' -> p_red1 sigma sigma' -> 
                     p_red1 y y' -> p_red1 sigma2 sigma2' -> p_red1 t t' ->
                  p_red1 (App (App (App (App (Op Add) sigma)  x) u)
                               (App (App (App (Op Abs) sigma2) y) t))
                         (App (App (App (Op Abs) 
                                   (App (App (App (App (Op Add) sigma') x') u') sigma2'))
 y') 
                              t')
  | beta_p_red : forall x x' sigma sigma' t t' u u',
p_red1 x x' -> p_red1 sigma sigma' -> p_red1 t t' -> p_red1 u u' -> 
                 p_red1 (App (App (App (App (Op Abs) sigma) x) t) u)
                        (App (App (App (App (Op Add) sigma') x') u') t')
.

Definition p_red := multi_step p_red1. 

Hint Constructors p_red1 .



Lemma reflective_p_red1 : reflective p_red1.
Proof. red; induction M; split_all. Qed. 
Hint Resolve reflective_p_red1. 

Lemma reflective_p_red : reflective p_red.
Proof. unfold p_red; eapply2 refl_multi_step. Qed. 
Hint Resolve reflective_p_red. 



Lemma preserves_app_p_red : preserves_app p_red.
Proof. eapply2 preserves_app_multi_step. red; split_all. Qed.
Hint Resolve  preserves_app_p_red. 


Lemma preserves_true_compound_p_red1:
forall M, true_compound M -> forall N, p_red1 M N -> 
true_compound N /\ 
p_red1 (left_component M) (left_component N) /\ 
p_red1(right_component M) (right_component N). 
Proof. intros; inversion H; subst; inv p_red1; auto. Qed. 

Hint Resolve preserves_true_compound_p_red1.

Lemma  preserves_compound_p_red1: 
forall M, compound M -> forall N, p_red1 M N -> 
compound N /\ 
p_red1 (left_component M) (left_component N) /\ 
p_red1(right_component M) (right_component N). 
Proof.
  intros; inversion H; subst; inv p_red1; split_all.
  eapply2 is_true_compound. eapply2 preserves_true_compound_p_red1.
eapply2 preserves_true_compound_p_red1. eapply2 preserves_true_compound_p_red1.
Qed. 

Hint Resolve preserves_compound_p_red1 .

Lemma  preserves_compound_p_red: preserves_compound p_red.
Proof. 
eapply2 preserves_compound_multi_step. 
split_all; eapply2 preserves_compound_p_red1. 
Qed.
Hint Resolve preserves_compound_p_red .


Ltac app_op := unfold_op; 
match goal with 
| |- p_red _ _ => red; app_op
| |- multi_step p_red1 (Op _) (Op _) => red; one_step; app_op
| |- multi_step p_red1 (App _ _) (App _ _) => eapply2 preserves_app_p_red ; app_op
| |- multi_step p_red1 (left_component _) (left_component _) => eapply2 preserves_compound_p_red; app_op 
| |- multi_step p_red1 (right_component _) (right_component _) => eapply2 preserves_compound_p_red; app_op
| |- p_red1 (App _ _) (App _ _) => eapply2 app_p_red ; app_op
| |- p_red1 (left_component _) (left_component _) => eapply2 preserves_compound_p_red1; app_op 
| |- p_red1 (right_component _) (right_component _) => eapply2 preserves_compound_p_red1; app_op
| H : p_red1 _ _ |- compound _ => eapply2 preserves_compound_p_red1
| |- p_red1 (left_component _) _ => eapply2 preserves_compound_p_red1
| |- p_red1 (right_component _) _ => eapply2 preserves_compound_p_red1
| _ => try red; split_all
end.




Ltac p_red_compound := 
fold p_red in *; 
match goal with 
| H : p_red   (App (App (Op ?o) ?M1) ?M2) ?N |- _ => 
assert(p_red  (right_component (App (App (Op o) M1) M2))
          (right_component N)) by 
eapply2 preserves_compound_p_red;
assert(p_red  (left_component (App (App (Op o) M1) M2))
          (left_component N)) by 
eapply2 preserves_compound_p_red; simpl in *; clear H; p_red_compound
| H : p_red (App (Op ?o) ?M1) ?N  |- _ => 
assert(p_red  (right_component (App (Op o) M1))
          (right_component N)) by 
eapply2 preserves_compound_p_red; clear H; p_red_compound
| _ => simpl in *
end;
simpl in *.


(* Diamond Lemmas *) 


Lemma diamond_p_red1_p_red1 : diamond p_red1 p_red1. 
Proof.  
red; intros M N OR; induction OR; split_all; eauto.

(* 17 subgoals *)
inversion H; clear H; subst;  inv p_red1. 
(* 33 subgoals *) 
elim(IHOR1 M'0); elim(IHOR2 N'0); split_all. eauto.
(* 32 *)
elim(IHOR1 (App (App s_op M'0) N'0)); 
elim(IHOR2 P'); split_all.  unfold s_op in *; inv p_red1. 
invsub. exist(App (App N'4 x) (App N'3 x)). 
(* 31 *)
elim(IHOR1 (App (Op Kop) P)); split_all. inv p_red1. invsub. eauto. 
(* 30 *)
elim(IHOR2 P); split_all; eauto.
(* 29 *)
eauto. 
(* 28 *)
exist (App k_op i_op); split_all. eapply2 e_op_factorable_p_red. 
inversion H2; split_all; subst; inv p_red1.
right. eapply2 preserves_compound_p_red1.
inversion H2; split_all; subst; inv p_red1.
intro; subst. assert(compound (Op o)) by eapply2 preserves_compound_p_red1.
inversion H0. inversion H1.
(* 27 *)
exist (App k_op i_op); split_all. eapply2 e_compound_op_p_red. 
eapply2 preserves_compound_p_red1.
(* 26 *)
elim(IHOR1 (App (Op Eop) M'0)); split_all. elim(IHOR2 N'0); split_all. inv p_red1.  invsub. 
exist(App
          (App (App (App (Op Eop) (left_component N'2)) (left_component x0))
             (App (App (Op Eop) (right_component N'2)) (right_component x0)))
          (App k_op i_op)); split_all. 
eapply2 e_compounds_p_red. eapply2 (preserves_compound_p_red1 M0). 
  eapply2 (preserves_compound_p_red1 N). 
  eapply2 app_p_red.   eapply2 app_p_red.   eapply2 app_p_red.   eapply2 app_p_red. 
eapply2 preserves_compound_p_red1. eapply2 (preserves_compound_p_red1 M0). 
eapply2 preserves_compound_p_red1. eapply2 (preserves_compound_p_red1 N). 
  eapply2 app_p_red.   eapply2 app_p_red.   
eapply2 preserves_compound_p_red1. eapply2 (preserves_compound_p_red1 M0). 
eapply2 preserves_compound_p_red1. eapply2 (preserves_compound_p_red1 N).
(* 25 *)
elim(IHOR1 (App (App (Op Tag) M'0) N'0));  split_all. elim(IHOR2 P'); split_all. inv p_red1.  invsub. 
exist(App (App (Op Tag) (App (App (Op Tag) N'4) N'3)) x0). split_all.  
(* 24 *)
elim(IHOR1  (App (Op Var) M'0));  split_all. elim(IHOR2 N'0); split_all. inv p_red1.  invsub. 
exist(App (App (Op Tag) (App (Op Var) N'2)) x0).
(* 23 *)
elim(IHOR1 (App (App (App (Op Add) sigma') x) u)); split_all. inv p_red1; invsub. 
exist(App N'4 (Op o)). 
(* 22 *)
elim(IHOR1 (App (App (App (Op Add) sigma') x') u')); split_all.  elim(IHOR2 M'0); split_all.
inv p_red1.  invsub. 
exist(App
          (App (App (App (App (Op Add) N'5) N'4) N'3) (left_component x1))
          (App (App (App (App (Op Add) N'5) N'4) N'3) (right_component x1))).  split_all. 
eapply2 add_true_compound_p_red. eapply2 preserves_true_compound_p_red1. 
eapply2 app_p_red. eapply2 app_p_red. eapply2 preserves_true_compound_p_red1. 
eapply2 preserves_true_compound_p_red1. 
eapply2 app_p_red. eapply2 preserves_true_compound_p_red1. 
eapply2 preserves_true_compound_p_red1. 
(* 21 *)
elim(IHOR1 (App (App (App (Op Add) sigma') x') u')); split_all.
elim(IHOR2 (App (App (Op Tag) M'0) N'0)); split_all.
inv p_red1.  invsub. 
exist(App (App (App (App (App (Op Add) N'11) N'10) N'9) N'6)
          (App (App (App (App (Op Add) N'11) N'10) N'9) N')) .
split_all. 
eapply2 app_p_red.
(* 20 *)
elim(IHOR1 (App (App (App (Op Add) sigma') x') u')); split_all.
elim(IHOR2 (App (Op Var) M'0)); split_all.
inv p_red1.  invsub.  
exist(App (App (App (App (Op Eop) N'6) N') N'5)
          (App N'7 (App (Op Var) N'))). split_all. 
(* 19 *)
elim(IHOR1 (App (App (App (Op Add) sigma') x') u')); split_all.
elim(IHOR2 (App (App (App (Op Add) sigma2') y') v')); split_all.
inv p_red1.  invsub. 
exist(App
          (App (App (Op Add) (App (App (App (App (Op Add) N'13) N'12) N'11) N'7))
N'6)
             (App (App (App (App (Op Add) N'13) N'12) N'11) N'))
          .
auto 20.
(* 18 *)
elim(IHOR1 (App (App (App (Op Add) sigma') x') u')); split_all.
elim(IHOR2 (App (App (App (Op Abs) sigma2') y') t')); split_all. 
inv p_red1.  invsub. 
exist(App (App (App (Op Abs) 
               (App (App (App (App (Op Add) N'13) N'12) N'11) N'7)) N'6) N').
split_all. auto 20.  
(* 17 *)
elim(IHOR1 (App (App (App (Op Abs) sigma') x') t')); split_all.
elim(IHOR2 u'); split_all.
inv p_red1.  invsub. 
exist(App (App (App (App (Op Add) N'5) N'4) x1) N'3). 
split_all.
(* 16 *) 
inv p_red1; invsub.
elim(IHOR1 N'2); elim(IHOR2 N'1); elim(IHOR3 N'0); split_all.
exist(App (App x1 x) (App x0 x)). 
(* 17 *)
elim(IHOR1 M'0); elim(IHOR2 N'0); elim(IHOR3 P'0); split_all.
exist(App (App x1 x) (App x0 x)). 
(* 15 *)
inversion H; subst. clear H. 
inv p_red1; invsub.
elim(IHOR N'0); split_all.
exist x. 
elim(IHOR P); split_all.
(* 14 *)
inversion H; subst. inversion H2.  subst. 
elim(IHOR N'); split_all.
exist x. 
elim(IHOR P); split_all.
(* 13 *)
inversion H; subst.  inversion H2; inversion H4; subst. inversion H3; inversion H6; subst.
eauto. eauto. assert False by eapply2 H4. noway. inversion H3. inversion H0.
inversion H2. inversion H0.
(* 12 *)
inversion H1; subst.  clear H1. inv p_red1.  
exist (App k_op i_op); split_all. eapply2 e_op_factorable_p_red.
inversion H; split_all; subst. inversion H6; eauto. right; eapply2 preserves_compound_p_red1.
inversion H; split_all; subst. inversion H6; eauto.
assert(compound N') by eapply2 preserves_compound_p_red1.
intro; subst. inversion H2. inversion H3.  
assert False by eapply2 H0. noway. eauto. eauto. inversion H4. inversion H2.
(* 11 *)
inversion H0; subst. inversion H3; inversion H5; subst. inversion H4; subst.
exist(App k_op i_op). split_all. eapply2 e_compound_op_p_red. 
eapply2 preserves_compound_p_red1.
inversion H. inversion H1. 
inversion H. inversion H1. 
eauto. 
inversion H4. inversion H1.
(* 11 *)
inversion H1; subst.
inversion H4; subst.
inversion H5; subst. 
elim(IHOR1 N'1); elim(IHOR2 N'0); split_all. 
exist(App
          (App (App (App (Op Eop) (left_component x0)) (left_component x))
             (App (App (Op Eop) (right_component x0)) (right_component x)))
          (App k_op i_op)) . split_all. 
apply app_p_red. apply app_p_red. apply app_p_red. apply app_p_red. auto. 
eapply2 preserves_compound_p_red1. (eapply2 (preserves_compound_p_red1 M)).
eapply2 preserves_compound_p_red1. eapply2 preserves_compound_p_red1.
apply app_p_red. apply app_p_red. auto. 
eapply2 preserves_compound_p_red1. (eapply2 (preserves_compound_p_red1 M)).
eapply2 preserves_compound_p_red1. eapply2 preserves_compound_p_red1.
auto.
eapply e_compounds_p_red. (eapply2 (preserves_compound_p_red1 M)).
 (eapply2 (preserves_compound_p_red1 N)). auto.  auto. 
 inversion H0. inversion H2. 
 inversion H. inversion H2. 
 inversion H0. inversion H2. 
 (* 10 *)
 elim(IHOR1 M'0); elim(IHOR2 N'0); split_all. 
exist(App
          (App (App (App (Op Eop) (left_component x0)) (left_component x))
             (App (App (Op Eop) (right_component x0)) (right_component x)))
          (App k_op i_op)) . split_all. 
apply app_p_red. apply app_p_red. apply app_p_red. apply app_p_red. auto. 
eapply2 preserves_compound_p_red1. (eapply2 (preserves_compound_p_red1 M)).
eapply2 preserves_compound_p_red1. eapply2 preserves_compound_p_red1.
apply app_p_red. apply app_p_red. auto. 
eapply2 preserves_compound_p_red1. (eapply2 (preserves_compound_p_red1 M)).
eapply2 preserves_compound_p_red1. eapply2 preserves_compound_p_red1.
auto.
apply app_p_red. apply app_p_red. apply app_p_red. apply app_p_red. auto. 
eapply2 preserves_compound_p_red1. (eapply2 (preserves_compound_p_red1 M)).
eapply2 preserves_compound_p_red1. eapply2 preserves_compound_p_red1.
apply app_p_red. apply app_p_red. auto. 
eapply2 preserves_compound_p_red1. (eapply2 (preserves_compound_p_red1 M)).
eapply2 preserves_compound_p_red1. eapply2 preserves_compound_p_red1.
auto.
(* 9 *)
inversion H; subst. clear H; inv p_red1. 
elim(IHOR1 N'2); elim(IHOR2 N'1); elim(IHOR3 N'0); split_all.
exist(App (App (Op Tag) (App (App (Op Tag) x1) x0)) x). split_all. 
elim(IHOR1 M'0); elim(IHOR2 N'0); elim(IHOR3 P'0); split_all.
exist(App (App (Op Tag) (App (App (Op Tag) x1) x0)) x). split_all. 
(* 8 *)
inversion H; subst. clear H; inv p_red1. 
elim(IHOR1 N'1); elim(IHOR2 N'0); split_all.
exist(App (App (Op Tag) (App (Op Var) x0)) x). split_all. 
elim(IHOR1 M'0); elim(IHOR2 N'0); split_all.
exist(App (App (Op Tag) (App (Op Var) x0)) x). split_all. 
(* 7 *)
inversion H; subst. clear H; inv p_red1. 
elim(IHOR N'2); split_all. eauto.
elim(IHOR sigma'0); split_all. eauto.
inversion H4.
(* 6 *)
inversion H0; subst; clear H0; inv p_red1; try (inversion H; fail). 
(* 7 *)
elim(IHOR1 N'1); elim(IHOR2 N'0); elim(IHOR3 N'2); elim(IHOR4 N'); split_all.
exist(App (App (App (App (App (Op Add) x1) x3) x2) (left_component x0))
          (App (App (App (App (Op Add) x1) x3) x2) (right_component x0))).
split_all. apply app_p_red. apply app_p_red. auto. 
eapply2 preserves_compound_p_red1. (eapply2 (preserves_compound_p_red1 M)).
apply app_p_red. auto. 
eapply2 preserves_compound_p_red1. (eapply2 (preserves_compound_p_red1 M)).
eapply add_true_compound_p_red. 
eapply2 preserves_true_compound_p_red1. auto. auto. auto. auto.
(* 6 *) 
elim(IHOR1 x'0); elim(IHOR2 u'0); elim(IHOR3 sigma'0); elim(IHOR4 M'0); split_all.
exist(App (App (App (App (App (Op Add) x1) x3) x2) (left_component x0))
          (App (App (App (App (Op Add) x1) x3) x2) (right_component x0))).
split_all. 
apply app_p_red. apply app_p_red. auto. 
eapply2 preserves_compound_p_red1. (eapply2 (preserves_compound_p_red1 M)).
apply app_p_red. auto. 
eapply2 preserves_compound_p_red1. (eapply2 (preserves_compound_p_red1 M)).
apply app_p_red. apply app_p_red. auto. 
eapply2 preserves_compound_p_red1. (eapply2 (preserves_compound_p_red1 M)).
apply app_p_red. auto. 
eapply2 preserves_compound_p_red1. (eapply2 (preserves_compound_p_red1 M)).
(* 5 *)
inversion H; subst; clear H; inv p_red1. 
elim(IHOR1 N'4); elim(IHOR2 N'3); elim(IHOR3 N'5); elim(IHOR4 N'2); elim(IHOR5 N'1); split_all.
exist(App (App (App (App (App (Op Add) x2) x4) x3) x1)
          (App (App (App (App (Op Add) x2) x4) x3) x0)). 
split_all. auto 20.
inversion H4. 

elim(IHOR1 x'0); elim(IHOR2 u'0); elim(IHOR3 sigma'0); elim(IHOR4 M'0); elim(IHOR5 N'0); split_all.
exist(App (App (App (App (App (Op Add) x2) x4) x3) x1)
          (App (App (App (App (Op Add) x2) x4) x3) x0)).
auto 20. 
(* 4 *)
inversion H; subst; clear H; inv p_red1; invsub; try (inversion H4; fail).  
elim(IHOR1 N'2); elim(IHOR2 N'1); elim(IHOR3 N'3); elim(IHOR4 N'0); split_all.
exist(App (App (App (App (Op Eop) x3) x0) x2)  (App x1 (App (Op Var) x0))). split_all. 
elim(IHOR1 x'0); elim(IHOR2 u'0); elim(IHOR3 sigma'0); elim(IHOR4 M'0); split_all.
exist(App (App (App (App (Op Eop) x3) x0) x2)  (App x1 (App (Op Var) x0))). split_all. 
(* 3 *)
inversion H; subst; clear H; inv p_red1; try (inversion H4; fail).
elim(IHOR1 N'4); elim(IHOR2 N'3); elim(IHOR3 N'5); elim(IHOR4 N'1); elim(IHOR5 N'0); elim(IHOR6 N'2);
split_all.
exist(App
          (App (App (Op Add) (App (App (App (App (Op Add) x3) x5) x4) x0)) x2)
             (App (App (App (App (Op Add) x3) x5) x4) x1))
          . 
split_all; auto 20. 
(* 3 *)
elim(IHOR1 x'0); elim(IHOR2 u'0); elim(IHOR3 sigma'0); elim(IHOR4 y'0); elim(IHOR5 v'0); elim(IHOR6 sigma2'0); 
split_all.
exist(App
          (App (App (Op Add) (App (App (App (App (Op Add) x3) x5) x4) x0)) x2)
             (App (App (App (App (Op Add) x3) x5) x4) x1))
          . 
split_all; auto 20. 
(* 2 *) 
inversion H; subst; clear H; inv p_red1; try (inversion H4; fail).
elim(IHOR1 N'4); elim(IHOR2 N'3); elim(IHOR3 N'5); elim(IHOR4 N'1); elim(IHOR5 N'2); elim(IHOR6 N'0);
split_all. 
exist(App
          (App (App (Op Abs) (App (App (App (App (Op Add) x3) x5) x4) x1)) x2) x0). 
split_all; auto 20.
elim(IHOR1 x'0); elim(IHOR2 u'0); elim(IHOR3 sigma'0); 
elim(IHOR4 y'0); elim(IHOR5 sigma2'0); elim(IHOR6 t'0); split_all.
exist(App
          (App (App (Op Abs) (App (App (App (App (Op Add) x3) x5) x4) x1)) x2) x0). 
split_all; auto 20.
(* 1 *)
inversion H; subst; clear H; inv p_red1; try (inversion H4; fail).
elim(IHOR1 N'1); elim(IHOR2 N'2); elim(IHOR3 N'0); elim(IHOR4 N');
split_all.
exist(App (App (App (App (Op Add) x2) x3) x0) x1); split_all. 
elim(IHOR1 x'0); elim(IHOR2 sigma'0); elim(IHOR3 t'0); elim(IHOR4 u'0);
split_all.
exist(App (App (App (App (Op Add) x2) x3) x0) x1); split_all. 
Qed. 


Hint Resolve diamond_p_red1_p_red1.

Lemma diamond_p_red1_p_red : diamond p_red1 p_red.
Proof. eapply2 diamond_strip. Qed. 

Lemma diamond_p_red : diamond p_red p_red.
Proof.  eapply2 diamond_tiling. Qed. 
Hint Resolve diamond_p_red.



Lemma c_red1_to_p_red1 : implies_red c_red1 p_red1. 
Proof. 
red. intros M N B; induction B; split_all; 
try (red; seq_r; red; one_step; fail);
try (red; seq_l; red; seq_l; red; one_step; fail);
try (red; seq_l; red; seq_r; red; one_step; fail).
Qed. 


Lemma c_red_to_p_red: implies_red c_red p_red. 
Proof. 
eapply2 implies_red_multi_step. 
red; split_all; one_step; eapply2 c_red1_to_p_red1. 
Qed. 

Lemma to_c_red_multi_step: forall red, implies_red red c_red -> implies_red (multi_step red) c_red. 
Proof. 
red.  intros red B M N R; induction R; split_all.
red; split_all. 
assert(c_red M N) by eapply2 B. 
apply transitive_red with N; auto. 
eapply2 IHR. 
Qed. 


Lemma p_red1_to_c_red: implies_red p_red1 c_red .
Proof. 
  red.  intros M N OR; induction OR; split_all;
        try (eapply2 succ_red; eapply2 preserves_app_c_red); auto 10; 
        repeat eapply2 preserves_app_c_red;
        repeat eapply2 preserves_compound_l_c_red;
        eapply2 preserves_compound_r_c_red.
Qed.


Hint Resolve p_red1_to_c_red.

Lemma p_red_to_c_red: implies_red p_red c_red. 
Proof. eapply2 to_c_red_multi_step. Qed.


Lemma diamond_c_red: diamond c_red c_red. 
Proof. 
red; split_all. 
assert(p_red M N) by eapply2 c_red_to_p_red.  
assert(p_red M P) by eapply2 c_red_to_p_red.  
elim(diamond_p_red M N H1 P); split_all. 
exist x; split_all; eapply2 p_red_to_c_red. 
Qed. 
Hint Resolve diamond_c_red. 


(* Confluence *)

Definition confluence (A : Set) (R : A -> A -> Prop) :=
  forall x y : A,
  R x y -> forall z : A, R x z -> exists u : A, R y u /\ R z u.

Theorem abstraction_confluence: confluence Term c_red. 
Proof. red; split_all; eapply2 diamond_c_red. Qed. 
