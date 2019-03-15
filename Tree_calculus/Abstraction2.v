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
(*                   Abstraction2.v                                   *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)


Require Import Omega Max Bool List.
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
Require Import IntensionalLib.Tree_calculus.Case.  
Require Import IntensionalLib.Tree_calculus.Extensions.  
Require Import IntensionalLib.Tree_calculus.Wait2.  
Require Import IntensionalLib.Tree_calculus.Abstraction.  

Set
Keep Proof Equalities.



Lemma bind_normal_case : forall P M, bind_normal M -> bind_normal (case P M). 
Proof. 
induction P; intros; unfold case;  fold case.
eapply2 star_opt_preserves_bind_normal. 
unfold_op. eapply2 bind_normal_fork. 
eapply2 star_opt_preserves_bind_normal.
eapply2 bn_app. 
eapply2 bn_app. 
eapply2 bn_app. 
eapply2 bn_normal.  eapply2 Fop_normal. 
unfold_op. eapply2 bind_normal_fork.
unfold lift. 
eapply2 lift_rec_preserves_bind_normal. 
unfold maxvar; fold maxvar. rewrite Fop_closed. 
simpl. case (maxvar(lift 1 M)); intros; omega.
unfold swap; unfold_op; eapply2 bn_normal. repeat eapply2 nf_compound. 
rewrite ! maxvar_app. rewrite ! maxvar_ref. 
assert(Nat.max
  (Nat.max (Nat.max (maxvar Fop) 1)
     (Nat.max (maxvar k_op) (maxvar (lift 1 M))))
  (Nat.max (maxvar k_op) (Nat.max (maxvar k_op) (maxvar (swap (Ref 0))))) >= 
 (Nat.max (Nat.max (maxvar Fop) 1)
     (Nat.max (maxvar k_op) (maxvar (lift 1 M))))
) by eapply2 max_is_max. 
assert( (Nat.max (Nat.max (maxvar Fop) 1)
     (Nat.max (maxvar k_op) (maxvar (lift 1 M)))) >= (Nat.max (maxvar Fop) 1)) by eapply2 max_is_max. 
assert((Nat.max (maxvar Fop) 1) >= 1) by eapply2 max_is_max. omega. 
(* 1 *) 
assert(is_program (App P1 P2) = true \/  (is_program (App P1 P2) <> true)) by decide equality.
inversion H0. 
(* 2 *) 
rewrite H1.  
eapply2 star_opt_preserves_bind_normal. 
apply bn_app.
apply bn_app.  
apply bn_app.
apply bn_app.  
apply bn_normal. eapply2 equal_comb_normal. 
eapply2 bn_normal; auto.
rewrite maxvar_app.  rewrite equal_comb_closed. cbv; auto.
all: cycle 1. 
rewrite maxvar_app. rewrite maxvar_app.  rewrite equal_comb_closed.
unfold max; fold max. unfold maxvar at 1. 
assert(max 1 (maxvar (App P1 P2)) >= 1) by eapply2 max_is_max. omega. 
unfold_op. 
eapply2 bind_normal_fork. 
unfold lift. eapply2 lift_rec_preserves_bind_normal.
rewrite maxvar_app. rewrite maxvar_app.  rewrite maxvar_app.  rewrite equal_comb_closed.
unfold max; fold max. unfold maxvar at 1. 
assert(Nat.max (Nat.max 1 (maxvar (App P1 P2))) (maxvar (App k_op (lift 1 M))) >= 
(Nat.max 1 (maxvar (App P1 P2)))) by eapply2 max_is_max. 
assert((Nat.max 1 (maxvar (App P1 P2))) >= 1) by eapply2 max_is_max. 
omega.
eapply2 bn_normal; unfold swap; unfold_op; repeat eapply2 nf_compound. 
rewrite maxvar_app. rewrite maxvar_app.  rewrite maxvar_app.   rewrite maxvar_app.  rewrite equal_comb_closed.
unfold max; fold max. unfold maxvar at 1. 
assert(Nat.max
  (Nat.max (Nat.max 1 (maxvar (App P1 P2))) (maxvar (App k_op (lift 1 M))))
  (maxvar (swap (Ref 0))) >= (Nat.max (Nat.max 1 (maxvar (App P1 P2))) (maxvar (App k_op (lift 1 M)))))
by eapply2 max_is_max. 
assert(Nat.max (Nat.max 1 (maxvar (App P1 P2))) (maxvar (App k_op (lift 1 M))) >= 
(Nat.max 1 (maxvar (App P1 P2)))) by eapply2 max_is_max. 
assert((Nat.max 1 (maxvar (App P1 P2))) >= 1) by eapply2 max_is_max. 
omega.
(* 2 *) 
all: cycle 1. 
eapply2 bn_normal. 
assert(program (App P1 P2)) by eapply2 program_is_program. 
inversion H2; auto. 
(* 1 *) 
assert(is_program(App P1 P2) = false). 
gen_case H1 (is_program (App P1 P2)). congruence . 
rewrite H2. 
(* 1 *) 
unfold case_app. 
eapply2 star_opt_preserves_bind_normal.
eapply2 bn_app. all: cycle 1. 
unfold swap. eapply2 bn_normal. unfold_op; repeat eapply2 nf_compound. 
unfold swap; unfold_op; unfold maxvar; fold maxvar.
unfold max; fold max.  
match goal with 
| |- Nat.max ?m ?n >0 => assert(Nat.max m n >= n) by eapply2 max_is_max
end.  omega. 
(* 1 *) 
eapply2 bn_app. 
eapply2 bn_app. 
eapply2 bn_app. 
eapply2 bn_normal.  eapply2 Fop_normal. 
eapply2 bn_normal; unfold_op; repeat eapply2 nf_compound. 
all: cycle 1. 
unfold maxvar; fold maxvar. 
match goal with 
| |- Nat.max ?m ?n >0 => assert(Nat.max m n >= m) by eapply2 max_is_max
end.
assert(Nat.max (Nat.max (maxvar Fop) 1) (maxvar i_op) >= (Nat.max (maxvar Fop) 1)) by eapply2 max_is_max. 
assert(Nat.max (maxvar Fop) 1 >= 1) by eapply2 max_is_max. omega. 
(* 1 *) 
unfold lift; eapply2 lift_rec_preserves_bind_normal. 
repeat eapply2 star_opt_preserves_bind_normal. 
eapply2 bn_app.
2: unfold_op; eapply2 bn_normal; repeat eapply2 nf_compound. 
eapply2 bn_app.
all: cycle 1. 
unfold maxvar; fold maxvar. 
match goal with 
| |- Nat.max ?m 1 >0 => assert(Nat.max m 1 >= 1) by eapply2 max_is_max end. 
omega .
unfold maxvar; fold maxvar. 
match goal with 
| |- Nat.max ?m ?n >0 => assert(Nat.max m n >= m) by eapply2 max_is_max end. 
assert(Nat.max
       (Nat.max
          (Nat.max
             (maxvar
                (lift_rec (case P1 (case P2 (App k_op (App k_op M)))) 0 2)) 2)
          (Nat.max (maxvar k_op)
             (Nat.max (maxvar k_op) (Nat.max (maxvar k_op) (maxvar i_op)))))
       1 >= 1) by eapply2 max_is_max. 
omega. 
(* 1 *) 
eapply2 bn_app. 
all: cycle 1. 
unfold_op; eapply2 bn_normal; repeat eapply2 nf_compound.
unfold maxvar; fold maxvar.
match goal with 
| |- Nat.max ?m ?n >0 => assert(Nat.max m n >= m) by eapply2 max_is_max end. 
assert(Nat.max
       (maxvar (lift_rec (case P1 (case P2 (App k_op (App k_op M)))) 0 2)) 2 >= 2) 
by eapply2 max_is_max. 
omega.
(* 1 *) 
eapply2 bn_app. 
all: cycle 1. 
unfold maxvar; fold maxvar. 
match goal with 
| |- Nat.max ?m ?n >0 => assert(Nat.max m n >= n) by eapply2 max_is_max end. 
omega .
eapply2 lift_rec_preserves_bind_normal. 
eapply2 IHP1. eapply2 IHP2.
unfold_op. eapply2 bind_normal_fork. eapply2 bind_normal_fork. 
Qed. 

 Lemma bind_normal_extension: forall P M R, bind_normal M -> bind_normal R -> bind_normal (extension P M R).
Proof. 
intros. unfold extension. eapply2 bind_normal_fork . eapply2 bind_normal_stem.
unfold_op. eapply2 bind_normal_fork. eapply2 bind_normal_case. 
Qed. 
 



Lemma size_subst: forall M, size (subst M (Op Node)) = size M. 
Proof. 
induction M; split_all. 
unfold subst. simpl. case n; insert_Ref_out. cbv; auto. 
intros; insert_Ref_out.  case n0; auto.
Qed. 
  

Lemma star_opt_size: forall M, size (star_opt M) + 1>= size M. 
Proof.
induction M; split_all. 
case n; split_all.  omega. 
case (occurs 0 M1).
unfold size; fold size. omega. 
gen_case IHM2 M2. 
(* 3 *) 
gen_case IHM2 n.
rewrite size_subst. omega.
all: replace (subst_rec M1 (Op Node) 0) with (subst M1 (Op Node)) by auto.  
all: try rewrite size_subst. omega. omega. 
(* 1 *) 
gen_case IHM2 (occurs 0 t). omega. 
gen_case IHM2 (occurs 0 t0). 
gen_case IHM2 t0; try omega.   
(* 1 *) 
all: replace (subst_rec M1 (Op Node) 0) with (subst M1 (Op Node)) by auto.  
all: replace (subst_rec t (Op Node) 0) with (subst t (Op Node)) by auto.  
all: replace (subst_rec t0 (Op Node) 0) with (subst t0 (Op Node)) by auto.  
rewrite ! size_subst. omega.
Qed.


Lemma size_app: forall M N, size (App M N) = size M + size N. 
Proof. intros; auto. Qed. 

Lemma lift_rec_preserves_size: 
forall M n k, size (lift_rec M n k) = size M. 
Proof.
induction M; split_all.
Qed. 
 


Lemma extension_size : forall P M R, size (extension P M R) > size M + size R. 
Proof.
intros. unfold extension.  unfold_op; simpl. 
assert(size (case P M) >= size M). 
2: omega.
generalize M; clear.  
induction P; intros. 
(* 3 *) 
unfold case; fold case.
assert(size(star_opt (App k_op M)) + 1 >= size (App k_op M)) by eapply2 star_opt_size. 
generalize H; unfold_op; unfold size; fold size; intros. omega.
(* 2 *) 
unfold case; fold case.
assert(size
  (star_opt
     (App (App (App Fop (Ref 0)) (App k_op (lift 1 M)))
        (App k_op (App k_op (swap (Ref 0)))))) + 1 >= 
size(App (App (App Fop (Ref 0)) (App k_op (lift 1 M)))
        (App k_op (App k_op (swap (Ref 0)))))) by eapply2 star_opt_size.
generalize H; unfold swap; unfold_op. rewrite ! size_app in *.
replace (size(Op Node)) with 1 by auto.
unfold lift. rewrite lift_rec_preserves_size.
intro.  omega.
(* 1 *) 
unfold case; fold case.  
case (is_program (App P1 P2)). 
assert(size
  (star_opt
     (App
        (App (App (App equal_comb (Ref 0)) (App P1 P2)) (App k_op (lift 1 M)))
        (swap (Ref 0)))) +1 >= (size
  (
     (App
        (App (App (App equal_comb (Ref 0)) (App P1 P2)) (App k_op (lift 1 M)))
        (swap (Ref 0)))))) 
by eapply2 star_opt_size.
assert( (size
  (
     (App
        (App (App (App equal_comb (Ref 0)) (App P1 P2)) (App k_op (lift 1 M)))
        (swap (Ref 0))))) >= size M +1). 
2: omega.
clear. unfold size; fold size. unfold lift. 
rewrite lift_rec_preserves_size.  omega. 
(* 1 *) 
unfold case_app. 
match goal with 
| |- size (star_opt ?Q) >= _ => 
assert(size (star_opt Q) +1 >= size Q) by eapply2 star_opt_size
end. 
assert(size
      (App
         (App (App (App Fop (Ref 0)) i_op)
            (lift 1
               (star_opt
                  (star_opt
                     (App
                        (App
                           (App
                              (App
                                 (lift 2
                                    (case P1
                                       (case P2 (App k_op (App k_op M)))))
                                 (Ref 1))
                              (App k_op (App k_op (App k_op i_op)))) 
                           (Ref 0)) (App k_op i_op)))))) (swap (Ref 0)))
>= size M + 1).
2: omega. 
clear H. 
rewrite ! size_app.
unfold_op. 
unfold size at 2 3. 
assert(size
  (lift 1
     (star_opt
        (star_opt
           (App
              (App
                 (App
                    (App
                       (lift 2
                          (case P1
                             (case P2
                                (App (App (Op Node) (Op Node))
                                   (App (App (Op Node) (Op Node)) M)))))
                       (Ref 1))
                    (App (App (Op Node) (Op Node))
                       (App (App (Op Node) (Op Node))
                          (App (App (Op Node) (Op Node))
                             (App (App (Op Node) (App (Op Node) (Op Node)))
                                (App (Op Node) (Op Node))))))) (Ref 0))
              (App (App (Op Node) (Op Node))
                 (App (App (Op Node) (App (Op Node) (Op Node)))
                    (App (Op Node) (Op Node))))))))
+ 2  >= size M). 
2: omega. 
unfold lift; rewrite lift_rec_preserves_size.
assert(size
  (star_opt
     (star_opt
        (App
           (App
              (App
                 (App
                    (lift_rec (case P1 (case P2 (App k_op (App k_op M)))) 0 2)
                    (Ref 1)) (App k_op (App k_op (App k_op i_op)))) (Ref 0))
           (App k_op i_op))))  + 1
>= 
size
     (star_opt
        (App
           (App
              (App
                 (App
                    (lift_rec (case P1 (case P2 (App k_op (App k_op M)))) 0 2)
                    (Ref 1)) (App k_op (App k_op (App k_op i_op)))) (Ref 0))
           (App k_op i_op)))).
eapply2 star_opt_size. 
assert(
size
     (star_opt
        (App
           (App
              (App
                 (App
                    (lift_rec (case P1 (case P2 (App k_op (App k_op M)))) 0 2)
                    (Ref 1)) (App k_op (App k_op (App k_op i_op)))) (Ref 0))
           (App k_op i_op))) +1 >=
size((App
           (App
              (App
                 (App
                    (lift_rec (case P1 (case P2 (App k_op (App k_op M)))) 0 2)
                    (Ref 1)) (App k_op (App k_op (App k_op i_op)))) (Ref 0))
           (App k_op i_op))))
by eapply2 star_opt_size. 
assert(size
       (App
          (App
             (App
                (App
                   (lift_rec (case P1 (case P2 (App k_op (App k_op M)))) 0 2)
                   (Ref 1)) (App k_op (App k_op (App k_op i_op)))) (Ref 0))
          (App k_op i_op))
>= size M). 
all: cycle 1.
assert(forall m n p q, m+1 >= n -> n+1 >= p -> p>= q -> m+2 >= q).
intros; omega. 
eapply2 H2. 
(* 1 *) 
clear H H0. 
rewrite ! size_app. 
rewrite lift_rec_preserves_size. 
assert(size (case P1 (case P2 (App k_op (App k_op M)))) >= size M).
2: omega.
assert(size (case P1 (case P2 (App k_op (App k_op M)))) >= size (case P2 (App k_op (App k_op M)))) by eapply2 IHP1. 
assert(size (case P2 (App k_op (App k_op M))) >= size((App k_op (App k_op M)))) by eapply2 IHP2.
assert(size  (App k_op (App k_op M)) > size M).
2: omega. 
unfold_op; simpl; omega. 
Qed. 


Lemma h_fn_size:   size h_fn = 50.
Proof. cbv. auto. Qed.


Lemma b_fn_size : size b_fn >50 . 
Proof.
unfold b_fn.
assert(forall M, size M + 1  >= 52 -> size M > 50). 
split_all; omega. 
apply H. clear H. 
eapply le_trans.
2: eapply2 star_opt_size.
assert(forall M, 53 <= size M + 1 -> 52 <= size M) by (split_all; omega).
apply H; clear H.  
eapply le_trans.
2: eapply2 star_opt_size.
assert(forall M, 54 <= size M + 1 -> 53 <= size M) by (split_all; omega).
apply H; clear H.  
eapply le_trans.
2: eapply2 star_opt_size.
eapply le_trans.
2: eapply2 extension_size.
rewrite ! size_app. unfold size; fold size. unfold plus; fold plus. 
assert(forall m, 45 <= m -> 54 <= S(S(S(S(S(S(S(S(S m))))))))) by (intros; omega).
apply H; clear H. 
eapply le_trans. 
2: eapply2 extension_size.
rewrite ! size_app. unfold size; fold size. unfold plus; fold plus. 
assert(forall m, 45 <= m -> 54 <= S(S(S(S(S(S(S(S(S m))))))))) by (intros; omega).
assert(45 <= (size
     (app_comb (app_comb (app_comb (A_k 5) (omega_k 4)) (omega_k 4)) (Ref 0)))). 
2: omega.
unfold app_comb. rewrite ! size_app.
replace (size (Op Node)) with 1 by auto. 
unfold_op. unfold size at 1 2 3 4 5.  unfold size at 1 3 4 5 7.
assert(size (A_k 5) >= 5). 
2: omega.
unfold A_k.

assert(forall M, size (star M) >= size M + 1). 
induction M; split_all.
case n; split_all. 
omega. 
eapply le_trans. 2: eapply2 H0. 
assert(4 <= size
  (star
     (app_comb
        (star
           (star
              (app_comb
                 (star (star (app_comb a_op (app_comb (Ref 1) (Ref 0)))))
                 (app_comb (Ref 1) (Ref 0))))) (app_comb (Ref 1) (Ref 0))))). 
2: omega. 
eapply le_trans. 2: eapply2 H0. 
unfold app_comb. 
rewrite ! size_app.
replace (size (Op Node)) with 1 by auto. 
omega.
Qed. 
 
 

Lemma b_not_h: b_fn <> h_fn.
Proof. 
intro. 
assert(size b_fn = size h_fn) by congruence.
rewrite h_fn_size in *.
assert(size b_fn > 50) by eapply2 b_fn_size. 
omega.
Qed. 

 
Lemma b_fn_body_maxvar : 
maxvar
  (extension
        (app_comb
           (app_comb (app_comb (app_comb (omega_k 4) (omega_k 4)) h_fn)
              (Ref 0)) (Ref 1))
        (App (App (App (App (Ref 4) (Ref 3)) (Ref 2)) (Ref 0))
           (App (App (App (Ref 4) (Ref 3)) (Ref 2)) (Ref 1)))
        (extension
           (app_comb
              (app_comb (app_comb (app_comb (omega_k 4) (omega_k 4)) (Ref 0))
                 (Ref 1)) (Ref 2))
           (App
              (App
                 (app_comb
                    (app_comb (app_comb (A_k 5) (omega_k 4)) (omega_k 4))
                    (Ref 0))
                 (App (App (App (Ref 5) (Ref 4)) (Ref 3)) (Ref 1)))
              (App (App (App (Ref 5) (Ref 4)) (Ref 3)) (Ref 2)))
           (extension
              (app_comb (app_comb (app_comb (omega_k 3) (omega_k 3)) (Ref 0))
                 (Ref 1)) (App (Ref 2) (Ref 1))
              (extension (app_comb (Y_k 2) (Ref 0)) (Ref 2)
                 (extension
                    (app_comb (app_comb (Ref 0) (app_comb (A_k 3) (Ref 1)))
                       (Ref 2))
                    (App
                       (App (app_comb (A_k 3) (Ref 1))
                          (App (App (App (Ref 5) (Ref 4)) (Ref 3)) (Ref 0)))
                       (Ref 2)) i_op)))))
 = 3.
Proof. 
rewrite maxvar_extension.
rewrite ! maxvar_app. 
rewrite ! pattern_size_app_comb. 
rewrite ! pattern_size_ref.
rewrite ! pattern_size_closed. 
2: eapply2 omega_k_closed.
2: cbv; auto. 
rewrite ! maxvar_ref. 
unfold plus, minus,  max; fold max.
rewrite maxvar_extension.
rewrite ! maxvar_app. 
rewrite ! maxvar_app_comb.
rewrite A_k_closed. 
rewrite omega_k_closed.
rewrite ! maxvar_ref. 
rewrite ! pattern_size_app_comb. 
rewrite ! pattern_size_ref.
rewrite ! pattern_size_closed. 
2: eapply2 omega_k_closed. 
unfold plus, minus,  max; fold max.
(* 1 *)  
rewrite maxvar_extension.
rewrite ! maxvar_app. 
rewrite ! pattern_size_app_comb. 
rewrite ! pattern_size_ref.
rewrite ! pattern_size_closed. 
2: eapply2 omega_k_closed.
rewrite ! maxvar_ref. 
unfold plus, minus,  max; fold max.
rewrite maxvar_extension.
rewrite ! maxvar_ref. 
rewrite ! pattern_size_app_comb. 
rewrite ! pattern_size_ref.
rewrite ! pattern_size_closed. 
2: eapply2 Y_k_closed.
(* 1 *)  
rewrite maxvar_extension.
rewrite ! maxvar_app. 
rewrite ! pattern_size_app_comb. 
rewrite ! pattern_size_ref.
rewrite ! maxvar_app_comb.
rewrite ! maxvar_ref.
rewrite A_k_closed.  
unfold_op; unfold maxvar, plus, minus,  max; fold max. auto. 
Qed. 

Lemma aux7: 
bind_normal
  (extension
     (app_comb (app_comb (app_comb (omega_k 3) (omega_k 3)) (Ref 0)) (Ref 1))
     (App (Ref 2) (Ref 1))
     (extension (app_comb (Y_k 2) (Ref 0)) (Ref 2)
        (extension
           (app_comb (app_comb (Ref 0) (app_comb (A_k 3) (Ref 1))) (Ref 2))
           (App
              (App (app_comb (A_k 3) (Ref 1))
                 (App (App (App (Ref 5) (Ref 4)) (Ref 3)) (Ref 0))) (Ref 2))
           i_op))).
Proof. 
eapply bind_normal_extension.
eapply2 bn_normal. 
eapply bind_normal_extension.
auto. 
eapply bind_normal_extension.
2: unfold_op; eapply2 bn_normal.  
apply bn_app.
apply bn_app.
eapply2 bn_normal. 
eapply2 app_comb_normal.
eapply2 bn_normal. 
rewrite maxvar_app. rewrite maxvar_app_comb. 
rewrite A_k_closed. cbv; omega. auto.  
rewrite 2 maxvar_app. rewrite maxvar_app_comb. 
rewrite A_k_closed. cbv; omega.
Qed. 


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
              (extension
                 (app_comb (app_comb (Ref 0) (app_comb (A_k 3) (Ref 1)))
                    (Ref 2))
                 (App
                    (App (app_comb (A_k 3) (Ref 1))
                       (App (App (App (Ref 5) (Ref 4)) (Ref 3)) (Ref 0)))
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



