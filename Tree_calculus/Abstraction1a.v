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
(*                   Abstraction1a.v                                  *)
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
Require Import IntensionalLib.Tree_calculus.Extensions.  
Require Import IntensionalLib.Tree_calculus.Wait2.  
Require Import IntensionalLib.Tree_calculus.Abstraction.  


Lemma b_op_program: program b_op. 
Proof.
unfold program.
split. 
eapply2 nf_compound. eapply2 nf_compound. eapply2 nf_compound. unfold_op; repeat eapply2 nf_compound. 
unfold_op; eapply2 nf_compound.  eapply2 nf_compound.  eapply2 nf_compound.  eapply2 nf_compound. 
 eapply2 b_fn_normal.  eapply2 nf_compound. eapply2 Y_k_normal.  
eapply2 b_op_closed.
Qed. 
 
(* 

Lemma star_opt_bind_normal_mono: 
forall M N, bind_normal M -> bind_normal N -> star_opt M = star_opt N -> M = N. 
Proof. 
induction M; split_all. 

Qed.
*)

Lemma h_fn_size:   size h_fn = 50.
Proof. cbv. auto. Qed.


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
case (occurs0 M1).
unfold size; fold size. omega. 
gen_case IHM2 M2. 
(* 3 *) 
gen_case IHM2 n.
rewrite size_subst. omega.
all: replace (subst_rec M1 (Op Node) 0) with (subst M1 (Op Node)) by auto.  
all: try rewrite size_subst. omega. omega. 
(* 1 *) 
gen_case IHM2 (occurs0 t). omega. 
gen_case IHM2 (occurs0 t0). 
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

