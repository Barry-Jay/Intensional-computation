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
(*                    Extensions.v                                    *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)


Require Import Omega Max Bool List.
Require Import IntensionalLib.SF_calculus.Test.  
Require Import IntensionalLib.SF_calculus.General.  
Require Import IntensionalLib.SF_calculus.SF_Terms.  
Require Import IntensionalLib.SF_calculus.SF_Tactics.  
Require Import IntensionalLib.SF_calculus.SF_reduction.  
Require Import IntensionalLib.SF_calculus.SF_Normal.  
Require Import IntensionalLib.SF_calculus.SF_Closed.  
Require Import IntensionalLib.SF_calculus.Substitution.  
Require Import IntensionalLib.SF_calculus.SF_Eval.  
Require Import IntensionalLib.SF_calculus.Star.  
Require Import IntensionalLib.SF_calculus.Fixpoints.  
Require Import IntensionalLib.SF_calculus.Equal.  

Lemma aux1: forall p q, S(S(S(S(S p)))) <= q ->
                        pred (pred (pred (q - S p))) = q - S (S (S (S p))). 
  intros.
  replace (pred (q - S p)) with (q - (S (S p)))  by omega.
  replace (pred (q - S(S p))) with (q - (S (S (S p))))  by omega.
omega.
Qed.

Lemma aux3 : forall M, pred (max match maxvar (lift 1 M) with
             | 0 => 1
             | S m' => S m'
             end 1) = maxvar M - 0. 
Proof.
intros. rewrite max_pred. simpl. rewrite max_zero. 
  replace (maxvar M - 0) with (maxvar M) by omega.
assert(maxvar M = 0 \/ maxvar M <> 0) by decide equality. 
inversion H. unfold lift; rewrite lift_rec_closed. rewrite H0; auto. auto. 
clear H. 
assert(maxvar (lift 1 M) = S(maxvar M)). 
induction M; split_all. gen_case H0 n. 
simpl in *. noway.  
simpl in *. 
assert (maxvar M1 = 0 -> maxvar (lift_rec M1 0 1) = 0) by (split_all; rewrite lift_rec_closed; auto).

gen3_case H0 H IHM1  (maxvar M1) . rewrite H; auto. 
unfold lift in *; rewrite IHM1; auto. 
assert (maxvar M2 = 0 -> maxvar (lift_rec M2 0 1) = 0) by (split_all; rewrite lift_rec_closed; auto).
gen3_case H0 H1 IHM2  (maxvar M2) . rewrite H1; auto. 
rewrite IHM2; auto. 
rewrite H. auto. 
Qed. 

Lemma max_aux: forall m n, max m n = m \/ max m n = n . 
Proof. 
induction m; split_all. induction n; split_all. 
assert(max m n = m \/ max m n = n) by eapply2 IHm. 
inversion H; rewrite H0; auto. 
Qed. 

Lemma maxvar_lift_rec_compare: 
forall M p  n k, p>= maxvar M  -> p+k >= maxvar (lift_rec M n k).
Proof.
induction M; split_all. 
unfold relocate. elim(test n0 n); split_all.  omega. omega. omega. 
elim(max_is_max (maxvar M1) (maxvar M2)). intros. 
eapply2 max_max2. 
eapply2 IHM1. omega. 
eapply2 IHM2. omega. 
Qed. 


Lemma lift_rec_misses: 
forall M n k, n >= maxvar M  -> lift_rec M n k = M. 
Proof.
induction M; split_all. relocate_lt. auto. 
assert(max (maxvar M1) (maxvar M2) >= maxvar M1 /\ max (maxvar M1) (maxvar M2) >= maxvar M2)
by eapply2 max_is_max. split_all. 
rewrite IHM1; try omega. rewrite IHM2; auto; omega. 
Qed.
 
Lemma maxvar_lift_rec_compare2: 
forall M N n k, maxvar M >= maxvar N -> maxvar (lift_rec M n k) >= maxvar (lift_rec N n k). 
Proof.
induction M; split_all. 
gen_case H N.
(* 5 *)  
unfold relocate. elim(test n0 n); split_all. elim(test n0 n1); split_all; try noway. 
omega. omega. elim(test n0 n1); split_all; try noway. 
(* 4 *) 
omega. 
(* 3 *) 
unfold relocate. elim(test n0 n); split_all. 
assert(max (maxvar s) (maxvar s0) >= maxvar s /\ max (maxvar s) (maxvar s0) >= maxvar s0) by eapply2 max_is_max. 
split_all. 
replace (S(k+n)) with (S n + k) by omega. 
eapply2 max_max2; eapply2 maxvar_lift_rec_compare; omega. 
assert(max (maxvar s) (maxvar s0) >= maxvar s /\ max (maxvar s) (maxvar s0) >= maxvar s0) by eapply2 max_is_max. 
split_all. 
rewrite ! lift_rec_misses; try omega. 
(* 2 *) 
rewrite lift_rec_closed; auto. omega. 
(* 1 *) 
assert(max (maxvar M1) (maxvar M2)  = maxvar M1 \/ 
max (maxvar M1) (maxvar M2) = maxvar M2) by eapply2 max_aux. 
assert(max (maxvar (lift_rec M1 n k)) (maxvar (lift_rec M2 n k)) >=(maxvar (lift_rec M1 n k)) /\ 
max (maxvar (lift_rec M1 n k)) (maxvar (lift_rec M2 n k)) >=(maxvar (lift_rec M2 n k)))
by eapply2 max_is_max. 
split_all. inversion H0. 
assert(maxvar (lift_rec M1 n k) >= maxvar (lift_rec N n k)). eapply2 IHM1; omega.  omega. 
assert(maxvar (lift_rec M2 n k) >= maxvar (lift_rec N n k)). eapply2 IHM2; omega.  omega. 
Qed. 

Lemma aux4 : forall M p,
     match
       pred
         (pred
            (maxvar (lift_rec M p 3) - p))
     with
     | 0 => 0
     | S m' => m'
     end = maxvar M - p
.
Proof.
induction M; split_all.
(* 2 *) 
 case p; split_all. relocate_lt. 
simpl. auto. 
unfold relocate. 
elim(test (S n0) n); split_all. 
(* 3 *) 
gen_case a n0. omega. 
gen_case a n1. gen_case a n. omega. 
gen_case a n2. gen_case a n. gen_case a n3. omega. 
unfold minus at 2; fold minus. 
assert(forall m n, m - (S n) = pred (m-n)) by (intros; omega). 
rewrite ! H. unfold pred at 3;  auto.
case (pred(pred (n-n3))); auto.  
(* 2 *) 
assert(pred(pred(n-n0)) = 0) by omega. 
rewrite H. omega. 
(* 1 *) 
assert(max (maxvar M1) (maxvar M2) = maxvar M1 \/ max (maxvar M1) (maxvar M2) = maxvar M2) by 
eapply2 max_aux. 
inversion H.  rewrite H0. 
assert( maxvar(lift_rec M1 p 3) >= max (maxvar (lift_rec M1 p 3)) (maxvar (lift_rec M2 p 3))).
eapply2 max_max2. eapply2 maxvar_lift_rec_compare2. 
assert(max (maxvar M1) (maxvar M2) >= maxvar M2) by eapply2 max_is_max. 
rewrite H0 in H1. auto. 
assert(max (maxvar (lift_rec M1 p 3)) (maxvar (lift_rec M2 p 3))>= maxvar(lift_rec M1 p 3))
by eapply2 max_is_max. 
assert(max (maxvar (lift_rec M1 p 3)) (maxvar (lift_rec M2 p 3)) = maxvar(lift_rec M1 p 3))
by omega. 
rewrite H3. eapply2 IHM1. 
(* 1 *) 
assert( maxvar(lift_rec M2 p 3) >= max (maxvar (lift_rec M1 p 3)) (maxvar (lift_rec M2 p 3))).
eapply2 max_max2. eapply2 maxvar_lift_rec_compare2. 
assert(max (maxvar M1) (maxvar M2) >= maxvar M1) by eapply2 max_is_max. 
rewrite H0 in H1. auto. 
assert(max (maxvar (lift_rec M1 p 3)) (maxvar (lift_rec M2 p 3))>= maxvar(lift_rec M2 p 3))
by eapply2 max_is_max. 
assert(max (maxvar (lift_rec M1 p 3)) (maxvar (lift_rec M2 p 3)) = maxvar(lift_rec M2 p 3))
by omega. 
rewrite H3. rewrite H0. eapply2 IHM2. 
Qed. 



Definition swap M := App (App (Op Sop) i_op ) (App k_op M).

Lemma swap_check : forall M N, sf_red (App (swap M) N) (App N M). 
Proof. 
unfold swap; split_all; eval_tac. eapply2 preserves_app_sf_red;  eval_tac.  eval_tac. 
Qed. 

Lemma star_opt_swap : 
star_opt (swap (Ref 0)) = App (App (Op Sop) (App k_op  (App (Op Sop) i_op ))) k_op .
Proof. split_all. Qed. 


Definition case_app case (P1 P2 M : SF) := 
(star_opt (App (App (App (App (Op Fop) (Ref 0)) i_op) 
                               (lift 1 (star_opt (star_opt (App (App (App (App 
                               (lift 2 (case P1 (case P2 (App k_op (App k_op M)))))
                               (Ref 1)) 
                                                       (App k_op (App k_op (App k_op i_op))))
                                                  (Ref 0))
                                             (App k_op i_op)))))) 
               (swap (Ref 0)))).

Ltac occurs_true_tac M := 
rewrite (star_opt_occurs_true M) at 1;
[| rewrite ! occurs_app; replace (occurs0 (Ref 0)) with true by split_all; 
rewrite ? orb_true_r; auto | discriminate]. 

Ltac occurs_false_tac M := 
rewrite (star_opt_occurs_false M) at 1; [| split_all]. 


Definition case_app_nf case (P1 P2 M: SF) := 
(App
        (App (Op Sop)
           (App
              (App (Op Sop)
                 (App (App (Op Sop) (Op Fop)) (App k_op  i_op )))
              (App k_op 
                 (App
                    (App (Op Sop)
                       (App (App (Op Sop) (App k_op  (Op Sop)))
                          (App
                             (App (Op Sop)
                                (case P1
                                   (case P2 (App k_op  (App k_op  M)))))
                             (App k_op 
                                (App k_op 
                                   (App k_op  (App k_op  i_op )))))))
                    (App k_op  (App k_op  (App k_op  i_op )))))))
        (App (App (Op Sop) (App k_op  (App (Op Sop) i_op ))) k_op )). 

(* 
Lemma case_app_val : 
forall case P1 P2 M, sf_red (case_app case P1 P2 M) (case_app_nf case P1 P2 M).
Proof. 
  intros; unfold case_app.
  rewrite star_opt_occurs_true; auto.  2: unfold swap; congruence. 
  rewrite star_opt_occurs_true; auto.
  2: case ((star_opt
      (star_opt
         (App
            (App
               (App (App (lift 2 (case P1 (case P2 (App k_op (App k_op M))))) (Ref 1))
                    (App k_op (App k_op (App k_op i_op)))) (Ref 0)) (App k_op i_op))))); intros;
    unfold lift; simpl; try congruence; case n; unfold relocate; simpl; congruence.
  eapply2 preserves_app_sf_red. 
  eapply2 preserves_app_sf_red. 
  eapply2 preserves_app_sf_red. 
  rewrite star_opt_lift.
  eapply2 preserves_app_sf_red. 
  rewrite (star_opt_occurs_true); auto. 2: simpl; rewrite ! orb_true_r; auto. 2: discriminate.
  rewrite star_opt_eta. 2: simpl; unfold lift; rewrite occurs_lift_rec_zero; auto.
  unfold subst, lift, subst_rec; fold subst_rec. rewrite subst_rec_lift_rec; try omega.  
  rewrite (star_opt_occurs_true); auto. 3: cbv; congruence.
  2: simpl; rewrite ! orb_true_r; auto. 
  eapply2 preserves_app_sf_red. 
  eapply2 preserves_app_sf_red.
  rewrite star_opt_closed. 
  2: simpl. 
  
unfold_op; simpl.   eapply2 preserves_app_sf_red. 
  rewrite star_opt_lift.
  eapply2 preserves_app_sf_red. 
  rewrite (star_opt_occurs_true); auto. 2: simpl; rewrite ! orb_true_r; auto. 2: discriminate.
  rewrite star_opt_eta. 2: simpl; unfold lift; rewrite occurs_lift_rec_zero; auto.
  unfold subst, lift, subst_rec; fold subst_rec. rewrite subst_rec_lift_rec; try omega.  
  rewrite (star_opt_occurs_true); auto. 3: cbv; congruence.

  unfold star_opt at 1; simpl. rewrite star_opt_occurs_true; auto.  2: unfold_op; congruence. 



  2: intro; congruence
  congruence.  split_all.
  cbv; auto. unfold swap; congruence. 
  unfold star_opt at 1. ;  unfold occurs0; fold occurs0. 
unfold lift; rewrite ! occurs_lift_rec_zero. simpl. 
rewrite subst_rec_lift_rec; try omega. 
rewrite ! occurs_lift_rec_zero. simpl. 
unfold subst; rewrite subst_rec_lift_rec; try omega. 
rewrite ! occurs_lift_rec_zero. simpl. 
rewrite subst_rec_lift_rec; try omega. 
rewrite ! lift_rec_null. 
eapply2 zero_red. 
Qed. 
 
*) 



Lemma program_app: forall M N, program (App M N) -> program M /\ program N.
Proof. 
unfold program; intros. inversion H. 
simpl in *; max_out; inversion H0; split; split; auto. 
Qed. 

Fixpoint is_program M := 
match M with 
| Ref _ => false 
| Op _ => true 
| App (Op _) M2 => is_program M2 
| App (App (Op _) M1) M2 => is_program M1 && is_program M2
| _ => false 
end. 
 


Lemma program_is_program: forall M, program M <-> is_program M = true. 
Proof.
induction M; intros; auto.  
(* 3 *) 
  split. unfold program. simpl. intro c; inversion c; discriminate. 
discriminate.
(* 2 *) 
split; intro; unfold program; split; auto. 
(* 1 *) 
gen_case IHM1 M1. 
(* 3 *) 
  split. unfold program. simpl. intro c; inversion c.  
gen_case H0 (maxvar M2); discriminate. 
intro; discriminate. 
(* 2 *) 
split. unfold program.  intro. inversion H. 
eapply2 IHM2. inversion H0; simpl in H1. 
assert(status (App (Op o) M2) = Passive). 
eapply2 closed_implies_passive. 
rewrite H7 in H6; discriminate. 
split; auto. 
intro.
assert(program M2) by eapply2 IHM2. 
 split; auto. nf_out. inversion H0; auto.  
case o; auto. simpl; inversion H0; auto. 
(* 1 *) 
gen_case IHM1 s. 
(* 3 *) 
  split. unfold program. simpl. intro c; inversion c.  
gen_case H0 (maxvar s0); gen_case H0 (maxvar M2); discriminate. 
intro; discriminate. 
(* 2 *) 
split. unfold program.  intro. inversion H.
assert(is_program s0 = true). 
eapply2 IHM1.  split; auto. nf_out. 
inversion H0. 
assert(status (App (App (Op o) s0) M2) = Passive). 
eapply2 closed_implies_passive. 
rewrite H7 in H6; discriminate. inversion H4; auto. case o; auto. 
simpl in *; max_out. 
rewrite H2; simpl. eapply2 IHM2.
eapply2 (program_app (App (Op o) s0) M2).
intro. 
apply eq_sym in H. 
assert(true = is_program s0 /\ true = is_program M2) by eapply2 andb_true_eq.
inversion H0. 
assert(program M2) by eapply2 IHM2. 
assert(program (App (Op o) s0)) by eapply2 IHM1. 
inversion H3; inversion H4. inversion H7. 
split. 
nf_out. case o; auto. case o; auto. simpl in *. 
rewrite H6; rewrite H8; auto.
 split; auto. nf_out. case o; auto. 
simpl in *. rewrite H6; rewrite H8; auto.
(* 1 *) 
gen_case IHM1 s1. 
(* 3 *) 
  split. unfold program. simpl. intro c; inversion c.  
gen_case H0 (maxvar s2); gen_case H0 (maxvar s0);  gen_case H0 (maxvar M2);  discriminate. 
intro; discriminate. 
(* 2 *) 
split. unfold program.  intro. inversion H. inversion H0. 
assert(status (App (App (App (Op o) s2) s0) M2) = Passive). 
eapply2 closed_implies_passive. 
rewrite H7 in H6; discriminate. inversion H6. 
intro.  discriminate. 
split; intro. 
inversion H.  inversion H0. 
assert(status (App (App (App (App s3 s4) s2) s0) M2) = Passive). 
eapply2 closed_implies_passive. 
rewrite H7 in H6; discriminate. inversion H6. 
discriminate.
Qed. 
 
Fixpoint case P M := 
(* case P M is applied to the argument and then the default function.
   The default function is either discared or swapped to the left. 
   Indices in P are renumbered, with binding from left to right 
*)   
 match P with
  | Ref _ => star_opt (App k_op M)               
  | Op Sop => App (App s_op 
                       (App (App s_op f_op)
                            (App (App s_op (App (App s_op
                                                     (star_opt (App (App (App (App (Ref 0) f_op) k_op)
                                                                         k_op) i_op)))
                                                (App k_op (App k_op M))))
                                 (star_opt (swap (Ref 0))))))
                  (star_opt (App k_op (App k_op (swap (Ref 0)))))
    (* star_opt (App (App (App (Op Fop) (Ref 0))
                                 (App (App (App (App (App (App (Ref 0) f_op) k_op) k_op) i_op)
                                           (App k_op (lift 1 M))) 
                                      (swap (Ref 0))))

 
                            (App k_op (App k_op (swap (Ref 0)))))
*) 
  | Op Fop => App (App s_op 
                       (App (App s_op f_op)
                            (App (App s_op (App (App s_op
                                                     (star_opt (App (App (App (App (Ref 0) f_op) k_op)
                                                                         k_op) i_op)))
                                                (star_opt (swap (Ref 0)))))
                                 (App k_op (App k_op M))))) 
                  (star_opt (App k_op (App k_op (swap (Ref 0)))))
(* 

                  star_opt (App (App (App (Op Fop) (Ref 0))
                                 (App (App (App (App (App (App (Ref 0) f_op) k_op) k_op) i_op)
                                           (swap (Ref 0)))
                                      (App k_op (lift 1 M))))
                            (App k_op (App k_op (swap (Ref 0)))))
 *)
  | App P1 P2 => 
if is_program P 
then App (App s_op (App (App s_op (App (App s_op equal_comb) (App k_op P)))
                        (App k_op (App k_op M))))
         (star_opt (swap (Ref 0)))
else case_app_nf case P1 P2 M            
                end
.


Lemma case_S_S: forall M R, sf_red (App (App (case (Op Sop) M) (Op Sop)) R) M.
Proof. 
intros; cbv; repeat eval_tac. 
eapply transitive_red. eapply preserves_app_sf_red.
 eapply preserves_app_sf_red.  eapply preserves_app_sf_red. 
 eapply succ_red. eapply2 f_compound_red. all: repeat eval_tac. 
Qed.

Lemma case_S_F: forall M R, sf_red (App (App (case (Op Sop) M) (Op Fop)) R) (App R (Op Fop)).
Proof. 
intros; cbv. do 22 eval_tac. eapply2 preserves_app_sf_red. repeat eval_tac. 
Qed.


Lemma case_F_F: forall M R, sf_red (App (App (case (Op Fop) M) (Op Fop)) R) M.
Proof. 
intros; cbv; repeat eval_tac. 
Qed.   

Lemma case_F_S: forall M R, sf_red (App (App (case (Op Fop) M) (Op Sop)) R) (App R (Op Sop)).
Proof. 
intros; cbv; repeat eval_tac. 
eapply transitive_red. eapply preserves_app_sf_red.
 eapply preserves_app_sf_red.  eapply preserves_app_sf_red. 
 eapply succ_red. eapply2 f_compound_red.
 all: auto. do 9 eval_tac. eapply2 preserves_app_sf_red. repeat eval_tac. 
Qed.


(* 
Fixpoint pattern_size P :=
  match P with
    | Ref _ => 1
    | Op _ => 0
    | App P1 P2 => pattern_size P1 + (pattern_size P2)
  end.



Lemma lift_rec_preserves_pattern_size: forall M n k, pattern_size (lift_rec M n k) = pattern_size M. 
Proof. induction M; split_all. Qed. 

Lemma pattern_size_closed: forall M, maxvar M = 0 -> pattern_size M = 0. 
Proof. induction M; split_all.  noway. rewrite IHM1; max_out; rewrite IHM2; max_out. Qed. 


Lemma pattern_size_A_k : forall k, pattern_size (A_k k) = 0. 
Proof. unfold A_k. intro. rewrite pattern_size_closed. auto. rewrite A_k_closed. auto. Qed. 

Lemma pattern_size_omega_k : forall k, pattern_size (omega_k k) = 0. 
Proof. unfold omega_k. intro. rewrite pattern_size_closed. auto. 
rewrite ? maxvar_star_opt. unfold maxvar; fold maxvar. 
rewrite?  maxvar_app_comb.   unfold maxvar; fold maxvar. rewrite A_k_closed.
rewrite?  maxvar_app_comb.   unfold maxvar; fold maxvar. auto. 
Qed. 


Lemma pattern_size_lt_maxvar: forall P, maxvar P = 0 -> pattern_size P = 0. 
Proof. induction P; split_all. omega.  max_out. Qed. 


Lemma aux_lift_rec: forall M p n k, 
lift_rec (lift_rec M (p + n) k) p 3 = lift_rec (lift_rec (lift_rec M (p + n) k) p 2) (p+2) 1. 
Proof. 
intros. rewrite (lift_rec_lift_rec (lift_rec M (p + n) k)); try omega. auto. 
Qed. 

(* 
Lemma lift_rec_preserves_case:
  forall P M n k, lift_rec (case P M) n k = case P (lift_rec M (pattern_size P +n) k).
Proof.
  induction P; intros. 
  (* 3 *)
  unfold case, maxvar. rewrite lift_rec_preserves_star_opt. unfold_op. 
  unfold lift_rec; fold lift_rec.  unfold pattern_size. auto.
  (* 2 *)
    unfold case, maxvar, pattern_size, swap, lift_rec; fold lift_rec.
  case o; unfold_op; simpl; auto. 
    (* 1 *) 
    unfold case; fold case. 
assert(is_program (App P1 P2) = true \/ is_program (App P1 P2) <> true) by decide equality. 
inversion H. rewrite H0. 
(* 2 *)
unfold_op; simpl. 
assert(program (App P1 P2)) by eapply2 program_is_program.  inversion H1.   
rewrite lift_rec_preserves_star_opt. 
unfold swap; unfold_op. rewrite ! lift_rec_app. 
rewrite lift_rec_closed. 2: auto. unfold lift_rec; fold lift_rec. relocate_lt.
rewrite 2? lift_rec_closed. 2: simpl in H3; max_out. 2: simpl in H3; max_out. 
rewrite pattern_size_closed. 
unfold lift; rewrite lift_lift_rec; try omega; auto. auto. 
(* 1 *) 
assert(is_program (App P1 P2) = false).
eapply2 not_true_iff_false. 
rewrite H1. 
(* 1 *) 
    unfold case_app_nf, swap, lift. unfold_op. 
    unfold lift_rec; fold lift_rec.
    rewrite ! IHP1. rewrite ! IHP2.  
unfold pattern_size; fold pattern_size.
    unfold lift_rec; fold lift_rec.
unfold plus; fold plus. 
replace (pattern_size P2 + (pattern_size P1 + n)) with 
(pattern_size P1 + pattern_size P2 + n) by omega. 
auto. 
Qed.
*) 

Lemma aux2 : forall M N p k, subst_rec (lift_rec M p (1 + 2)) N
     (S (S (S k)) + p) =
   lift_rec (subst_rec M N (k + p))
     p (1 + 2). 
Proof. 
intros. unfold plus; fold plus. replace (S(S(S (k+ p)))) with (3+ (k+p)) by omega. 
rewrite subst_rec_lift_rec1; try omega. auto. 
Qed. 

Lemma subst_rec_preserves_case:
  forall P M N k, subst_rec (case P M) N k = case P (subst_rec M N (pattern_size P + k)).
Proof.
  induction P; intros. 
  (* 3 *)
  unfold case, maxvar, pattern_size. rewrite subst_rec_preserves_star_opt.
  unfold_op; unfold subst_rec; fold subst_rec; auto.  
  (* 2 *)
  unfold case, maxvar, swap. case o; unfold_op; unfold subst; simpl; auto. 
  (* 1 *)
  unfold case; fold case.
  assert(is_program (App P1 P2) = true \/ is_program (App P1 P2) <> true) by decide equality. 
  inversion H. rewrite H0. 
  (* 2 *) 
  assert(program (App P1 P2)) by eapply2 program_is_program.  inversion H1.   
  rewrite subst_rec_preserves_star_opt. 
  unfold swap; unfold_op; rewrite ! subst_rec_app. 
  rewrite subst_rec_closed. 2: rewrite equal_comb_closed; omega. 
  unfold subst_rec; fold subst_rec. insert_Ref_out.  
  rewrite 2? subst_rec_closed. 2: simpl in H3; max_out. 2: simpl in H3; max_out. 
  rewrite pattern_size_closed. 2: auto.  
  unfold lift; rewrite subst_rec_lift_rec1; try omega. 
  replace (k+0) with k by omega; auto.  
(* 1 *) 
assert(is_program (App P1 P2) = false).
eapply2 not_true_iff_false. 
rewrite H1. 
(* 1 *) 
  unfold case_app_nf, swap. unfold_op. 
  unfold subst_rec; fold subst_rec. insert_Ref_out. 
  rewrite IHP1. rewrite IHP2.  
  unfold subst_rec; fold subst_rec. 
unfold pattern_size; fold pattern_size. 
replace  (k+ (pattern_size P1 + (pattern_size P2))) 
    with (k+ pattern_size P1 + pattern_size P2)
      by omega. 
auto. 
Qed.


Inductive pattern_normal : nat -> SF -> Prop :=
| pnf_normal : forall j M, normal M -> pattern_normal j M
(*  pattern_normal j (Ref n)
| pnf_op : forall j o, pattern_normal j (Op o)
| pnf_active : forall j M1 M2, normal M1 -> normal j M2 -> 
                              status (App M1 M2) = Active -> 
                              pattern_normal j (App M1 M2)  
*) 
| pnf_compound : forall j M1 M2, pattern_normal j M1 -> pattern_normal j M2 -> 
                              compound (App M1 M2) -> pattern_normal j (App M1 M2)
| pnf_active : forall j M1 M2, pattern_normal j M1 -> pattern_normal j M2 -> 
                              status (App M1 M2) = Active -> pattern_normal j (App M1 M2)
| pnf_break : forall j M1 M2, pattern_normal j M1 -> pattern_normal j M2 -> 
                              0 < maxvar M2 -> maxvar M2 <= j -> 
                              pattern_normal j (App M1 M2) 
(* actually, it is enough that one of the pattern variables occurs in M2 *) 
.

(* 
Lemma pattern_normal_1_occurs : 
forall M, pattern_normal 1 M -> 
normal M \/ exists M1 M2, M = App M1 M2 /\ occurs0 M2 = true. 
Proof.
induction M; split_all; try discriminate.  inversion H; subst.  auto. 
right; exists M1; exist M2. split; auto. 
clear - H5 H6. 
induction M2; split_all; simpl in *. 
assert(n= 0) by omega. subst. auto. noway. 
assert(0< maxvar M2_1 \/ 0< maxvar M2_2). 

gen_case H5 (maxvar M2_1);  gen_case H5 (maxvar M2_2). 
left; omega. inversion H. 
rewrite IHM2_1; auto. 
gen_case H6 (maxvar M2_1). gen_case H6 (maxvar M2_2).
gen_case H6 n.  gen_case H6 n0. noway. 
rewrite IHM2_2; auto. apply orb_true_r.  
gen_case H6 (maxvar M2_1). gen_case H6 (maxvar M2_2).
gen_case H6 n.  gen_case H6 n0. noway. 
Qed. 
*) 

Lemma pattern_normal_closed: 
forall M, maxvar M = 0 -> forall j, pattern_normal j M -> normal M. 
Proof. 
induction M; split_all. max_out. inversion H0; subst; auto.
eapply2 nf_compound. 
assert(status (App M1 M2) = Passive). 
eapply2 (closed_implies_passive).  simpl; rewrite H1; rewrite H2; auto. 
rewrite H in H7; discriminate. 
   noway. 
Qed. 

Lemma occurs_maxvar_1: forall M, maxvar M = 1 -> occurs0 M = true.
Proof.
induction M; split_all. inversion H; subst. auto. noway. 
gen3_case IHM1 IHM2 H (maxvar M1). 
rewrite IHM2. apply orb_true_r. auto. 
gen3_case IHM1 IHM2 H (maxvar M2). 
rewrite IHM1. auto. auto. 
gen3_case IHM1 IHM2 H n. 
rewrite IHM1. auto. auto. 
gen3_case IHM1 IHM2 H n0. 
rewrite IHM2.  apply orb_true_r. auto. noway. 
Qed. 
 


Lemma occurs_false_subst_compound: 
forall M N, occurs0 M = false -> compound (subst_rec M N 0) -> compound M. 
Proof.
induction M; split_all.
gen2_case H H0 n.  discriminate. generalize H0; insert_Ref_out; intro. 
inversion H1.
rewrite orb_false_iff in H. inversion H. 
inversion H0; subst. 
gen2_case H1 H4 M1.  gen2_case H1 H4 n. discriminate. 
generalize H4; insert_Ref_out; intro. discriminate. 
inversion H4; subst; auto.  discriminate.
gen2_case H1 H4 M1.  gen2_case H1 H4 n. discriminate. 
generalize H4; insert_Ref_out; intro. discriminate. 
discriminate.  
gen2_case H1 H4 s.  gen2_case H1 H4 n. discriminate. 
generalize H4; insert_Ref_out; intro. discriminate. 
inversion H4; subst; auto.  discriminate.
gen2_case H1 H4 M1.  gen2_case H1 H4 n. discriminate. 
generalize H4; insert_Ref_out; intro. discriminate. 
inversion H4; subst; auto.  discriminate.
gen2_case H1 H4 M1.  gen2_case H1 H4 n. discriminate. 
generalize H4; insert_Ref_out; intro. discriminate. 
discriminate.  
gen2_case H1 H4 s.  gen2_case H1 H4 n. discriminate. 
generalize H4; insert_Ref_out; intro. discriminate. 
inversion H4; subst; auto.  discriminate.
Qed. 


Lemma occurs_false_subst_active: 
forall M N, occurs0 M = false -> status (subst_rec M N 0) = status M. 
Proof.
rank_tac. 
induction p; split_all. assert (rank M >0) by eapply2 rank_positive. noway. 
generalize H H0; clear H H0; case M; intros. 
(* 3 *) 
gen_case H0 n.  discriminate.
(* 2 *) 
split_all.
(* 1 *)  
simpl in H0.  
rewrite orb_false_iff in H0. inversion H0. clear H0 H2. 
generalize H H1; clear H H1; case s; intros. 
(* 3 *) 
gen_case H1 n.  discriminate.
(* 2 *) 
split_all.
(* 1 *)  
simpl in H1.  
rewrite orb_false_iff in H1. inversion H1. 
generalize H H0; clear H H0; case s1; intros. 
(* 3 *) 
gen_case H0 n.  discriminate.
(* 2 *) 
split_all.
(* 1 *)  
simpl in H0.  
rewrite orb_false_iff in H0. inversion H0. 
generalize H H3; clear H H3; case s3; intros. 
(* 3 *) 
gen_case H3 n.  discriminate.
(* 2 *) 
gen_case H o. eapply2 IHp. simpl in *; omega. 
(* 1 *)  
simpl in H3.  
rewrite orb_false_iff in H3. inversion H3. 
unfold subst_rec; fold subst_rec.
replace (status (App (App (App (App s5 s6) s4) s2) s0))
with (status (App (App (App s5 s6) s4) s2)) by auto. 
replace (status
  (App (App (App (App (subst_rec s5 N 0) (subst_rec s6 N 0)) (subst_rec s4 N 0)) (subst_rec s2 N 0))
 (subst_rec s0 N 0)))
with (status  (subst_rec (App (App (App s5 s6) s4) s2) N 0)) by auto. 
eapply2 IHp. simpl in *; omega.  simpl in *; auto. 
rewrite H2; rewrite H4; rewrite H5; rewrite H6; auto.
Qed. 
 


Lemma occurs_false_subst_normal2: 
forall M N, occurs0 M = false -> normal (subst_rec M N 0) -> normal M. 
Proof.
induction M; split_all.
inversion H0; subst. rewrite orb_false_iff in H. inversion H. 
eapply2 nf_active.      
replace(App (subst_rec M1 N 0) (subst_rec M2 N 0)) with (subst_rec (App M1 M2) N 0)  in H5 by auto. 
rewrite occurs_false_subst_status in H5. auto. split_all.
rewrite H1; rewrite H2; auto. 
rewrite orb_false_iff in H. inversion H. 
apply nf_compound. eapply2 IHM1. eapply2 IHM2. 
replace(App (subst_rec M1 N 0) (subst_rec M2 N 0)) with (subst_rec (App M1 M2) N 0)  in H5 by auto. 
apply occurs_false_subst_compound in H5. auto. 
simpl; rewrite H1; rewrite H2; auto. 
Qed.

Lemma normal_star_opt_app: 
forall M1 M2, occurs0 (App M1 M2)  = true 
-> normal (star_opt M1) -> normal (star_opt M2) -> 
normal (star_opt (App M1 M2)).
Proof.
intros.  unfold star_opt; fold star_opt. simpl in H. 
rewrite orb_true_iff in H.  inversion H. rewrite H2. 
eapply2 nf_compound. 
assert(occurs0 M1 = true \/ occurs0 M1 <> true) by decide equality. 
inversion H3. 
(* 2 *) 
rewrite H4. eapply2 nf_compound.
(* 1 *)  
assert(occurs0 M1 = false). gen_case H4 (occurs0 M1). 
assert False by eapply2 H4; noway. 
rewrite H5. 
rewrite (star_opt_occurs_false) in H0. 2: auto. 
inversion H0; subst. 
inversion H10. 
gen2_case H1 H2 M2. 
gen2_case H1 H2 n; discriminate. discriminate. 
rewrite H2. 
unfold_op; eapply2 nf_compound. 
rewrite star_opt_occurs_false; auto.
Qed. 

(* delete 
Lemma pattern_normal_subst_occurs_false: 
forall M j, occurs0 M = false -> pattern_normal j M  -> 
pattern_normal (pred j) (subst M (Op Sop)). 
Proof. 
induction M; split_all. 
gen2_case H H0 n; unfold subst, subst_rec; insert_Ref_out. 
discriminate. eapply2 pnf_normal. 
unfold subst, subst_rec; eapply2 pnf_normal. 
rewrite orb_false_iff in H. inversion H. 
inversion H0; subst. 
eapply2 pnf_normal. 
unfold subst. eapply2 occurs_false_subst_normal. 
simpl; rewrite H1; rewrite H2; auto.
eapply2 pnf_compound.  fold subst_rec.  
eapply2 occurs_false_subst_normal. fold subst_rec.
 assert(compound (subst_rec (App M1 M2) (Op Sop) 0)).  
(eapply2 subst_rec_preserves_compounds).
simpl in H3. auto. 
unfold subst, subst_rec; fold subst_rec. 
apply pnf_break; fold subst_rec.
eapply2 IHM1. eapply2 IHM2. 
  

assert(maxvar M2noway. 



  inversion H1; subst; auto. 
e

auto. 

*) 


Lemma occurs_false_subst_rec_maxvar_gt0 : 
forall M, occurs0 M = false -> 0< maxvar M -> 
forall N, 0 < maxvar (subst_rec M N 0). 
Proof.
induction M; split_all; subst.  
simpl in *. gen_case H n. discriminate. omega. 
simpl in *. 
assert(occurs0 M1 = false /\ occurs0 M2 = false). eapply2 orb_false_iff. 
inversion H. 
assert(0< maxvar M1 \/ 0< maxvar M2). 
gen_case H0 (maxvar M1). left; omega. 
inversion H2; subst. inversion H1. 
assert(0< (maxvar (subst_rec M1 N 0))) by eapply2 IHM1. 
assert(Nat.max (maxvar (subst_rec M1 N 0)) (maxvar (subst_rec M2 N 0)) >= 
maxvar (subst_rec M1 N 0)) by eapply2 max_is_max.  omega.  inversion H1. 
assert(0< (maxvar (subst_rec M2 N 0))) by eapply2 IHM2. 
assert(Nat.max (maxvar (subst_rec M1 N 0)) (maxvar (subst_rec M2 N 0)) >= 
maxvar (subst_rec M2 N 0)) by eapply2 max_is_max.  omega.
Qed. 

Lemma occurs_false_subst_rec_maxvar_lt : 
forall M, occurs0 M = false ->  forall j, maxvar M <= j -> 
forall N, maxvar (subst_rec M N 0) <= pred j.  
Proof.
induction M; split_all; subst.  simpl in *.
 gen2_case H H0 n. discriminate. omega. omega. 
 simpl in *. 
assert(occurs0 M1 = false /\ occurs0 M2 = false). eapply2 orb_false_iff. 
inversion H1. 
assert (Nat.max (maxvar M1) (maxvar M2)  >= maxvar M1) by eapply2 max_is_max. 
assert (Nat.max (maxvar M1) (maxvar M2)  >= maxvar M2) by eapply2 max_is_max. 
assert(maxvar M1 <= j /\ maxvar M2 <= j). 
split; omega.  inversion H6.
assert(pred j >=  Nat.max (maxvar (subst_rec M1 N 0)) (maxvar (subst_rec M2 N 0))). 
eapply2 max_max2.  omega. 
Qed. 


Lemma occurs_false_subst_pattern_normal: 
forall M j N, occurs0 M = false -> pattern_normal j M -> pattern_normal (pred j) (subst_rec M N 0). 
Proof.
induction M; split_all.
(* 3 *) 
gen2_case H H0 n. discriminate.  insert_Ref_out. eapply2 pnf_normal.
(* 2 *)  
eapply2 pnf_normal.
(* 1 *)    
assert(occurs0 M1 = false /\ occurs0 M2 = false) by eapply2 orb_false_iff. 
inversion H1. 
inversion H0.
(* 4 *) 
 eapply2 pnf_normal. 
assert(normal (subst_rec (App M1 M2) N 0)) by eapply2 occurs_false_subst_normal. 
simpl in H7; auto.
(* 3 *) 
eapply2 pnf_compound. 
assert(compound (subst_rec (App M1 M2) N 0)) by eapply2 subst_rec_preserves_compounds. 
simpl in H10; auto.
(* 2 *)
eapply2 pnf_active. 
replace (App (subst_rec M1 N 0) (subst_rec M2 N 0)) with (subst_rec (App M1 M2) N 0) by auto. 
rewrite occurs_false_subst_status.  auto. simpl; auto. 
(* 1 *) 
 subst. 
eapply pnf_break. eapply2 IHM1. eapply2 IHM2.
(* 2 *)  
eapply2 occurs_false_subst_rec_maxvar_gt0.
eapply2 occurs_false_subst_rec_maxvar_lt. 
Qed. 

Lemma pattern_normal_star_opt: 
forall M j, pattern_normal j M -> pattern_normal (pred j) (star_opt M). 
Proof. 
induction M; intros. 
(* 3 *) 
eapply2 pnf_normal. eapply2 star_opt_normal.  
(* 2 *) 
eapply2 pnf_normal. eapply2 star_opt_normal.  
(* 1 *) 
 subst; inversion H; subst. 
(* 4 *) 
eapply2 pnf_normal. eapply2 star_opt_normal.
(* 3 *)   
unfold star_opt; fold star_opt. 
assert(occurs0 M1 = true \/ occurs0 M1 <> true) by decide equality. 
inversion H0. 
(* 4 *) 
rewrite H1. eapply2 pnf_compound. eapply2 pnf_compound.  eapply2 pnf_normal. 
(* 3 *)  
assert(pattern_normal  (pred j) (star_opt M2)) by eapply2 IHM2. 
assert(occurs0 M1 = false). gen_case H1 (occurs0 M1). 
assert False by eapply2 H1; noway. 
rewrite H6.
assert(pattern_normal (pred j) (subst_rec M1 (Op Sop) 0)) .
eapply2 occurs_false_subst_pattern_normal.
assert(pattern_normal (pred j) (star_opt M1)) by eapply2 IHM1. 
clear IHM1 IHM2 H H0 H1 . 
(* 3 *)  
unfold subst, subst_rec; fold subst_rec. 
assert(pattern_normal (pred j) (App (App (Op Sop) (star_opt M1)) (star_opt M2))). 
eapply2 pnf_compound. eapply2 pnf_compound. eapply2 pnf_normal. 
assert(occurs0 M2 = false -> 
  pattern_normal (pred j) (App k_op (App (subst_rec M1 (Op Sop) 0) (subst_rec M2 (Op Sop) 0)))). 
intro. 
assert(pattern_normal (pred j) (subst_rec M2 (Op Sop) 0)).
rewrite star_opt_occurs_false in H3.  2: auto. 
inversion H3; subst; auto.
eapply2 pnf_normal.  inversion H1; auto. 
eapply2 pnf_compound. unfold_op;  eapply2 pnf_normal. 
2: unfold_op; auto. 
eapply2 pnf_compound.  
assert(compound (subst_rec (App M1 M2) (Op Sop) 0)).  
(eapply2 subst_rec_preserves_compounds).
simpl in H9.  inversion H9; subst; auto.
(* 3 *) 
gen3_case H H0 H7 M2. gen3_case H H0 H7 n. 
gen3_case H H0 H7 (occurs0 s || occurs0 s0). 
(* 2 *) 
unfold star_opt; fold star_opt. 
assert(occurs0 M1 = true \/ occurs0 M1 <> true) by decide equality. 
inversion H0. 
(* 3 *) 
rewrite H1. eapply2 pnf_compound. eapply2 pnf_compound.  eapply2 pnf_normal. 
(* 2 *)  
assert(pattern_normal  (pred j) (star_opt M2)) by eapply2 IHM2. 
assert(occurs0 M1 = false). gen_case H1 (occurs0 M1). 
assert False by eapply2 H1; noway. 
rewrite H6.
assert(pattern_normal (pred j) (subst_rec M1 (Op Sop) 0)) .
eapply2 occurs_false_subst_pattern_normal.
assert(pattern_normal (pred j) (star_opt M1)) by eapply2 IHM1. 
clear IHM1 IHM2 H H0 H1 . 
(* 2 *)  
unfold subst, subst_rec; fold subst_rec. 
assert(pattern_normal (pred j) (App (App (Op Sop) (star_opt M1)) (star_opt M2))). 
eapply2 pnf_compound. eapply2 pnf_compound. eapply2 pnf_normal. 
assert(occurs0 M2 = false -> 
  pattern_normal (pred j) (App k_op (App (subst_rec M1 (Op Sop) 0) (subst_rec M2 (Op Sop) 0)))). 
intro. 
assert(pattern_normal (pred j) (subst_rec M2 (Op Sop) 0)).
rewrite star_opt_occurs_false in H3.  2: auto. 
inversion H3; subst; auto.
eapply2 pnf_normal.  inversion H1; auto. 
eapply2 pnf_compound. unfold_op;  eapply2 pnf_normal. 
2: unfold_op; auto. 
eapply2 pnf_active.
replace (App (subst_rec M1 (Op Sop) 0) (subst_rec M2 (Op Sop) 0)) with 
(subst_rec (App M1 M2) (Op Sop) 0) by auto. 
rewrite occurs_false_subst_status. auto.  
simpl; rewrite H6; rewrite H0; auto. 
(* 2 *) 
gen3_case H H0 H7 M2. gen3_case H H0 H7 n. 
gen3_case H H0 H7 (occurs0 s || occurs0 s0). 
(* 1 *) 
assert(M2 = Ref 0 \/ M2 <> Ref 0) by repeat decide equality. 
inversion H0; subst.  
assert(occurs0 M1 = true \/ occurs0 M1 <> true) by decide equality. 
inversion H1; subst. 
(* 3 *) 
unfold star_opt; fold star_opt. rewrite H4. 
eapply2 pnf_compound. eapply2 pnf_compound. eapply2 pnf_normal. 
assert(occurs0 M1 = false). 
gen_case H4 (occurs0 M1).  assert False by eapply2 H4; noway.  
unfold star_opt; fold star_opt. rewrite H7.
eapply2 occurs_false_subst_pattern_normal. 
assert(occurs0 M1 = true \/ occurs0 M1 <> true) by decide equality. 
inversion H4; subst. 
(* 2 *) 
unfold star_opt; fold star_opt. rewrite H7. 
eapply2 pnf_compound. eapply2 pnf_compound. eapply2 pnf_normal. 
assert(occurs0 M1 = false). 
gen_case H7 (occurs0 M1).  assert False by eapply2 H7; noway.  
unfold star_opt; fold star_opt. rewrite H8.
(* 1 *) 
assert(pattern_normal  (pred j) (star_opt M2)) by eapply2 IHM2. 
assert(pattern_normal (pred j) (subst_rec M1 (Op Sop) 0)) .
eapply2 occurs_false_subst_pattern_normal.
assert(pattern_normal (pred j) (star_opt M1)) by eapply2 IHM1. 
(* 1 *)  
unfold subst, subst_rec; fold subst_rec. 
assert(pattern_normal (pred j) (App (App (Op Sop) (star_opt M1)) (star_opt M2))). 
eapply2 pnf_compound. eapply2 pnf_compound. eapply2 pnf_normal. 
assert(occurs0 M2 = false -> 
  pattern_normal (pred j) (App k_op (App (subst_rec M1 (Op Sop) 0) (subst_rec M2 (Op Sop) 0)))). 
intro. 
assert(pattern_normal (pred j) (subst_rec M2 (Op Sop) 0)).
rewrite star_opt_occurs_false in H9.  2: auto. 
eapply2 occurs_false_subst_pattern_normal. unfold_op. 
eapply2 pnf_compound. eapply2 pnf_normal. 
eapply2 pnf_break. 
eapply2 occurs_false_subst_rec_maxvar_gt0. 
eapply2 occurs_false_subst_rec_maxvar_lt. 
(* 1 *) 
gen3_case H10 H12 H13 M2. gen3_case H10 H12 H13 n. 
gen3_case H10 H12 H13 (occurs0 s || occurs0 s0). 
Qed. 


Lemma pattern_normal_zero: forall M, pattern_normal 0 M -> normal M. 
Proof. 
induction M; split_all. inversion H; subst. auto. 
eapply2 nf_compound.  eapply2 nf_active. noway. 
Qed. 


Lemma pattern_normal_gt: 
forall j M, pattern_normal j M -> forall k, j <= k -> pattern_normal k M. 
Proof.
intros j M pn; induction pn; split_all. 
eapply2 pnf_normal. eapply2 pnf_compound. eapply2 pnf_active. eapply2 pnf_break.  omega. 
Qed. 


Lemma pattern_normal_app_comb: forall M N j, pattern_normal j M -> pattern_normal j N -> 
pattern_normal j (app_comb M N). 
Proof. 
intros. replace (app_comb M N) with 
(App (App s_op (App (App s_op (App k_op M)) (App k_op N))) i_op) by auto. 
unfold_op. eapply2 pnf_compound.  eapply2 pnf_compound. eapply2 pnf_normal.  
unfold_op. eapply2 pnf_compound.  eapply2 pnf_compound. eapply2 pnf_normal.  
eapply2 pnf_compound.  eapply2 pnf_normal.
eapply2 pnf_compound.  eapply2 pnf_normal. eapply2 pnf_normal.
Qed. 


Lemma case_normal: 
forall (P M : SF), normal M -> normal (case P M).
Proof.
  induction P; intros.
  (* 3 *)
  unfold case, maxvar.   eapply2 star_opt_normal. unfold_op; split_all. 
  (* 2 *) 
unfold case, swap; unfold_op; intros. case o; nf_out. 
apply nf_active. nf_out. eapply2 nf_active; nf_out. 
eapply2 nf_active; nf_out. 
unfold lift; apply lift_rec_preserves_normal; auto. 
nf_out. cbv; auto.  
apply nf_active. nf_out.
repeat (apply nf_active; nf_out). 
unfold lift; apply lift_rec_preserves_normal; auto. 
nf_out. cbv; auto.  
  (* 1 *) 
  unfold case; fold case; unfold case_app_nf. 
assert(is_program (App P1 P2) = true \/ is_program (App P1 P2) <> true) by decide equality. 
inversion H0. rewrite H1. 
(* 2 *) 
rewrite star_opt_occurs_true. 2: cbv; auto. 2: unfold swap; discriminate. 
rewrite star_opt_occurs_true. 2: cbv; auto. 2: unfold swap; discriminate. 
rewrite star_opt_occurs_true. 2: cbv; auto. 2: unfold swap; discriminate. 
rewrite star_opt_eta.
nf_out.  
unfold subst; rewrite subst_rec_closed. eapply2 equal_comb_normal. 
rewrite equal_comb_closed; omega. 
assert(program (App P1 P2)) by eapply2 program_is_program. inversion H2; auto. 
unfold lift; apply lift_rec_preserves_normal. auto. 
unfold swap; unfold_op; nf_out.  
eapply2 occurs_closed. 
(* 1 *) 
assert(is_program (App P1 P2) = false).
eapply2 not_true_iff_false. 
rewrite H2. 
(* 1 *) 
  unfold case_app_nf, swap. unfold_op; nf_out. 
inversion H; eapply2 IHP1;  eapply2 IHP2. 
eapply2 nf_compound. eapply2 nf_compound. 
Qed. 




Lemma case_pattern_normal: 
forall (P M : SF) j, pattern_normal j M -> 
pattern_normal (j - (pattern_size P)) (case P M).
Proof.
  induction P; intros. 
  (* 3 *)
  unfold pattern_size. unfold case. 
replace (j-1) with (pred j) by omega. 
eapply pattern_normal_star_opt; auto. 
unfold_op. eapply2 pnf_compound. eapply2 pnf_normal. 
(* 2 *) 
unfold pattern_size, case; simpl. replace (j-0) with j by omega. 
case o. 
(* 3 *) 
eapply2 pnf_compound. eapply2 pnf_compound. eapply2 pnf_normal. 
eapply2 pnf_compound. eapply2 pnf_compound. eapply2 pnf_normal. 
unfold subst, subst_rec; eapply2 pnf_normal. 
eapply2 pnf_compound. eapply2 pnf_compound. eapply2 pnf_normal. 
eapply2 pnf_compound. eapply2 pnf_compound. eapply2 pnf_normal. 
eapply2 pnf_compound. eapply2 pnf_compound. eapply2 pnf_normal. 
eapply2 pnf_compound. eapply2 pnf_compound. eapply2 pnf_normal. 
eapply2 pnf_compound. eapply2 pnf_compound. eapply2 pnf_normal. 
eapply2 pnf_normal. nf_out. 
unfold subst, subst_rec; eapply2 pnf_normal. unfold_op. nf_out. 
unfold_op; eapply2 pnf_compound. eapply2 pnf_normal. 
unfold subst, subst_rec; eapply2 pnf_normal. 
unfold_op; eapply2 pnf_compound. eapply2 pnf_normal. 
unfold subst, subst_rec; eapply2 pnf_normal. 
2:unfold_op; eapply2 pnf_compound. 
2: eapply2 pnf_normal. 2: nf_out.  
2: unfold subst, subst_rec; nf_out. 
2:unfold subst, subst_rec; eapply2 pnf_normal. 
2: unfold_op; eapply2 pnf_compound. 
2: unfold subst, subst_rec; eapply2 pnf_normal. 
2: unfold subst, subst_rec; eapply2 pnf_normal. 
2: nf_out.  
(* 3 *) 
unfold lift. rewrite ! occurs_lift_rec_zero. gen_case H M. gen_case H n. relocate_lt. 
unfold_op. eapply2 pnf_compound.  eapply2 pnf_normal. 
eapply2 pnf_normal. unfold subst; nf_out.  insert_Ref_out; auto. 
relocate_lt. eapply2 pnf_normal. unfold subst; nf_out.  insert_Ref_out; auto. 
eapply2 pnf_normal. unfold subst; nf_out. 
unfold_op; eapply2 pnf_compound. eapply2 pnf_normal.
unfold subst, subst_rec; fold subst_rec. 
rewrite ! subst_rec_lift_rec; try omega.  rewrite ! lift_rec_null. 
eapply2 pnf_compound. eapply2 pnf_normal.
(* 2 *) 
unfold subst, subst_rec; fold subst_rec. 
eapply2 pnf_compound. eapply2 pnf_compound. eapply2 pnf_normal. 
eapply2 pnf_compound. eapply2 pnf_normal. 
eapply2 pnf_compound. eapply2 pnf_compound. eapply2 pnf_normal. 
eapply2 pnf_compound. eapply2 pnf_compound. eapply2 pnf_normal. 
eapply2 pnf_compound. eapply2 pnf_compound. eapply2 pnf_normal. 
eapply2 pnf_compound. eapply2 pnf_normal. unfold_op; unfold subst_rec; nf_out. 
eapply2 pnf_normal. unfold_op; unfold subst_rec; nf_out. 
eapply2 pnf_normal. unfold_op; unfold subst_rec; nf_out. 
eapply2 pnf_normal. unfold_op; unfold subst_rec; nf_out. 
2: eapply2 pnf_normal; unfold_op; unfold subst_rec; nf_out. 
(* 2 *) 
unfold lift. gen_case H M; unfold lift_rec; fold lift_rec. 
gen_case H n. relocate_lt. unfold plus. insert_Ref_out.
eapply2 pnf_normal; nf_out. 
eapply2 pnf_normal; nf_out. 
relocate_lt. unfold plus. insert_Ref_out. nf_out. 
eapply2 pnf_normal; nf_out. 
(* 2 *) 
rewrite ! occurs_lift_rec_zero. simpl. 
rewrite ! subst_rec_lift_rec; try omega. rewrite ! lift_rec_null.
unfold_op; eapply2 pnf_compound. eapply2 pnf_normal.  eapply2 pnf_compound. 
eapply2 pnf_normal.
(* 1 *) 
unfold pattern_size; fold pattern_size. 
unfold case; fold case.
assert(is_program (App P1 P2) = true \/ is_program (App P1 P2) <> true) by decide equality. 
inversion H0. rewrite H1. 
(* 2 *) 
rewrite star_opt_occurs_true. 2: cbv; auto. 2: unfold swap; discriminate. 
rewrite star_opt_occurs_true. 2: cbv; auto. 2: unfold swap; discriminate. 
rewrite star_opt_occurs_true. 2: cbv; auto. 2: unfold swap; discriminate. 
rewrite star_opt_eta.
eapply2 pnf_compound. eapply2 pnf_compound. eapply2 pnf_normal.  
eapply2 pnf_compound. eapply2 pnf_compound. eapply2 pnf_normal.  
eapply2 pnf_compound. eapply2 pnf_compound. eapply2 pnf_normal.  
eapply2 pnf_normal. unfold subst; rewrite subst_rec_closed. 
eapply2 equal_comb_normal. rewrite equal_comb_closed; omega. 
eapply2 pnf_normal. eapply2 star_opt_normal. 
assert(program (App P1 P2)) by eapply2 program_is_program. 
inversion H2; auto. 
unfold_op. rewrite star_opt_occurs_false.
unfold lift, subst_rec; fold subst_rec.   
rewrite subst_rec_lift_rec; try omega. rewrite lift_rec_null. 
eapply2 pnf_compound. 
unfold_op; eapply2 pnf_normal.   
eapply2 pnf_compound. eapply2 pnf_normal. 
rewrite ! pattern_size_closed. 
replace (j-(0+0)) with j by omega. auto. 
assert(program (App P1 P2)) by eapply2 program_is_program. 
inversion H2.  simpl in H4; max_out. 
assert(program (App P1 P2)) by eapply2 program_is_program. 
inversion H2.  simpl in H4; max_out. 
unfold_op; auto. 
unfold occurs0; fold occurs0. 
unfold lift; rewrite occurs_lift_rec_zero.  auto. 
eapply2 pnf_normal. unfold swap; unfold_op; nf_out. 
eapply2 occurs_closed. 
(* 1 *) 
assert(is_program (App P1 P2) = false).
eapply2 not_true_iff_false. 
rewrite H2. 
(* 1 *) 
  unfold case_app_nf, swap. unfold_op; nf_out. 
eapply2 pnf_compound. eapply2 pnf_compound. eapply2 pnf_normal.  
eapply2 pnf_compound. eapply2 pnf_normal.  nf_out. 
eapply2 pnf_compound. eapply2 pnf_normal.  
eapply2 pnf_compound. eapply2 pnf_compound. eapply2 pnf_normal.  
eapply2 pnf_compound. eapply2 pnf_normal. 
eapply2 pnf_compound. eapply2 pnf_compound. eapply2 pnf_normal.
2: eapply2 pnf_normal. 2: nf_out.   
2: eapply2 pnf_normal. 2: nf_out.   
2: unfold_op; auto. 2: eapply2 pnf_normal.  2: nf_out.
(* 1 *) 
replace (j - (pattern_size P1 + pattern_size P2)) with (j - pattern_size P2 - pattern_size P1)
by omega. 
eapply2 IHP1. eapply2 IHP2. 
unfold_op;  eapply2 pnf_compound. eapply2 pnf_normal. 
eapply2 pnf_compound. eapply2 pnf_normal.
Qed. 
 

end experiment  *) 



(* matching *) 

Inductive matching : SF -> SF -> list SF -> Prop :=
| match_ref : forall i M, matching (Ref i) M (cons M nil)
| match_op: forall o, matching (Op o) (Op o) nil
| match_app: forall p1 p2 M1 M2 sigma1 sigma2,
               (compound (App p1 p2) \/ status (App p1 p2) = Active) -> compound (App M1 M2) ->
               matching p1 M1 sigma1 -> matching p2 M2 sigma2 ->
               matching (App p1 p2) (App M1 M2) ((map (lift (length sigma1)) sigma2) ++ sigma1)
.

Hint Constructors matching. 

Lemma matching_lift:
  forall P M sigma, matching P M sigma -> forall k, matching P (lift k M) (map (lift k) sigma). 
Proof.
  induction P; split_all; inversion H; subst; unfold map; fold map; auto. 
(* 2 *) 
replace (lift k (App M1 M2)) with (App (lift k M1) (lift k M2)) by (unfold lift; auto). 
replace(fix map (l : list SF) : list SF :=
            match l with
            | nil => nil
            | a :: t => lift (length sigma1) a :: map t
            end) with (map (lift (length sigma1))) by auto.
replace (fix map (l : list SF) : list SF :=
         match l with
         | nil => nil
         | a :: t => lift k a :: map t
         end) with (map (lift k)) by auto. 
rewrite map_app.
replace (map (lift k) (map (lift (length sigma1)) sigma2)) with
         (map (lift (length (map (lift k) sigma1))) (map (lift k) sigma2)).
eapply2 match_app. 
replace (App (lift k M1) (lift k M2)) with  (lift k (App M1 M2)) by (unfold lift; auto). 
unfold lift. eapply2 lift_rec_preserves_compound. 
clear. induction sigma2; split_all. rewrite IHsigma2. rewrite map_length. 
unfold lift; repeat rewrite lift_rec_lift_rec; try omega. 
replace (length sigma1 + k) with (k+ length sigma1) by omega. auto.
Qed.


Lemma program_matching: forall M, program M -> matching M M nil. 
Proof.
  induction M; split_all.
  inversion H; split_all. simpl in *; noway. 
  inversion H; split_all. inversion H0.
  assert(status (App M1 M2) = Passive) by eapply2 closed_implies_passive.
  rewrite H6 in H7; discriminate.
  replace (nil: list SF)
  with (List.map (lift (length (nil: list SF))) (nil: list SF) ++ (nil: list SF))
    by split_all.
  eapply2 match_app. simpl in *. max_out. eapply2 IHM1. unfold program; auto.
  simpl in *. max_out. eapply2 IHM2. unfold program; auto.
Qed. 

Lemma program_matching2: forall M sigma, matching M M sigma -> maxvar M = 0 -> program M. 
Proof.
  induction M; split_all. noway. unfold program; auto. 
  inversion H; split_all; subst. unfold program; split; auto.  eapply2 nf_compound. 
  eapply2 IHM1. max_out.  eapply2 IHM2. max_out. 
Qed. 



  
Lemma pattern_is_closed: 
forall P, maxvar P = 0 -> forall M sigma, matching P M sigma -> M = P /\ sigma = nil. 
Proof. 
induction P; intros; inversion H; subst.  
(* 2 *) 
inversion H0; auto. 
(* 1 *) 
inversion H0; subst; simpl in *; max_out. 
assert(M1 = P1 /\ sigma1 = nil). eapply2 IHP1 . 
assert(M2 = P2 /\ sigma2 = nil). eapply2 IHP2 . 
split_all; subst. inversion H2; inversion H7; subst; split; auto.  
Qed. 


(* 
Lemma maxvar_case_app : 
forall P1 P2, 
(forall M : SF, maxvar (case P1 M) = maxvar M - pattern_size P1) -> 
(forall M : SF, maxvar (case P2 M) = maxvar M - pattern_size P2) -> 
forall M, maxvar (case_app case P1 P2 M) = maxvar M - pattern_size (App P1 P2). 
Proof. 
intros. unfold case_app. 
rewrite maxvar_star_opt. 
unfold_op. unfold maxvar; fold maxvar.  unfold max; fold max. 
unfold lift; rewrite ! lift_rec_preserves_star_opt. 
unfold lift_rec; fold lift_rec. 
rewrite lift_rec_lift_rec; try omega. 
rewrite ! maxvar_star_opt. 
relocate_lt. 
rewrite ! lift_rec_preserves_case. 
unfold lift_rec; fold lift_rec. 
unfold maxvar; fold maxvar. 
unfold max; fold max. 
rewrite H; rewrite H0. 
unfold maxvar; fold maxvar. 
unfold max; fold max. 
rewrite ! max_pred. simpl. rewrite ! max_zero. 

replace (pattern_size P2 + (pattern_size P1 + 0)) 
with (pattern_size P1 + pattern_size P2) by omega. 
replace (maxvar (lift_rec M (pattern_size P1 + pattern_size P2) 3) -
             pattern_size P2 - pattern_size P1)
with (maxvar (lift_rec M (pattern_size P1 + pattern_size P2) 3) -
             (pattern_size P1 + pattern_size P2)) by omega. 

replace (pred
     match
       pred
         (pred
            (maxvar (lift_rec M (pattern_size P1 + pattern_size P2) 3) -
             (pattern_size P1 + pattern_size P2)))
     with
     | 0 => 1
     | S m' => S m'
     end)
with (match
       pred
         (pred
            (maxvar (lift_rec M (pattern_size P1 + pattern_size P2) 3) -
             (pattern_size P1 + pattern_size P2)))
     with
     | 0 => 0
     | S m' => m'
     end).

apply aux4. 

case (pred
         (pred
            (maxvar (lift_rec M (pattern_size P1 + pattern_size P2) 3) -
             (pattern_size P1 + pattern_size P2)))); split_all. 
Qed. 

Lemma maxvar_lift: forall M, pred (maxvar (lift 1 M)) = maxvar M. 
Proof.
induction M; split_all. relocate_lt. omega. 
rewrite max_pred. unfold lift in *. auto. 
Qed. 



Lemma maxvar_case : forall P M, maxvar (case P M) = maxvar M - (pattern_size P).
Proof.
  induction P; intros; unfold case; fold case; unfold maxvar; fold maxvar.
  (* 3 *)
  rewrite maxvar_star_opt. split_all. omega. 
  (* 2 *)
case o; unfold_op; unfold pattern_size.  
  rewrite maxvar_star_opt. simpl. 
replace (maxvar M - 0) with (maxvar M) by omega.
replace (match
       Nat.max match maxvar (lift 1 M) with
               | 0 => 1
               | S m' => S m'
               end 1
     with
     | 0 => 1
     | S m' => S m'
     end)
with (S (pred (maxvar (lift 1 M)))). 
rewrite max_pred. simpl.  rewrite ! maxvar_lift. eapply2 max_zero. 
case (maxvar (lift 1 M)); intros; cbv; auto. fold max. 
rewrite max_zero; auto. 
rewrite maxvar_star_opt. simpl. 
replace (maxvar M - 0) with (maxvar M) by omega.
replace (max (match match maxvar (lift 1 M) with
           | 0 => 1
           | S m' => S m'
           end with
     | 0 => 1
     | S m' => S m'
     end) 1)
with (S (pred (maxvar (lift 1 M)))). 
simpl.  rewrite ! maxvar_lift. auto.
case (maxvar (lift 1 M)); intros; cbv; auto. fold max. 
rewrite max_zero; auto. 
(* 1 *)
unfold case_app_nf.
assert(is_program (App P1 P2) = true \/ is_program(App P1 P2) <> true)
by decide equality. 
inversion H. 
rewrite H0. 
assert(program (App P1 P2)) by eapply2 program_is_program. 
inversion H1. 
(* 2 *) 
rewrite star_opt_occurs_true. 2: cbv; auto. 2: unfold swap; discriminate. 
rewrite star_opt_occurs_true. 2: cbv; auto. 2: unfold swap; discriminate. 
rewrite star_opt_occurs_true. 2: cbv; auto. 2: unfold swap; discriminate. 
rewrite star_opt_eta.
unfold subst; rewrite subst_rec_closed. 2: auto. 
2: rewrite occurs_closed; auto. 
rewrite star_opt_closed. 2: auto.  
rewrite star_opt_occurs_false. 
2: unfold_op; unfold occurs0; fold occurs0. 
2: unfold lift; rewrite occurs_lift_rec_zero; auto. 
unfold_op; unfold subst_rec; fold subst_rec.
unfold lift; rewrite subst_rec_lift_rec; try omega. rewrite lift_rec_null. 
unfold swap; unfold_op. 
rewrite star_opt_occurs_true.  2: cbv; auto. 2: discriminate. 
rewrite star_opt_closed; auto. 
rewrite star_opt_eta; auto. 
unfold subst, subst_rec. rewrite pattern_size_closed. 2: auto. 
unfold_op; unfold maxvar; fold maxvar. unfold max; fold max.
rewrite ! max_zero. 
rewrite equal_comb_closed. 
assert(maxvar P1 = 0) by (simpl in H3; max_out).
assert(maxvar P2 = 0) by (simpl in H3; max_out). rewrite H4; rewrite H5.
simpl. omega.
(* 1 *) 
assert(is_program (App P1 P2) = false) by 
eapply2 not_true_iff_false. 
rewrite H1. 
(* 1 *) 
unfold_op; simpl. rewrite ! max_zero. 
rewrite IHP1. rewrite IHP2. simpl. omega. 
Qed. 

 *)


Lemma program_matching3: 
forall P M sigma, matching P M sigma -> maxvar P = 0 -> M = P /\ sigma = nil. 
Proof.
  induction P; split_all. noway. 
  inversion H; split_all; subst. 
  inversion H; split_all; subst. 
  simpl in H0; max_out. 
  assert(M1 = P1 /\ sigma1 = nil) by eapply2 IHP1.  
  assert(M2 = P2 /\ sigma2 = nil) by eapply2 IHP2.   
  inversion H0; inversion H6; subst; split; cbv; auto.  
Qed. 

Lemma case_by_matching:
  forall P N sigma,  matching P N sigma ->
                     forall M, sf_red (App (case P M) N) (App k_op (fold_left subst sigma M)). 
Proof.
  induction P; intros.
  (* 3 *)
  inversion H; subst. unfold fold_left.  unfold case; unfold_op.  eapply2 star_opt_beta.
  (* 2 *)
  inversion H; subst. unfold fold_left.  unfold case; unfold_op. case o. 
  cbv.   repeat eval_tac. 
  eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red.
  eapply succ_red. eapply2 f_compound_red. 1,2,3,4,5: repeat eval_tac.
  (* 1 *)
  unfold case; fold case. 
  assert(is_program (App P1 P2) = true \/ is_program(App P1 P2) <> true)
by decide equality. 
inversion H0. 
rewrite H1. 
assert(program (App P1 P2)) by eapply2 program_is_program. 
eval_tac. eval_tac. eval_tac.
eapply transitive_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
auto.  eval_tac. eval_tac. eval_tac. 
assert(N = App P1 P2 /\ sigma = nil). 
eapply2 program_matching3.  inversion H2; auto. 
inversion H3; subst. 
eapply transitive_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. 
eapply2 equal_programs. auto. auto. 
unfold_op; eval_tac.
(* 1 *)  
assert(is_program (App P1 P2) = false) by 
eapply2 not_true_iff_false. 
rewrite H2. 
(* 1 *) 
  unfold case_app_nf. eval_tac. eval_tac. eval_tac. 
  eapply transitive_red. eapply preserves_app_sf_red.  
  eapply succ_red. eapply2 f_compound_red. 
  inversion H. subst; auto. 
  all: eval_tac. eval_tac. eval_tac. eval_tac. eval_tac.  
(* 1 *) 
inversion H; subst. simpl. 
  eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red.  eapply preserves_app_sf_red.  
eapply2 IHP1. eval_tac. auto. eval_tac. eval_tac. eval_tac. 
 (* 1 *) 
rewrite fold_subst_list. rewrite fold_subst_list. rewrite fold_subst_list.
eapply transitive_red. eapply list_subst_preserves_sf_red. 
eapply preserves_app_sf_red. eapply preserves_app_sf_red.
eapply IHP2. eapply2 matching_lift. 
unfold lift; simpl. auto. unfold lift; simpl. auto. 
eapply transitive_red. eapply list_subst_preserves_sf_red. 
eval_tac. 
repeat rewrite list_subst_preserves_app. repeat rewrite list_subst_preserves_op. 
eval_tac.   repeat eapply2 preserves_app_sf_red.
rewrite fold_left_app. auto. 
Qed. 




Definition extension P M R := App (App s_op (case P M)) (App k_op R). 

Proposition extensions_by_matching:
  forall P N sigma,  matching P N sigma ->
                     forall M R, sf_red (App (extension P M R) N) (fold_left subst sigma M) .
Proof.
  intros. unfold extension. eapply succ_red. eapply2 s_red.
  eapply transitive_red. eapply preserves_app_sf_red. eapply2 case_by_matching. eval_tac. eval_tac.
Qed.


(* 
Lemma lift_rec_preserves_extension: 
  forall P M R n k, lift_rec (extension P M R) n k =
                    extension P (lift_rec M (pattern_size P +n) k) (lift_rec R n k).
Proof.
  intros. unfold extension. unfold_op. unfold lift_rec; fold lift_rec.
rewrite lift_rec_preserves_case. auto. 
Qed.


Lemma subst_rec_preserves_extension: 
  forall P M R N k, subst_rec (extension P M R) N k =
                    extension P (subst_rec M N (k+ pattern_size P)) (subst_rec R N k).
Proof.
  intros. unfold extension. unfold_op. unfold subst_rec; fold subst_rec.
rewrite subst_rec_preserves_case. auto. 
Qed.

 

Lemma maxvar_extension : 
forall P M R, maxvar (extension P M R) = max (maxvar M - (pattern_size P)) (maxvar R).
Proof.  intros. unfold extension; simpl. rewrite maxvar_case. auto. Qed. 

 *)

Lemma extension_ref: forall i M R N, sf_red (App (extension (Ref i) M R) N)  (subst_rec M N 0).
Proof.
  split_all. unfold extension. unfold_op.  eapply succ_red. eapply2 s_red.
  unfold case. unfold_op. eapply transitive_red. eapply preserves_app_sf_red.
  eapply2 star_opt_beta. eval_tac. unfold subst; split_all. eval_tac.
Qed. 

Lemma extension_op : forall o M R, sf_red (App (extension (Op o) M R) (Op o)) M.
Proof.
  intros. unfold extension, case; unfold_op.  
eapply succ_red. eapply2 s_red. 
case o. 
repeat eval_tac.   
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red.
 eapply preserves_app_sf_red.
eapply succ_red. eapply2 f_compound_red.  all: repeat eval_tac. 
Qed.



Lemma extension_op_fail : 
forall o M R N, factorable N -> Op o <> N -> sf_red (App (extension (Op o) M R) N) (App R N).
Proof.
  intros. unfold extension, case; unfold_op. eval_tac. 
  generalize H0; case o; intro. unfold subst; unfold_op; simpl.
  (* 2 *) 
  eval_tac. eval_tac. 
  inversion H. inversion H2; subst. 
  assert (x = Fop) . 
  gen_case H1 x; try discriminate. 
  assert False by eapply2 H1; noway. subst. do 21 eval_tac. 
  eapply2 preserves_app_sf_red. eval_tac. 
  eapply transitive_red. eapply preserves_app_sf_red. eapply succ_red. 
  eapply2 f_compound_red. do 12 eval_tac.
  eapply2 preserves_app_sf_red. do 11 eval_tac.
  eapply2 preserves_app_sf_red. do 11 eval_tac.
  (* 1 *) 
  eval_tac. eval_tac. 
  inversion H. inversion H2; subst. 
  assert (x = Sop) . 
  gen_case H1 x; try discriminate. 
  assert False by eapply2 H1; noway. subst. do 21 eval_tac.
  eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red.
  eapply preserves_app_sf_red. eapply succ_red. eapply2 f_compound_red. 
  1,2,3,4,5: eval_tac. do 6 eval_tac.   eapply2 preserves_app_sf_red. eval_tac. 
  eapply transitive_red. eapply preserves_app_sf_red. eapply succ_red. 
  eapply2 f_compound_red. do 12 eval_tac. eval_tac. 
  do 10 eval_tac.   eapply2 preserves_app_sf_red. eval_tac.
Qed. 

Lemma subst_rec_preserves_compound: 
forall (M: SF), compound M -> forall N k, compound(subst_rec M N k).
Proof. intros M c; induction c; unfold subst; split_all. Qed. 


Lemma swapred: forall N R, sf_red (App (swap N) R) (App R N). 
Proof.
intros; unfold swap; unfold_op. eval_tac. eval_tac. 
eapply2 preserves_app_sf_red. eval_tac. eval_tac. 
Qed. 



Lemma extension_compound_op: forall P1 P2 M R o, compound (App P1 P2) -> 
sf_red (App (extension (App P1 P2) M R) (Op o)) (App R (Op o)). 
Proof. 
  intros. unfold extension, case; fold case. 
assert(is_program (App P1 P2) = true \/ is_program(App P1 P2) <> true)
by decide equality. 
inversion H0. 
rewrite H1. 
do 4 eval_tac. 
eapply transitive_red.  eapply preserves_app_sf_red.  eapply preserves_app_sf_red.  eapply preserves_app_sf_red.
eapply transitive_red. eapply preserves_app_sf_red. 
auto. eval_tac. 
eapply2 unequal_op. 
eapply2 programs_are_factorable.  eapply2 program_is_program. discriminate.
eval_tac. eval_tac. eval_tac. do 7 eval_tac. 
eapply2 preserves_app_sf_red;  eval_tac.
(* 1 *) 
assert(is_program (App P1 P2) = false) by 
eapply2 not_true_iff_false. 
rewrite H2. 
do 14 eval_tac. eapply2 preserves_app_sf_red. eval_tac. 
Qed. 

(* 

Lemma extension_normal: forall P M  R,normal M -> normal R -> normal (extension P M R).
Proof.
  induction P; unfold extension; unfold_op; intros; 
  eapply2 nf_compound; eapply2 nf_compound; eapply2 case_normal. 
Qed. 



Lemma extension_pattern_normal: 
forall P M R j, pattern_normal (pattern_size P + j) M -> pattern_normal j R -> 
pattern_normal j (extension P M R).
Proof.
  induction P; unfold extension; unfold_op; intros; 
  eapply2 pnf_compound; eapply2 pnf_compound; try (eapply2 pnf_normal; fail); 
match goal with | |- pattern_normal ?j (case ?P _) => 
replace j with (pattern_size P + j - (pattern_size P)) by omega;  
eapply2 case_pattern_normal
end. 
Qed. 

*) 
 
Lemma active_not_closed: forall P, status P = Active -> maxvar P <>0. 
Proof.
intros. assert(maxvar P = 0 \/ maxvar P <> 0) by decide equality. 
inversion H0. assert(status P = Passive) by eapply2 closed_implies_passive. 
rewrite H in *. discriminate. 
auto. 
Qed. 
 
Inductive matchfail : SF -> SF -> Prop :=
| matchfail_op: forall o M, factorable M -> Op o <> M -> matchfail (Op o) M
| matchfail_compound_op: forall p1 p2 o, compound (App p1 p2) -> matchfail (App p1 p2) (Op o)
| matchfail_active_op: forall p1 p2 o, status (App p1 p2) = Active -> matchfail (App p1 p2) (Op o)
| matchfail_compound_l: forall p1 p2 M1 M2, compound (App p1 p2) -> compound (App M1 M2) ->
               matchfail p1 M1 -> matchfail (App p1 p2) (App M1 M2)
| matchfail_compound_r: forall p1 p2 M1 M2 sigma1, compound (App p1 p2) -> compound (App M1 M2) ->
               matching p1 M1 sigma1 -> matchfail p2 M2 -> matchfail (App p1 p2) (App M1 M2)
| matchfail_active_l: forall p1 p2 M1 M2, status(App p1 p2) = Active -> compound (App M1 M2) ->
               matchfail p1 M1 -> matchfail (App p1 p2) (App M1 M2)
| matchfail_active_r: forall p1 p2 M1 M2 sigma1, status (App p1 p2) = Active -> compound (App M1 M2) ->
               matching p1 M1 sigma1 -> matchfail p2 M2 -> matchfail (App p1 p2) (App M1 M2)
.

Hint Constructors matchfail. 


Lemma matchfail_lift: forall P M, matchfail P M -> forall k, matchfail P (lift k M).
Proof.
  induction P; split_all; inversion H; subst; unfold lift, lift_rec; fold lift_rec. 
(* 6 *) 
  gen2_case H1 H2 M. inversion H1; split_all. inversion H0. discriminate.  inv1 compound.
  eapply2 matchfail_op. unfold lift.  inversion H1; split_all. inversion H0; discriminate. 
 unfold factorable. right.
  replace (App (lift_rec s 0 k) (lift_rec s0 0 k)) with (lift_rec (App s s0) 0 k) by auto. 
  eapply2 lift_rec_preserves_compound. discriminate. 
(* 5 *) 
unfold lift; split_all. 
unfold lift; split_all. 
(* 4 *) 
eapply2 matchfail_compound_l.
replace (App (lift_rec M1 0 k) (lift_rec M2 0 k)) with (lift k (App M1 M2)) by auto.
unfold lift. eapply2 lift_rec_preserves_compound.
(* 3 *) 
eapply2 matchfail_compound_r.
replace (App (lift_rec M1 0 k) (lift_rec M2 0 k)) with (lift_rec (App M1 M2) 0 k) by auto. 
eapply2 lift_rec_preserves_compound.
eapply2 matching_lift. 
(* 2 *) 
apply matchfail_active_l. auto. 
replace (App (lift_rec M1 0 k) (lift_rec M2 0 k)) with (lift_rec (App M1 M2) 0 k) by auto. 
eapply2 lift_rec_preserves_compound.
eapply2 IHP1. 
(* 1 *) 
eapply matchfail_active_r. auto. 
replace (App (lift_rec M1 0 k) (lift_rec M2 0 k)) with (lift_rec (App M1 M2) 0 k) by auto. 
eapply2 lift_rec_preserves_compound.
eapply2 matching_lift. eapply2 IHP2. 
Qed.

Lemma matchfail_unequal : 
forall P M, maxvar P = 0 -> matchfail P M -> sf_red (App (App equal_comb M) P) (App k_op i_op). 
Proof. 
induction P; split_all. inversion H0; subst. 
inversion H0; split_all; subst; split_all. 
inversion H2. inversion H1; subst. eapply2 unequal_op.  unfold factorable; eauto. 
eapply2 unequal_compound_op. 
(* 1 *) 
inversion H0; subst. 
eapply2 unequal_op. unfold factorable; auto.  discriminate. 
assert(status (App P1 P2) = Passive). eapply2 closed_implies_passive. 
rewrite H1 in H4; discriminate. 
eapply transitive_red. eapply2 equal_compounds. simpl. 
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply2 IHP1. max_out. auto. auto. eval_tac.  eval_tac. eval_tac. 
assert(M1 = P1 /\ sigma1 = nil). eapply2 program_matching3. max_out. inversion H1; subst. 
eapply transitive_red. eapply2 equal_compounds. simpl. 
eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red. 
eapply2 equal_programs. eapply2 program_matching2. max_out. 
eapply2 IHP2. max_out. auto. eval_tac.
assert(status (App P1 P2) = Passive). eapply2 closed_implies_passive. 
rewrite H1 in H3; discriminate. 
assert(status (App P1 P2) = Passive). eapply2 closed_implies_passive. 
rewrite H1 in H3; discriminate. 
Qed. 


Lemma case_by_matchfail:
  forall P N R,  matchfail P N  -> forall M, sf_red (App (App (case P M) N) R) (App R N). 
Proof.
  induction P; intros; inversion H; subst.
  (* 7 *)
  unfold case, maxvar; unfold_op. 
  gen_case H2 o. eval_tac. eval_tac. 
  inversion H1. inversion H0; subst. 
  assert(x = Fop). gen_case H2 x.  assert False by eapply2 H2; noway. subst.
  do 20 eval_tac.  eapply2 preserves_app_sf_red.  eval_tac. 
  (* 8 *) 
  eapply transitive_red. eapply preserves_app_sf_red.  eapply succ_red. 
  eapply2 f_compound_red. repeat eval_tac. auto. do 10 eval_tac.
  eapply2 preserves_app_sf_red.  eval_tac. 
  (* 7 *)
  unfold subst; unfold_op; simpl; eval_tac. eval_tac. 
  inversion H1. inversion H0; subst. 
  assert(x = Sop). gen_case H2 x.  assert False by eapply2 H2; noway. subst.
  do 20 eval_tac.  
  (* 8 *) 
  eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red.  eapply succ_red. 
  eapply2 f_compound_red. repeat eval_tac. repeat eval_tac. eval_tac. auto. do 7 eval_tac.
  eapply2 preserves_app_sf_red.  eval_tac. 
  eapply transitive_red. eapply preserves_app_sf_red.  eapply succ_red. 
  eapply2 f_compound_red. repeat eval_tac. auto. do 10 eval_tac.
  eapply2 preserves_app_sf_red.  eval_tac. 
  (* 6 *) 
  unfold case; fold case.
assert(is_program (App P1 P2) = true \/ is_program(App P1 P2) <> true)
by decide equality. 
inversion H0. 
rewrite H1. 
assert(program (App P1 P2)) by eapply2 program_is_program.
eval_tac. eval_tac. eval_tac. 
  eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red.  eapply transitive_red. eapply preserves_app_sf_red. auto. eval_tac. 
eapply2 unequal_op. 
eapply2 programs_are_factorable.  discriminate. eval_tac. eval_tac. auto.
do 7 eval_tac. 
eapply2 preserves_app_sf_red;  eval_tac.
(* 6 *) 
assert(is_program (App P1 P2) = false) by 
eapply2 not_true_iff_false. 
rewrite H2. 
unfold case_app_nf.  do 12 eval_tac.  eapply2 preserves_app_sf_red. eval_tac. 
(* 5 *) 
  unfold case; fold case.
assert(is_program (App P1 P2) = true \/ is_program(App P1 P2) <> true)
by decide equality. 
inversion H0. 
rewrite H1. 
assert(program (App P1 P2)) by eapply2 program_is_program. 
do 3 eval_tac. 
eapply transitive_red.  eapply preserves_app_sf_red.  eapply preserves_app_sf_red.
eapply preserves_app_sf_red.
eapply transitive_red. eapply preserves_app_sf_red. auto.  eval_tac. 
eapply2 unequal_op. 
eapply2 programs_are_factorable.  discriminate. eval_tac. eval_tac. auto.
do 7 eval_tac. 
eapply2 preserves_app_sf_red;  eval_tac.
(* 5 *) 
assert(is_program (App P1 P2) = false) by 
eapply2 not_true_iff_false. 
rewrite H2. 
unfold case_app_nf.  do 12 eval_tac.
eapply2 preserves_app_sf_red. eval_tac. 
(* 4 *) 
  unfold case; fold case.
assert(is_program (App P1 P2) = true \/ is_program(App P1 P2) <> true)
by decide equality. 
inversion H0. 
rewrite H1. 
assert(program (App P1 P2)) by eapply2 program_is_program. 
do 3 eval_tac. 
eapply transitive_red.  eapply preserves_app_sf_red.  eapply preserves_app_sf_red.
eapply preserves_app_sf_red.
eapply transitive_red. eapply preserves_app_sf_red. auto.  eval_tac. 
eapply2 equal_compounds. eval_tac. eval_tac. auto. simpl. 
eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red. 
eapply preserves_app_sf_red.  eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply2 matchfail_unequal. inversion H4.  simpl in H7; max_out. auto. auto. auto. eval_tac. auto. 
do 9 eval_tac. 
eapply2 preserves_app_sf_red; eval_tac. 
assert(is_program (App P1 P2) = false) by 
eapply2 not_true_iff_false. 
rewrite H4. 
  unfold case_app_nf. do 3 eval_tac.  
  eapply transitive_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. eapply succ_red. 
eapply2  f_compound_red. eval_tac. eval_tac.  auto.  do 5 eval_tac. 
 eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red. 
eapply preserves_app_sf_red.  eapply preserves_app_sf_red. 
eapply2 IHP1. auto. eval_tac. eval_tac. auto. 
do 9 eval_tac.  eapply2 preserves_app_sf_red.  eval_tac. 
(* 3 *) 
  unfold case; fold case.
assert(is_program (App P1 P2) = true \/ is_program(App P1 P2) <> true)
by decide equality. 
inversion H0. 
rewrite H1. 
assert(program (App P1 P2)) by eapply2 program_is_program.
do 3 eval_tac. 
eapply transitive_red.  eapply preserves_app_sf_red.
eapply preserves_app_sf_red.  eapply preserves_app_sf_red.
eapply transitive_red. eapply preserves_app_sf_red. auto.  eval_tac. 
eapply2 equal_compounds. eval_tac. eval_tac. auto. simpl. 
eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red. 
eapply preserves_app_sf_red.  eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
assert(M1 = P1 /\ sigma1 = nil). eapply2 program_matching3. 
inversion H5; simpl in *; max_out. inversion H7; subst. 
eapply2 equal_programs.
eapply2 (program_app P1 P2).  auto. auto. auto. eval_tac. auto. eval_tac. 
eapply transitive_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
eapply2 matchfail_unequal. inversion H5; simpl in *; max_out. 
auto. auto. auto.  do 6 eval_tac. 
eapply2 preserves_app_sf_red; eval_tac. 
(* 3 *) 
assert(is_program (App P1 P2) = false) by 
eapply2 not_true_iff_false. 
rewrite H5. 
 unfold case_app_nf. do 3 eval_tac.  
  eapply transitive_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. eapply succ_red. 
eapply2  f_compound_red. eval_tac. eval_tac.  auto.  do 5 eval_tac. 
 eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red. 
eapply preserves_app_sf_red.  eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. eapply2 case_by_matching.  eval_tac. auto. eval_tac. eval_tac. auto.  
eval_tac. 
rewrite fold_subst_list.
rewrite fold_subst_list.
rewrite fold_subst_list.
rewrite fold_subst_list.
eapply transitive_red. eapply list_subst_preserves_sf_red. 
eapply preserves_app_sf_red. eapply preserves_app_sf_red.
eapply IHP2. eapply2 matchfail_lift. 
unfold lift; simpl. auto. unfold lift; simpl. auto. 
eapply transitive_red. eapply list_subst_preserves_sf_red. unfold lift; simpl.  eval_tac.
eapply transitive_red. eapply list_subst_preserves_sf_red.
do 6 (eapply transitive_red; [eval_tac|]). auto. 
repeat rewrite list_subst_preserves_app. repeat rewrite list_subst_preserves_op.
 eapply transitive_red. eapply preserves_app_sf_red. auto. eval_tac. 
replace(lift_rec M1 0 (length sigma1)) with (lift (length sigma1) M1) by auto. 
replace(lift_rec M2 0 (length sigma1)) with (lift (length sigma1) M2) by auto.
eapply2 preserves_app_sf_red. 
replace (lift_rec R 0 (length sigma1)) with (lift (length sigma1) R) by auto. 
 rewrite list_subst_lift; auto.  rewrite ! list_subst_lift; auto. 
 (* 2 *) 
  unfold case; fold case.
assert(is_program (App P1 P2) = true \/ is_program(App P1 P2) <> true)
by decide equality. 
inversion H0. 
assert(status(App P1 P2) = Passive) . eapply2 closed_implies_passive.
assert(program (App P1 P2)) by eapply2 program_is_program. 
inversion H4; auto. rewrite H4 in H2. discriminate.
assert(is_program (App P1 P2) = false) by eapply2 not_true_iff_false. 
rewrite H4. 
 unfold case_app_nf. do 3 eval_tac.  
  eapply transitive_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. eapply succ_red. 
eapply2  f_compound_red. eval_tac. eval_tac.  auto.  do 5 eval_tac. 
 eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red. 
eapply preserves_app_sf_red.  eapply preserves_app_sf_red. eapply transitive_red. 
eapply2 IHP1. eval_tac. auto. eval_tac. eval_tac. auto. do 8 eval_tac. 
eapply2 preserves_app_sf_red.  eval_tac. 
(* 1 *) 
   unfold case; fold case.
assert(is_program (App P1 P2) = true \/ is_program(App P1 P2) <> true)
by decide equality. 
inversion H0. 
assert(status(App P1 P2) = Passive) . eapply2 closed_implies_passive.
assert(program (App P1 P2)) by eapply2 program_is_program. 
inversion H5; auto. rewrite H5 in H2. discriminate.
assert(is_program (App P1 P2) = false) by eapply2 not_true_iff_false. 
rewrite H5. 
 unfold case_app_nf. do 3 eval_tac.  
  eapply transitive_red. eapply preserves_app_sf_red. 
eapply preserves_app_sf_red. eapply succ_red. 
eapply2  f_compound_red. eval_tac. eval_tac.  auto.  do 5 eval_tac. 
 eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red. 
 eapply preserves_app_sf_red.  eapply preserves_app_sf_red. eapply preserves_app_sf_red. 
 eapply2 case_by_matching.  eval_tac. auto. eval_tac. eval_tac. auto.  eval_tac. 
rewrite fold_subst_list.
rewrite fold_subst_list.
rewrite fold_subst_list.
rewrite fold_subst_list.
eapply transitive_red. eapply list_subst_preserves_sf_red. 
eapply preserves_app_sf_red. eapply preserves_app_sf_red.
eapply IHP2. eapply2 matchfail_lift. 
unfold lift; simpl. auto. unfold lift; simpl. auto.  unfold lift; simpl. 
eapply transitive_red. eapply list_subst_preserves_sf_red.
eapply transitive_red; [eval_tac|].
eapply transitive_red; [eval_tac|].
eapply transitive_red; [eval_tac|].
eapply transitive_red; [eval_tac|].
eapply transitive_red; [eval_tac|].
eapply transitive_red; [eval_tac|].
eapply transitive_red; [eval_tac|].
eapply transitive_red; eapply preserves_app_sf_red. auto. eval_tac. auto. auto. 
repeat rewrite list_subst_preserves_app.  
replace(lift_rec M1 0 (length sigma1)) with (lift (length sigma1) M1) by auto. 
replace(lift_rec M2 0 (length sigma1)) with (lift (length sigma1) M2) by auto.
replace (lift_rec R 0 (length sigma1)) with (lift (length sigma1) R) by auto. 
 rewrite ! list_subst_lift; auto.  
Qed. 



Proposition extensions_by_matchfail:
  forall P N,  matchfail P N -> forall M R, sf_red (App (extension P M R) N) (App R N).
Proof.
  intros. unfold extension. eval_tac. 
  eapply transitive_red. eapply2 case_by_matchfail.  
  eapply transitive_red. eapply preserves_app_sf_red. eapply succ_red. eapply2 f_op_red. auto. 
auto. auto. 
Qed. 

Lemma match_program: 
forall P M, normal P -> program M -> matchfail P M \/ exists sigma, matching P M sigma.
Proof. 
induction P; split_all. 
(* 3 *) 
right. exist (cons M nil). 
(* 2 *) 
gen_case H0 M. inversion H0; split_all.  simpl in *; discriminate. 
case o; case o0; split_all. 
right; eauto. 
left; auto; eapply2 matchfail_op. unfold factorable; left; eauto.  discriminate.  
left; auto; eapply2 matchfail_op. unfold factorable; left; eauto.  discriminate.  
right; eauto. 
left; auto; eapply2 matchfail_op.  eapply2 programs_are_factorable.  discriminate. 
(* 1 *) 
gen_case H0 M; inversion H0; auto. 
(* 2 *) 
simpl in *; discriminate. 
(* 2 *) 
inversion H; subst; left; auto. 
(* 1 *) 
inversion H; subst. inversion H1; subst.
(* 3 *)  
assert(status (App s s0) = Passive) by eapply2 closed_implies_passive. 
rewrite H3 in H10; discriminate. 
(* 2 *) 
simpl in H2; max_out. 
assert(matchfail P1 s \/ (exists sigma : list SF, matching P1 s sigma)).
eapply2 IHP1. unfold program; split_all. 
assert(matchfail P2 s0 \/ (exists sigma : list SF, matching P2 s0 sigma)). 
eapply2 IHP2. unfold program; split_all. 
(* 2 *) 
inversion H2. left; eapply2 matchfail_active_l.
inversion H11. 
inversion H12. left; eapply2 matchfail_active_r.
inversion H12; inversion H13. 
right; exist (map (lift (length x)) x0++x). 
(* 1 *) 
inversion H1; subst.
(* 3 *)  
assert(status (App s s0) = Passive) by eapply2 closed_implies_passive. 
rewrite H3 in H10; discriminate. 
(* 1 *) 
simpl in H2; max_out. 
assert(matchfail P1 s \/ (exists sigma : list SF, matching P1 s sigma)).
eapply2 IHP1. unfold program; split_all. 
assert(matchfail P2 s0 \/ (exists sigma : list SF, matching P2 s0 sigma)). 
eapply2 IHP2. unfold program; split_all. 
(* 2 *) 
inversion H2. left; eapply2 matchfail_compound_l. 
inversion H11; inversion H12; subst. left; eapply2 matchfail_compound_r. 
inversion H13; subst. right; eauto.
Qed. 

