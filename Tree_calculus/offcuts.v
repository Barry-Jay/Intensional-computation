


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

  


Lemma maxvar_occurs: forall M, maxvar M = 1 -> occurs 0 M >0. 
Proof.
induction M; split_all.
gen_case H n.  omega.
assert(maxvar M1 = 1 \/ maxvar M2 = 1). 
gen_case H (maxvar M1).
gen_case H (maxvar M2).
assert (max n n0 >= n) by eapply2 max_is_max.
left; omega. 
inversion H0. 
assert(occurs 0 M1 >0) by eapply2 IHM1. omega. 
assert(occurs 0 M2 >0) by eapply2 IHM2. omega. 
Qed.  


(*
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
(* 
Lemma aux :
  forall M N, occurs 0 M >0 -> maxvar N = 0 -> S (size(subst M N)) >= size M + size N.
Proof.
  induction M; split_all.
  gen_case H n. unfold subst; simpl. insert_Ref_out.
  unfold lift; rewrite lift_rec_null. omega. omega. omega. 
  assert(occurs 0 M1 >0 \/ occurs 0 M2 >0) by omega.
  inversion H1.
  assert(S(size (subst M1 N)) >= size M1 + size N) by eapply2 IHM1.   
  unfold subst in *.
assert(size (subst_rec M2 N 0) >= size M2). apply size_subst. ga.   
*) 


(* restore ? 
Lemma star_bigger: 
forall M, maxvar M = 0 -> 
star_opt
  (star_opt
     (App (Ref 0)
        (app_comb (app_comb (app_comb M (Ref 1)) (Ref 1)) (Ref 0)))) <>
M. 
Proof.
  intros. 
  replace (star_opt (star_opt (App (Ref 0) (app_comb (app_comb (app_comb M (Ref 1)) (Ref 1)) (Ref 0)))))
  with
    (subst (star_opt (star_opt (App (Ref 0) (app_comb (app_comb (app_comb (Ref 2) (Ref 1)) (Ref 1)) (Ref 0))))) M) .
  intro. 
elim(size_subst_star_opt (star_opt
               (App (Ref 0)
                  (app_comb (app_comb (app_comb (Ref 2) (Ref 1)) (Ref 1)) (Ref 0)))) M); intros; auto. 

  unfold app_comb, star_opt; unfold_op; unfold occurs, eqnat; simpl. 
intro.
omega. intro.


  
intros. 
rewrite star_opt_occurs_true. 
2: cbv. 2: omega.
2: discriminate . 
unfold star_opt at 3.
unfold app_comb.
rewrite  (star_opt_occurs_true (App (Op Node) (App (Op Node) i_op))). 
2: unfold app_comb; simpl; auto. 2: omega. 
2: discriminate . 
 rewrite  (star_opt_occurs_true (App (Op Node) (App (Op Node) (App k_op (Ref 0))))). 
2: unfold app_comb; simpl; auto. 2: omega. 
2: discriminate .
rewrite (star_opt_occurs_false (App k_op _)). 
2: simpl; auto. 2: eapply2 occurs_closed; auto.
subst_tac.
rewrite subst_rec_closed. 2: omega. 
rewrite star_opt_occurs_true. 
2: simpl; auto. 2: omega. 2: discriminate.
rewrite star_opt_closed. 2: cbv; omega.
rewrite star_opt_occurs_true.
2: unfold app_comb; simpl; auto. 2: omega. 
2: discriminate .
rewrite star_opt_occurs_true.
2: unfold app_comb; simpl; auto.
2: discriminate .
rewrite star_opt_occurs_true.
2: unfold app_comb; simpl; auto.
2: discriminate .
rewrite star_opt_closed.
2: cbv; auto. 
rewrite star_opt_occurs_true.
2: unfold app_comb; simpl; auto.
2: discriminate .
rewrite star_opt_occurs_true.
2: unfold app_comb; simpl; auto.
2: discriminate .
rewrite star_opt_occurs_true.
2: unfold app_comb; simpl; auto.
2: discriminate .
rewrite star_opt_closed.
2: cbv; auto. 
rewrite star_opt_occurs_true.
2: unfold app_comb; simpl; auto.
2: discriminate .
rewrite star_opt_occurs_true.
2: unfold app_comb; simpl; auto.
2: discriminate .
rewrite star_opt_occurs_true.
2: unfold app_comb; simpl; auto.
2: discriminate .
rewrite star_opt_occurs_true.
2: unfold app_comb; simpl; auto.
2: discriminate .
rewrite star_opt_occurs_true.
2: unfold app_comb; simpl; auto.
2: discriminate .
rewrite star_opt_occurs_true.
2: unfold app_comb; simpl; auto.
2: discriminate .
rewrite star_opt_occurs_true.
2: unfold app_comb; simpl; auto.
2: discriminate .
rewrite star_opt_occurs_true.
2: unfold app_comb; simpl; auto.
2: discriminate .
rewrite star_opt_occurs_true.
2: unfold app_comb; simpl; auto.
2: discriminate .
rewrite star_opt_closed.
2: cbv; auto. 
intro. clear H.  
match goal with 
| H: ?M = ?N |- _ => assert(size M = size N) by congruence 
end.
clear H0.
generalize H. clear H. unfold_op; unfold star_opt, occurs, size; fold size.
rewrite ! orb_false_l. 
unfold_op; unfold subst, subst_rec, size; fold size. 
intro; omega.
Qed. 
 *)

(* 
Lemma star_opt_app_comb2:
  forall M N, maxvar M = 0 -> occurs 0 N = true -> occurs 1 N = true -> 
              star_opt (star_opt (app_comb M  N)) = k_op.
Proof.
  intros.
  rewrite star_opt_app_comb1; auto.   
  rewrite star_opt_occurs_true. 
  2: simpl; rewrite H0; auto.
  2: rewrite ! orb_false_r.
  2: replace (match N with
      | Ref 0 => subst k_op (Op Node)
      | _ =>
          App (App (Op Node) (App (Op Node) (star_opt N)))
            (App k_op (subst (App node node) (Op Node)))
      end)
    with (App (App (Op Node) (App (Op Node) (star_opt N)))
              (App k_op (subst (App node node) (Op Node)))).
  all: cycle 1.
  simpl. 
  rewrite occurs_star_opt.
  rewrite H1; auto. simpl. 
  rewrite orb_true_r.   auto.
  2: discriminate.
  gen2_case H0 H1 N.
  assert False.
  gen2_case H0 H1 n; discriminate. omega. 
  (* 1 *)
  assert (match N with
      | Ref 0 => subst k_op (Op Node)
      | _ =>
          App (App (Op Node) (App (Op Node) (star_opt N)))
            (App k_op (subst (App node node) (Op Node)))
          end =
          App (App (Op Node) (App (Op Node) (star_opt N)))
              (App k_op (subst (App node node) (Op Node)))).
  gen2_case H0 H1 N.
  assert False.
  gen2_case H0 H1 n; discriminate. omega. 
  rewrite star_opt_closed. 
  2: cbv; auto.
  rewrite star_opt_occurs_true. 
  2: simpl; rewrite H0; auto.
  2: rewrite ! orb_false_r.
  2: rewrite H2.  
  2: simpl; auto. 
  all: cycle 1.
rewrite occurs_star_opt.   
rewrite H1.   simpl. rewrite orb_true_r. auto.
discriminate.
  rewrite star_opt_occurs_true. 
  2: simpl; rewrite H0; auto.
  2: rewrite ! orb_false_r.
  2: rewrite H2.  
  2: simpl; auto. 
  all: cycle 1.
rewrite occurs_star_opt.   
rewrite H1.   simpl. rewrite orb_true_r. auto.
discriminate.
  rewrite star_opt_occurs_true. 
  2: simpl; rewrite H0; auto.
  2: rewrite ! orb_false_r.
  2: rewrite H2.  
  2: simpl; auto. 
  all: cycle 1.
rewrite occurs_star_opt.   
rewrite H1.   simpl. rewrite orb_true_r. auto.
discriminate.
  rewrite star_opt_occurs_true. 
  2: simpl; rewrite H0; auto.
  2: rewrite ! orb_false_r.
  2: rewrite H2.  
  2: simpl; auto. 
  all: cycle 1.
rewrite occurs_star_opt.   
rewrite H1. auto.    
discriminate.
rewrite star_opt_closed. 
2: cbv; auto.
rewrite star_opt_occurs_true.
2: rewrite ! occurs_app. 
2: rewrite ! occurs_op.
2: rewrite occurs_star_opt. 
2: rewrite ! occurs_app. 2: rewrite H1. 2: cbv; auto. 2: discriminate.
rewrite star_opt_occurs_true.
2: rewrite ! occurs_app. 
2: rewrite ! occurs_op.
2: rewrite occurs_star_opt. 
2: rewrite ! occurs_app. 2: rewrite H1. 2: cbv; auto. 2: discriminate.



simpl2: rewrite H2. cbv; auto. 2: discriminate. 
  2: simpl; rewrite H0; auto.
  2: rewrite ! orb_false_r.
  2: rewrite H2.  
  2: simpl; auto. 
  all: cycle 1.
rewrite occurs_star_opt.   
rewrite H1.   simpl. rewrite orb_true_r. auto.
discriminate.
  rewrite star_opt_occurs_true. 
  2: simpl; rewrite H0; auto.
  2: rewrite ! orb_false_r.
  2: rewrite H2.  
  2: simpl; auto. 
  all: cycle 1.
rewrite occurs_star_opt.   
rewrite H1.   simpl. rewrite orb_true_r. auto.
discriminate.
  rewrite star_opt_occurs_true. 
  2: simpl; rewrite H0; auto.
  2: rewrite ! orb_false_r.
  2: rewrite H2.  
  2: simpl; auto. 
  all: cycle 1.
rewrite occurs_star_opt.   
rewrite H1.   simpl. rewrite orb_true_r. auto.
discriminate.



assert False.
  gen2_case H0 H1 n; discriminate. omega. 


  2: rewrite ! orb_false_r.



  all: try discriminate.
  rewrite H0.  rewrite occurs_closed. simpl. 
  unfold eqnat in *.

  2: congruence. 
  rewrite star_opt_occurs_true. 
  2: simpl; rewrite H0; auto. 2: congruence. 
  rewrite star_opt_closed. 
  2: cbv; auto.
  rewrite star_opt_occurs_true. 
  2: simpl; rewrite H0; auto. 2: congruence. 
  rewrite star_opt_occurs_true. 
  2: simpl; rewrite H0; auto. 2: congruence. 
  rewrite (star_opt_closed  (App (Op Node) (App (Op Node) i_op))).
  2: cbv; auto.
  rewrite ! (star_opt_closed (Op Node)).
  2: cbv; auto. auto. 
Qed.


(* 

  Lemma star_opt_app_comb:
  forall M1 N1 M2 N2, maxvar M1 = 0 -> maxvar M2 = 0 -> occurs 0 N1 = occurs 0 N2 ->
                      star_opt (app_comb M1 N1) = star_opt (app_comb M2 N2) ->
                      M1 = M2 /\ star_opt N1 = star_opt N2.
Proof.
  intros.
  assert (occurs 0 N1 = false \/ occurs 0 N1 <> false) by decide equality.  
  inversion H3.
  (* 2 *) 
rewrite ! star_opt_occurs_false in *. 
inversion H2. split.  rewrite ! subst_rec_closed in H7. auto. omega. omega. congruence. 
unfold app_comb; simpl.   rewrite H4 in *. rewrite <- H1. rewrite occurs_closed.
auto. auto. congruence.
unfold app_comb; simpl.   rewrite H4 in *. rewrite occurs_closed.
auto. auto. congruence.
(* 1 *)
generalize H2; clear H2.  unfold app_comb. 
  rewrite star_opt_occurs_true at 1.   
  rewrite star_opt_occurs_true at 1.   
  2: unfold_op; simpl.
  2: gen_case H4 (occurs 0 N1). 2: congruence. 2: unfold_op; simpl.
  2: gen_case H4 (occurs 0 N1). 2: congruence. 
  rewrite star_opt_closed at 1. 2: simpl; auto. 
  rewrite star_opt_occurs_true at 1.   
  2: unfold_op; simpl.
  2: gen_case H4 (occurs 0 N1). 2: congruence.
  rewrite star_opt_occurs_true at 1.   
  2: unfold_op; simpl.
  2: gen_case H4 (occurs 0 N1). 2: congruence.
  unfold star_opt at 2 3.
  rewrite (star_opt_closed (App (Op Node) _)). 
  2: cbv; auto.

  intro. 
assert(star_opt
         (App (App (Op Node) (App (Op Node) i_op))
              (App (App (Op Node) (App (Op Node) (App k_op N2))) (App k_op M2))) =
        App
         (App (Op Node)
            (App (Op Node)
               (App (App (Op Node) (App (Op Node) (App k_op (App k_op M1))))
                  (App
                     (App (Op Node)
                        (App (Op Node)
                           (App (App (Op Node) (App (Op Node) (star_opt (App k_op N1))))
                              (App k_op (Op Node))))) (App k_op (Op Node))))))
         (App k_op (App (Op Node) (App (Op Node) i_op))) )
     by auto.   
generalize H5; clear H2 H5.
assert(occurs 0 N2 = true). gen2_case H4 H1 (occurs 0 N1). 
rewrite star_opt_occurs_true at 1.   
  rewrite star_opt_occurs_true at 1.   
  2: unfold_op; simpl.
  2:  rewrite H2; auto. 2:congruence. 2: unfold_op; simpl.
  2: rewrite H2; auto. 2: congruence. 
  rewrite star_opt_closed at 1. 2: simpl; auto. 
  rewrite star_opt_occurs_true at 1.   
  2: unfold_op; simpl.
  2: auto.  2: congruence.
  rewrite star_opt_occurs_true at 1.   
  2: unfold_op; simpl.
  2: auto. 2: congruence.
  unfold star_opt at 2 3.
  rewrite (star_opt_closed (App (Op Node) _)). 
  2: cbv; auto.

  intro. inversion H5; subst.
  rewrite H2 in *.
  assert(occurs 0 N1 = true) by (gen_case H4 (occurs 0 N1)). 
  rewrite H6 in *. 
  split; auto. 
  clear - H2 H6 H8.
  gen2_case H2 H8 N2. 
  gen2_case H2 H8 n.
  gen2_case H6 H8 N1. 
  gen2_case H6 H8 n0.
  all: try discriminate.   
  gen2_case H6 H8 N1. 
  gen2_case H6 H8 n.
  gen2_case H2 H8 (occurs 0 t).
all: try (inversion H8; fail).   
all: try discriminate. 
inversion H8; subst. auto. 
Qed.
 *) 
 *)
