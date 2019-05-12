
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
