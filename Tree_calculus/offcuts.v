
Lemma Y4_aux : forall M N P, sf_red (App (App (app_comb (Y_k 4) M) N) P) 
(app_comb (app_comb (app_comb (app_comb (omega_k 4) (omega_k 4)) M) N) P).
Proof. 
intros.  
eapply transitive_red. eapply preserves_app_sf_red.
eapply2 app_comb_red. auto.
unfold Y_k; fold Y_k.     
eapply transitive_red. eapply preserves_app_sf_red.  eapply preserves_app_sf_red.
eapply2 app_comb_red. all: auto.
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red.
eapply preserves_app_sf_red.
eapply2 app_comb_red. all: auto.
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red.
eapply preserves_app_sf_red.
eapply2 A3_red. all: auto.
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red.
eapply2 app_comb_red. all: auto.
eapply transitive_red. eapply preserves_app_sf_red. eapply preserves_app_sf_red.
eapply2 A3_red. all: auto.
eapply transitive_red. eapply preserves_app_sf_red. 
eapply2 app_comb_red. all: auto.
eapply transitive_red. eapply preserves_app_sf_red. 
eapply2 A3_red. all: auto.
eapply transitive_red. 
eapply2 app_comb_red.
unfold A_k. 
eapply2 a_op2_red.  
Qed. 
    
Lemma star_opt_preserves_bind_normal: forall M, bind_normal M -> bind_normal (multi_star (maxvar M) M). 
star_opt M).
Proof.
intros. inversion H; subst. 
(* 2 *) 
eapply2 bn_normal. 
eapply2 star_opt_normal.
(* 1 *) 
simpl in *.  
induction M; split_all. 
case n; unfold_op; auto. repeat eapply2 bn_app. 
all: try (intro; inversion H0; fail).
split_all. repeat eapply2 bn_app.  
all: try (intro; inversion H0; fail).
unfold_op. repeat eapply2 bn_app.  
all: try (intro; inversion H0; fail).
(* 1 *) 
inversion H; subst.

Lemma aux: forall M, bind_normal M -> occurs0 M = false -> bind_normal (subst M (Op Node)).
Proof.
induction M; split_all.
gen_case H0 n. cbv . auto. 
assert(occurs0 M1 = false). gen_case H0 (occurs0 M1). 
assert(occurs0 M2 = false). gen_case H0 (occurs0 M2). rewrite orb_true_r in H0. discriminate.  
inversion H. subst. 
replace (subst (App M1 M2) (Op Node)) with (App (subst M1 (Op Node)) (subst M2 (Op Node))).
eapply2 bn_app.
intro. simpl.  unfold subst.

assert(ready M1). generalize H1 H3; clear. induction M1.
(* 5 *)  
cbv; split_all. gen_case H3 n;  inversion H3. 
(* 4 *) 
cbv; intros. inversion H3.
(* 3 *) 
intros. unfold subst in *; simpl in *.  inversion H3; subst. 
gen2_case H1 H M1_1. 
gen2_case H1 H n. discriminate.  
unfold insert_Ref in H. simpl in H. discriminate. discriminate. 
inversion H; subst. 
gen_case H4 t; try discriminate. 
unfold insert_Ref in H4. 
gen_case H4 n. 



occurs problem!


 discriminate. discriminate. 
inversion H; subst. 
gen_case H4 t; try discriminate. 
 
   
split_all. 
simpl in *. 

Lemma aux2:   rewrite maxvar_subst_rec. 
 eapply2 IHM1.   


 
case (occurs0 M1). 
(* 2 *) 
repeat eapply2 bn_app.
all: try (intro R; inversion R; fail).
(* 1 *) 
gen2_case IHM2 H3 M2.
gen2_case IHM2 H3 n.
 

case M2; split_all. 
all: cycle 2. 
case (occurs0 t); case (occurs0 t0); simpl. 


gen_case H3 M2 is needed above. 
  




Fixpoint multi_star n M := 
match n with 
| 0 => M 
| S k => multi_star k (star_opt M)
end .

Lemma multi_star_plus: forall m n M, multi_star (m+n) M = multi_star m (multi_star n M).
Proof.
induction m; split_all. 
rewrite IHm. 
cut(multi_star n (star_opt M) = star_opt (multi_star n M)); auto. congruence . 
generalize M; clear.  induction n; split_all.
Qed. 
 


Lemma multi_star_normal0 : forall n M, normal M -> normal (multi_star n M).
Proof.  induction n; split_all. eapply2 IHn. eapply2 star_opt_normal. Qed. 




eapply2 multi_star_normal0. unfold_op; auto.


assert(maxvar (App M1 M2) = 0 \/ maxvar (App M1 M2) <> 0) by decide equality .
inversion H0. 
simpl in *; max_out. rewrite H5 in *; rewrite H6 in *. simpl. 
assert(normal (App M1 M2) \/ ready M1). 
eapply2 ready_or_not. 
eapply2  bind_normal_0_is_program. 
eapply2  bind_normal_0_is_program. 
inversion H1; auto. simpl ; auto. 
rewrite H5; rewrite H6; auto.  
simpl ; auto. 
rewrite H5; rewrite H6; auto.  
(* 1 *) 
simpl in *. 
replace (


subst.  
 
clear; induction n0; split_all. 
  
inversion H; split_all. 




Inductive ready : Tree -> Prop := 
| is_ready : forall M N, factorable M -> ready (App (App (Op Node) M) N)
.

Hint Constructors ready. 

Lemma ready_or_not: forall M N, program M -> normal N -> normal (App M N) \/ ready M.
Proof.
intros. inversion H; subst. inversion H1; subst.  
(* 4 *) 
left. eapply2 nf_active.
left. eapply nf_compound. 
case o; auto. 
auto. 
case o; auto.
assert(status (App M1 M2) = Passive) by eapply2 closed_implies_passive. 
rewrite H6 in H5; discriminate. 
(* 1 *)  
inversion H5; subst; auto.
right. simpl in *. max_out. 
inversion H3; subst.
assert(status(App (Op Node) M) = Passive) by eapply2 closed_implies_passive. 
rewrite H2 in H11; discriminate . 
assert(factorable M).
 eapply2 programs_are_factorable.
split; auto. 
inversion H2. 
inversion H8; subst; auto.
inversion H8; subst; auto.
Qed. 


Lemma subst_rec_preserves_ready: forall M N k, ready M -> ready (subst_rec M N k).
Proof.
intros. inversion H; subst. simpl. eapply2 is_ready. 
inversion H0; subst. 
inversion H1; subst. simpl; auto. 
unfold factorable. right. 
inversion H1; subst; cbv; auto. 
Qed.



Inductive bind_normal : Tree -> Prop := 
| bn_leaf : bind_normal (Op Node) 
| bn_ref : forall i, bind_normal (Ref i) 
| bn_app : forall M N, bind_normal M -> bind_normal N -> (ready M -> maxvar (App M N) > 0) -> bind_normal (App M N)
.

Hint Constructors bind_normal. 

Lemma bind_normal_0_is_program : forall M, bind_normal M -> maxvar M = 0 -> program M.
Proof.
induction M; split_all; inversion H; subst; unfold program; auto. split. 
all: cycle 1. 
max_out. simpl; auto. rewrite H1; rewrite H2; auto. 
(* 1 *) 
max_out.
assert(program M1) by auto. 
assert(program M2) by auto.
inversion H0; subst. 
inversion H6; subst.
assert(normal (App M1 M2) \/ ready M1) by eapply2 ready_or_not. 
inversion H11; auto. 
assert(maxvar (App M1 M2) >0) by eapply2 H5. simpl in *. 
rewrite H1 in *; rewrite H2 in *. simpl in *; omega.
Qed. 
  