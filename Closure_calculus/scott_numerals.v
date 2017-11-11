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
(*                        scott_numerals                              *)
(*                                                                    *)
(*                          Barry Jay                                 *)
(*                                                                    *)
(**********************************************************************)

Add LoadPath ".." as IntensionalLib. 

Require Import List Omega IntensionalLib.Closure_calculus.Closure_calculus.


(* primitive recursion 
      https://en.wikipedia.org/wiki/Lambda_calculus#Arithmetic_in_lambda_calculus
 *)


(* 
Scott numerals specialize the general account of algebraic data types to natural numbers. 
The number n takes two arguments, x and f. 
If n is zero then return x, 
else if n is the successor of n1 then return f n1. 


*) 

Definition zero:= tt. (* \xf. x *) 
Definition succ := Abs Iop 2 (Abs (Add Iop 2 (Ref 2)) 1 
                    (Abs (Add (Add Iop 1 (Ref 1)) 2 (Ref 2)) 0 
                    (Tag (Ref 0) (Ref 2)))). (* \nxf.fn *) 
Fixpoint scott n :=
  match n with
    | 0 => tt
    | S n => Abs (Add Iop 2 (scott n)) 1 
              (Abs (Add (Add Iop 1 (Ref 1)) 2 (Ref 2)) 0 (Tag (Ref 0) (Ref 2)))
  end.

Lemma scott_numerals_are_normal: forall n, normal (scott n). 
Proof.  
induction n; unfold scott; fold scott; unfold zero, value; split_all. unfold tt; auto. 
Qed. 

Hint Resolve scott_numerals_are_normal. 

Lemma succ_scott: forall n, seq_red (App succ (scott n)) (scott (S n)).
Proof. intro; unfold succ.  repeat eapply2 succ_red.   Qed. 

(* zero-test *) 

Definition is_zero := 
Abs (Add (Add Iop 0 (Abs Iop 0 ff)) 1 tt) 2
    (Tag (Tag (Ref 2) (Ref 1)) (Ref 0)) . 

Lemma is_zero_zero: seq_red (App is_zero zero) tt .
Proof. unfold is_zero, zero, tt; split_all. repeat eapply2 succ_red. Qed.

Lemma is_zero_succ: forall n, seq_red (App is_zero (scott (S n))) ff .
Proof. intros. unfold is_zero, scott, ff. repeat eapply2 succ_red. Qed. 

(* predecessor *) 

Definition my_pred :=
 Abs Iop 0 (Tag (Tag (Ref 0) zero) (Abs Iop 0 (Ref 0))).
  (* λn.n zero (\x.x) *) 

Lemma pred_zero: seq_red (App my_pred zero) zero. 
Proof. unfold my_pred, zero, tt. repeat eapply2 succ_red. Qed. 

Lemma pred_succ: forall n, seq_red (App my_pred (scott (S n))) (scott n).
Proof. 
intro n; case n; unfold my_pred; split_all; repeat eapply2 succ_red. 
Qed. 


(* plus *) 
Definition my_plus_aux :=  
Abs Iop 3 (Abs (Add Iop 3 (Ref 3))  2 (Tag (Tag (Ref 2) (Abs Iop 0 (Ref 0)))
(Abs (Add Iop 3 (Ref 3)) 1 (Abs (Add (Add Iop 1 (Ref 1)) 3 (Ref 3)) 0 
     (App succ (Tag (Tag (Ref 3) (Ref 1)) (Ref 0))))))). 
Definition my_plus := App Y3 my_plus_aux. 
  (* Y3 (\fm.m(\n.n) ((\fxn. succ (fxn))f)) *) 


Lemma my_plus_scott: 
forall m n, seq_red (App (App my_plus (scott m)) (scott n)) (scott (m+n)).
Proof.
  induction m; intros. 
  (* 2 *) 
  split_all. unfold my_plus, zero; split_all.
  eapply transitive_red. 
  eapply2 fixpoint3_property.  
  unfold my_plus_aux. eapply2 succ_red. eapply2 succ_red. eapply2 succ_red. eapply2 succ_red. 
  eapply2 succ_red. eapply2 succ_red. eapply2 succ_red. eapply2 succ_red. 
  eapply2 succ_red. eapply2 succ_red. eapply2 succ_red. 
  eapply transitive_red. eapply preserves_app_seq_red. eapply2 if_true. auto. 
  eapply2 succ_red. 
  (* 1 *) 
  simpl. unfold my_plus. 
  eapply transitive_red. 
  eapply2 fixpoint3_property.
replace (App Y3 my_plus_aux) with my_plus by auto. 
  unfold my_plus_aux, succ. 
  repeat (eapply2 succ_red; eapply2 succ_red). 
eapply2 preserves_abs_seq_red. eapply2 preserves_add_seq_red.  
  unfold succ.  eapply2 succ_red; repeat (eapply2 succ_red; eapply2 succ_red).
 eapply2 succ_red; repeat (eapply2 succ_red; eapply2 succ_red).
eapply2 IHm. 
Qed. 


(* primitive recursion *) 


Lemma fold_left_app_preserves_seq_red:
forall xs M N, seq_red M N -> seq_red (fold_left App xs M) (fold_left App xs N).
Proof. induction xs; split_all. Qed.  
 

(* simple composition *) 

Definition compose_1_1:= 
Abs Iop 2 (Abs (Add Iop 2 (Ref 2)) 1
(Abs (Add (Add Iop 2 (Ref 2)) 1 (Ref 1)) 0
(Tag (Ref 2) (Tag (Ref 1) (Ref 0))))).

Lemma compose_1_1_val : 
forall g f x, seq_red (App (App (App compose_1_1 g) f) x) (App g (App f x)).
Proof. intros. unfold compose_1_1. repeat eapply2 succ_red. Qed.



(* projections *)



Fixpoint kn n := 
match n with 
| 0 => Iop 
| S n1 => App (App compose_1_1 tt) (kn n1) 
end.


Lemma kn_val: forall xs x, seq_red (fold_left App (x::xs) (kn (length xs))) x .
Proof.
induction xs; split_all. 
eapply transitive_red. 
eapply fold_left_app_preserves_seq_red. 
eapply preserves_app_seq_red. 
eapply2 compose_1_1_val. auto. 
eapply transitive_red. 
eapply fold_left_app_preserves_seq_red. 
eapply2 if_true.  
replace (fold_left App xs (App (kn (length xs)) x)) 
with (fold_left App (x :: xs) (kn (length xs)))
by auto. eapply2 IHxs. 
Qed. 

Fixpoint proj n i :=  (* 0<= i <= n *) 
match i with 
| 0 => kn n  
| S i1 => App tt (proj (pred n) i1) 
end.


Lemma projection_val: 
forall (xs : list lambda) i, i <= length xs -> 
seq_red (fold_left App xs (proj (pred (length xs)) i)) (nth i xs Iop). 
Proof.
induction xs; split_all. inversion H. subst.  unfold proj; auto. 
generalize H; clear H; case i; intros. 
unfold proj.
replace (fold_left App xs (App (kn (length xs)) a))
with (fold_left App (a::xs) (kn (length xs))) by auto. 
eapply2 kn_val. 
(* 1 *) 
unfold proj; fold proj. 
eapply transitive_red. 
eapply fold_left_app_preserves_seq_red. 
eapply2 if_true. eapply2 IHxs. omega. 
Qed. 

(* general composition *) 

Fixpoint compose_1_m m  := 
match m with 
| 0 => Iop
| S m1 => App (App compose_1_1 compose_1_1) (compose_1_m m1)
end.

Lemma compose_1_m_val: 
forall xs f g, seq_red (fold_left App xs (App (App (compose_1_m (length xs)) f) g)) (App f (fold_left App xs g)). 
Proof.
induction xs; split_all. 
eapply transitive_red. 
eapply fold_left_app_preserves_seq_red. 
eapply preserves_app_seq_red. 
eapply preserves_app_seq_red. 
eapply2 compose_1_1_val. auto. auto. 
eapply transitive_red. 
eapply fold_left_app_preserves_seq_red. 
eapply2 compose_1_1_val. 
eapply2 IHxs. 
Qed.

Fixpoint compose_k_m k m  := 
match k with 
| 0 => (kn m) 
| S k1 => App (App compose_1_1 (App compose_1_1 (compose_k_m k1 m))) (compose_1_m m)
end.

Lemma compose_k_m_val: 
forall gs xs f, 
seq_red (fold_left App xs (fold_left App gs (App (compose_k_m (length gs) (length xs)) f)))
        (fold_left App (map (fold_left App xs) gs) f).
Proof.
induction gs; split_all. 
eapply2 kn_val. 
eapply transitive_red. 
eapply fold_left_app_preserves_seq_red. 
eapply fold_left_app_preserves_seq_red. 
eapply preserves_app_seq_red. 
eapply2 compose_1_1_val. auto.
eapply transitive_red. 
eapply fold_left_app_preserves_seq_red. 
eapply fold_left_app_preserves_seq_red. 
eapply2 compose_1_1_val.
eapply transitive_red. 
eapply2 IHgs. 


missing a fold_left here 



eapply transitive_red. 
eapply fold_left_app_preserves_seq_red. 
eapply2 compose_1_m_val.
eapply transitive_red. 
eapply2 IHgs. 
eapply fold_left_app_preserves_seq_red. 
eapply2 compose_1_1_val. 
Qed.



(* restore ! 

Definition mu_scott_n f := 
App Ycomb (Abs 1 (0::nil) Iop 
                (Tag (Tag (Tag is_zero (Tag f (Ref 0))) (Ref 0)) 
                     (Tag (Ref 1) (App succ (Ref 0))))). 

Definition mu_scott f := App (mu_scott_n f) zero. 

Lemma mu_scott_property_true: 
forall x xs f n, seq_red (App (Abs x xs Iop f) (scott n)) zero -> 
seq_red (App (mu_scott_n (Abs x xs Iop f)) (scott n)) (scott n) . 
Proof.
intros; unfold mu_scott_n. eapply transitive_red. eapply preserves_app_seq_red. 
eapply2 fixpoint_property. auto. eapply2 succ_red.  eapply2 succ_red. 
 eapply2 succ_red.  eapply2 succ_red.  eapply2 succ_red.  eapply2 succ_red. 
 eapply2 succ_red.  eapply2 succ_red. eapply2 succ_red.  eapply2 succ_red. 
 eapply2 succ_red.  eapply2 succ_red.  
unfold is_zero. eapply2 succ_red.  eapply2 succ_red.  eapply2 succ_red.  eapply2 succ_red. 
eapply2 succ_red.  eapply2 succ_red.  eapply2 succ_red.  eapply2 succ_red. 
eapply transitive_red. eapply preserves_app_seq_red. eapply preserves_app_seq_red.
 eapply preserves_app_seq_red. eapply preserves_app_seq_red.
 eapply preserves_app_seq_red. eapply preserves_abs_seq_red.
eapply succ_red.  auto. 
eapply succ_red.  auto. 
eapply2 succ_red.  auto. auto. 
eapply2 succ_red.  unfold abs; eapply2 succ_red. auto. auto. 
eapply transitive_red. eapply preserves_app_seq_red. eapply preserves_app_seq_red.
 eapply preserves_app_seq_red. eapply preserves_app_seq_red.
eapply2 H. auto. auto.   auto. auto. 
(* 1 *) 
unfold zero. eapply2 succ_red. unfold tt, abs;  eapply2 succ_red. eapply2 succ_red.
eapply2 succ_red. eapply2 succ_red. eapply2 succ_red. eapply2 succ_red.
eapply2 succ_red. eapply2 succ_red. eapply2 succ_red. eapply2 succ_red.
eapply2 succ_red. eapply2 succ_red. 
Qed. 

Lemma mu_scott_property_false: 
forall x xs f n k, seq_red (App (Abs x xs Iop f) (scott n)) (scott (S k)) -> 
seq_red (App (mu_scott_n (Abs x xs Iop f)) (scott n)) 
        (App (mu_scott_n (Abs x xs Iop f)) (scott (S n))) . 
Proof.
intros; unfold mu_scott_n. eapply transitive_red. eapply preserves_app_seq_red. 
eapply2 fixpoint_property. auto. eapply2 succ_red.  eapply2 succ_red. 
 eapply2 succ_red.  eapply2 succ_red.  eapply2 succ_red.  eapply2 succ_red. 
 eapply2 succ_red.  eapply2 succ_red. eapply2 succ_red.  eapply2 succ_red. 
 eapply2 succ_red.  eapply2 succ_red.  
unfold is_zero. eapply2 succ_red.  eapply2 succ_red.  eapply2 succ_red.  eapply2 succ_red. 
eapply2 succ_red.  eapply2 succ_red.  eapply2 succ_red.  eapply2 succ_red. 
eapply transitive_red. eapply preserves_app_seq_red. eapply preserves_app_seq_red.
 eapply preserves_app_seq_red. eapply preserves_app_seq_red.
 eapply preserves_app_seq_red. eapply preserves_abs_seq_red.
eapply succ_red.  auto. 
eapply succ_red.  auto. 
eapply2 succ_red.  auto. auto. 
eapply2 succ_red.  unfold abs; eapply2 succ_red. auto. auto. 
eapply transitive_red. eapply preserves_app_seq_red. eapply preserves_app_seq_red.
 eapply preserves_app_seq_red. eapply preserves_app_seq_red.
eapply2 H. auto. auto.   auto. auto. 
(* 1 *) 
unfold scott; fold scott. eapply2 succ_red. unfold tt, abs;  eapply2 succ_red. eapply2 succ_red.
eapply2 succ_red. eapply2 succ_red. eapply2 succ_red. eapply2 succ_red.
eapply2 succ_red. eapply2 succ_red. eapply2 succ_red. eapply2 succ_red.
unfold ff, abs. eapply2 succ_red. eapply2 succ_red.  eapply2 succ_red.  
eapply2 succ_red. eapply2 preserves_app_seq_red.
unfold succ, abs. eapply2 succ_red.  eapply2 succ_red. eapply2 succ_red.  eapply2 succ_red. 
eapply2 succ_red.  eapply2 succ_red. 
Qed. 

Lemma mu_scott_property_le: 
forall k x xs f n, 
seq_red (App (mu_scott_n (Abs x xs Iop f)) (scott n)) (scott k) -> n<= k.
Proof.
induction k; split_all. 
intros; unfold mu_scott_n. eapply transitive_red. eapply preserves_app_seq_red. 
eapply2 fixpoint_property. auto. eapply2 succ_red.  eapply2 succ_red. 
 eapply2 succ_red.  eapply2 succ_red.  eapply2 succ_red.  eapply2 succ_red. 
 eapply2 succ_red.  eapply2 succ_red. eapply2 succ_red.  eapply2 succ_red. 
 eapply2 succ_red.  eapply2 succ_red.  
unfold is_zero. eapply2 succ_red.  eapply2 succ_red.  eapply2 succ_red.  eapply2 succ_red. 
eapply2 succ_red.  eapply2 succ_red.  eapply2 succ_red.  eapply2 succ_red. 
eapply transitive_red. eapply preserves_app_seq_red. eapply preserves_app_seq_red.
 eapply preserves_app_seq_red. eapply preserves_app_seq_red.
 eapply preserves_app_seq_red. eapply preserves_abs_seq_red.
eapply succ_red.  auto. 
eapply succ_red.  auto. 
eapply2 succ_red.  auto. auto. 
eapply2 succ_red.  unfold abs; eapply2 succ_red. auto. auto. 
eapply transitive_red. eapply preserves_app_seq_red. eapply preserves_app_seq_red.
 eapply preserves_app_seq_red. eapply preserves_app_seq_red.
eapply2 H. auto. auto.   auto. auto. 
(* 1 *) 
unfold scott; fold scott. eapply2 succ_red. unfold tt, abs;  eapply2 succ_red. eapply2 succ_red.
eapply2 succ_red. eapply2 succ_red. eapply2 succ_red. eapply2 succ_red.
eapply2 succ_red. eapply2 succ_red. eapply2 succ_red. eapply2 succ_red.
unfold ff, abs. eapply2 succ_red. eapply2 succ_red.  eapply2 succ_red.  
eapply2 succ_red. eapply2 preserves_app_seq_red.
unfold succ, abs. eapply2 succ_red.  eapply2 succ_red. eapply2 succ_red.  eapply2 succ_red. 
eapply2 succ_red.  eapply2 succ_red. 
Qed. 



Lemma mu_scott_property: 
forall k x xs f, 
seq_red (mu_scott (Abs x xs Iop f)) (scott k) -> 
seq_red (App (Abs x xs Iop f) (scott k)) zero . 
Proof.
induction k; intros. 
intros; unfold mu_scott_n. eapply2 succ_red.  eapply2 succ_red. 
 eapply2 succ_red.  eapply2 succ_red.  eapply2 succ_red.  eapply2 succ_red. 
 eapply2 succ_red.  eapply2 succ_red. eapply2 succ_red.  eapply2 succ_red. 
 eapply2 succ_red.  eapply2 succ_red.  
unfold is_zero. eapply2 succ_red.  eapply2 succ_red.  eapply2 succ_red.  eapply2 succ_red. 
eapply2 succ_red.  eapply2 succ_red.  eapply2 succ_red.  eapply2 succ_red. 
eapply transitive_red. eapply preserves_app_seq_red. eapply preserves_app_seq_red.
 eapply preserves_app_seq_red. eapply preserves_app_seq_red.
 eapply preserves_app_seq_red. eapply preserves_abs_seq_red.
eapply succ_red.  auto. 
eapply succ_red.  auto. 
eapply2 succ_red.  auto. auto. 
eapply2 succ_red.  unfold abs; eapply2 succ_red. auto. auto. 
eapply transitive_red. eapply preserves_app_seq_red. eapply preserves_app_seq_red.
 eapply preserves_app_seq_red. eapply preserves_app_seq_red.
eapply2 H. auto. auto.   auto. auto. 
(* 1 *) 
unfold scott; fold scott. eapply2 succ_red. unfold tt, abs;  eapply2 succ_red. eapply2 succ_red.
eapply2 succ_red. eapply2 succ_red. eapply2 succ_red. eapply2 succ_red.
eapply2 succ_red. eapply2 succ_red. eapply2 succ_red. eapply2 succ_red.
unfold ff, abs. eapply2 succ_red. eapply2 succ_red.  eapply2 succ_red.  
eapply2 succ_red. eapply2 preserves_app_seq_red.
unfold succ, abs. eapply2 succ_red.  eapply2 succ_red. eapply2 succ_red.  eapply2 succ_red. 
eapply2 succ_red.  eapply2 succ_red. 
Qed. 




forall f n, seq_red (App f (scott n)) zero 



*) 