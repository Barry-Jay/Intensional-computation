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
(*                           General.v                                *)
(*                                                                    *)
(*                          Barry Jay                                 *)
(*                                                                    *)
(**********************************************************************)

Require Import Omega ArithRing. 

(* some general-purpose tactics *) 

Ltac eapply2 H := eapply H; eauto.


Ltac split_all := simpl; intros; auto.

Ltac noway := intros; assert False by omega; contradiction. 

Ltac exist x := exists x; split_all. 

Ltac gen_case H W := 
  generalize H; clear H; case W; split_all. 

Ltac gen2_case H0 H1 W := 
  generalize H0 H1; clear H0 H1; case W; split_all.

Ltac gen3_case H0 H1 H2 W := 
  generalize H0 H1 H2; clear H0 H1 H2; case W; split_all.

Ltac gen4_case H0 H1 H2 H3 W := 
  generalize H0 H1 H2 H3; clear H0 H1 H2 H3; case W; split_all.

Ltac gen_inv H W := 
  generalize H; clear H; inversion W; split_all. 

Ltac gen2_inv H0 H1 W := 
  generalize H0 H1; clear H0 H1; inversion W; split_all.

Ltac gen3_inv H0 H1 H2 W := 
  generalize H0 H1 H2; clear H0 H1 H2; inversion W; split_all.

Ltac gen4_inv H0 H1 H2 H3 W := 
  generalize H0 H1 H2 H3; clear H0 H1 H2 H3; inversion W; split_all.


Ltac gen_case_inv H M := gen_case H M; inversion H; auto.

Ltac invsub := match goal with | H : _ = _ |- _ => inversion H; subst; clear H; invsub | _ => split_all end. 


(* some arithmetic *) 




Lemma max_is_max : forall m n, max m n >= m /\ max m n >= n.
Proof. 
double induction m n; split; auto; try omega.
elim (H0 n); intros; auto; simpl; omega. 
elim (H0 n); intros; auto; simpl; omega. 
Qed. 


Lemma max_succ: forall m n, S (max m n) = max (S m) (S n). 
Proof. double induction m n; split_all.  Qed. 

Lemma max_pred: forall m n, pred (max m n) = max (pred m) (pred n). 
Proof. double induction m n; intros; auto. case n; intros; auto. Qed. 

Lemma max_max : forall m n p, m >= max n p -> m>= n /\ m>= p.
Proof. 
induction m; intros n p. 
case n; case p; simpl; intros; split; auto; subst; try noway; try omega. 
intros. 
assert(m >= pred (max n p)) by omega. 
rewrite max_pred in H0. 
elim (IHm (pred n) (pred p)); split_all; omega. 
Qed. 

Lemma max_max2 : forall m n k, k>= m -> k>= n -> k>= max m n. 
Proof. 
double induction m n; simpl; intros; auto. 
assert(pred k >= max n1 n) .  eapply2 H0; omega.  omega. 
Qed. 

Lemma max_zero : forall m, max m 0 = m. 
Proof. induction m; split_all. Qed.

Lemma max_plus: forall m n k, max m n +k = max (m+k) (n+k). 
Proof.
double induction m n; simpl; intros; auto. 
induction k; simpl; auto.  
assert(max k (S (n0+k)) >= S(n0+k)) by eapply2 max_is_max.  
assert(S(n0+k) >= max k (S(n0+k))) . eapply2 max_max2. 
omega. 
omega. 
case k; simpl; intros; auto. 
assert(max (n+S n1) n1 >= n+ S n1) by  eapply2 max_is_max.  
assert(n+ S n1 >= max (n+S n1) n1) . eapply2 max_max2. 
omega. 
omega. 
Qed. 

Lemma max_minus: forall m n k, max m n -k = max (m-k) (n-k). 
Proof.
double induction m n; split_all.
case k; split_all. 
rewrite max_zero. omega.
case k; split_all. 
Qed. 

Lemma max_monotonic : forall m1 m2 n1 n2, m1 >= n1 -> m2 >= n2 -> max m1 m2 >= max n1 n2. 
Proof. 
double induction m1 m2; split_all. 
assert (n1 = 0) by omega; subst. 
assert (n2 = 0) by omega; subst. 
split_all. 
assert (n1 = 0) by omega; subst. split_all. 
assert (n2 = 0) by omega; subst. 
assert(max n1 0 = n1) . case n1; split_all. 
rewrite H2; auto.  
assert(n0 >= pred n1) by omega.
cut(max n0 n >= pred (max n1 n2)).  
intro.  
omega. 
rewrite max_pred. 
eapply2 H0. 
omega. 
Qed. 

Lemma max_succ_zero : forall k n, max k (S n) = 0 -> False .
Proof. split_all. assert(max k (S n) >= S n) by eapply2 max_is_max. noway. Qed. 
Ltac max_out := 
match goal with 
| H : max _ (S _) = 0  |- _ => assert False by (eapply2 max_succ_zero); noway
| H : max ?m ?n = 0 |- _ => 
assert (m = 0) by (assert (max m n >= m) by eapply2 max_is_max; omega);
assert (n = 0) by (assert (max m n >= n) by eapply2 max_is_max; omega);
clear H; try omega; try noway
| H : max ?m ?n <= 0 |- _ => 
assert (m = 0) by (assert (max m n >= m) by eapply2 max_is_max; omega);
assert (n = 0) by (assert (max m n >= n) by eapply2 max_is_max; omega);
clear H; try omega; try noway
end. 

Lemma max_choice: forall m n, max m n = m \/ max m n = n.
Proof.
induction m; split_all.   case n; split_all. 
assert(max m n0 = m \/ max m n0 = n0) by eapply2 IHm. 
inversion H; rewrite H0; auto. 
Qed.

