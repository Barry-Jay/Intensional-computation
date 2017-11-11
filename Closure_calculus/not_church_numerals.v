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
(*                     not_church_numerals                            *)
(*                                                                    *)
(*                          Barry Jay                                 *)
(*                                                                    *)
(**********************************************************************)


Require Import List Omega Closure_calculus.


(* primitive recursion 
      https://en.wikipedia.org/wiki/Lambda_calculus#Arithmetic_in_lambda_calculus
 *)

(* 
The Church numeral n is an iterator, that maps f and x to f^n (x). 
Church numerals don't work in closure calculus, at least with the traditinal account of 
predecessor, since pred zero reduces to a normal form which, unlike zero, 
has a non-empty environment.  
*) 

Definition zero_c:= ff. (* \fx. x *) 
Definition succ_c := 
Abs Iop 2 (Abs (Add Iop 2 (Ref 2)) 1 (Abs (Add (Add Iop 2 (Ref 2)) 1 (Ref 1)) 0 
    (Tag (Ref 1) (Tag (Tag (Ref 2) (Ref 1)) (Ref 0))))). 
(* \nfx.f(nfx) *) 

Fixpoint church n :=
match n with
  | 0 => ff
  | S n => Abs (Add Iop 2 (church n)) 1 (Abs (Add (Add Iop 2 (Ref 2)) 1 (Ref 1)) 0 
               (Tag (Ref 1) (Tag (Tag (Ref 2) (Ref 1)) (Ref 0))))
end.

Lemma church_numerals_are_normal: forall n, normal (church n). 
Proof.  
induction n; unfold church; fold church; unfold zero, value; split_all. unfold ff; auto.
repeat eapply2 nf_abs.  
Qed. 

Hint Resolve church_numerals_are_normal. 

Lemma succ_church: forall n, seq_red (App succ_c (church n)) (church (S n)).
Proof. intro; unfold succ_c. repeat eapply2 succ_red.  Qed. 


Definition is_zero_c := Abs Iop 0 (Tag (Tag (Ref 0) (Abs Iop 0 ff)) tt).

Lemma is_zero_c_zero_c: seq_red (App is_zero_c zero_c) tt .
Proof. unfold is_zero_c, zero_c, ff, tt; split_all. repeat eapply2 succ_red. Qed.

Lemma is_zero_c_succ_c: forall n, seq_red (App is_zero_c (church (S n))) ff .
Proof. intros. unfold church, is_zero_c, tt, ff, church. repeat eapply2 succ_red. Qed. 


Definition my_pred_c :=
Abs Iop 2 (Abs (Add Iop 2 (Ref 2)) 1 (Abs (Add (Add Iop 2 (Ref 2)) 1 (Ref 1)) 0 
    (Tag (Tag (Tag (Ref 2) (Abs (Add (Add Iop 1 (Ref 1)) 0 (Ref 0)) 4
     (Abs (Add (Add (Add Iop 1 (Ref 1)) 0 (Ref 0)) 4 (Ref 4)) 3 
        (Tag (Ref 3) (Tag (Ref 4) (Ref 1))))))
              (Abs Iop 5 (Ref 0)))
         Iop)))
  (* λnfx. n (\gh. h(gf))(\u.x)(\u.u) *) 
.

Definition pred_0_nf := 
Abs (Add Iop 2 (Abs Iop 1 (Abs Iop 0 (Ref 0)))) 1
     (Abs (Add (Add Iop 2 (Ref 2)) 1 (Ref 1)) 0
        (Tag
           (Tag
              (Tag (Ref 2)
                 (Abs (Add (Add Iop 1 (Ref 1)) 0 (Ref 0)) 4
                    (Abs (Add (Add (Add Iop 1 (Ref 1)) 0 (Ref 0)) 4 (Ref 4)) 3 (Tag (Ref 3) (Tag (Ref 4) (Ref 1))))))
              (Abs Iop 5 (Ref 0))) Iop)).

 
Lemma pred_0_val : seq_red (App my_pred_c zero_c) pred_0_nf. 
Proof. unfold my_pred_c, zero_c, ff, tt. repeat eapply2 succ_red.  Qed. 


Lemma pred_zero_fails: ~(seq_red (App my_pred_c zero_c) zero_c).
Proof.
intro. 
assert (exists n, seq_red zero_c n /\ seq_red pred_0_nf n).
eapply2 closure_confluence.  eapply2 pred_0_val. split_all.  
assert(irreducible zero_c seq_red1). 
eapply2 irreducible_iff_normal. 
replace zero_c with (church 0) by auto. eapply2 church_numerals_are_normal. 
assert(x = zero_c). 
inversion H0; auto. 
assert False by eapply2 H1. contradiction. subst. 
assert(irreducible pred_0_nf seq_red1). 
eapply2 irreducible_iff_normal. 
unfold pred_0_nf;  auto 20. 
assert(zero_c = pred_0_nf). 
inversion H2; auto. 
assert False by eapply2 H3. contradiction.  discriminate. 
Qed. 

