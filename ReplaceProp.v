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


(****************************************************************************)
(*                          Signes Project                                  *)
(*                            2002-2003                                     *)
(*                           Houda ANOUN                                    *)
(*                          Pierre Casteran                                 *)
(*                           LaBRI/INRIA                                    *)
(****************************************************************************)



Require Export Terms.
Set Implicit Arguments.
Unset Strict Implicit.

Section replace_props.
Variable Atoms : Set.



(* Inductive definition of replace such that when
 (replace Gamma Gamma' Delta Delta'):then Gamma' results from replacing a 
distinguished occurrence of the subterm  Delta in the term Gamma by Delta' *)

Inductive replace (Atoms : Set) :
Term Atoms -> Term Atoms -> Term Atoms -> Term Atoms -> Set :=
  | replaceRoot : forall F1 F2 : Term Atoms, replace F1 F2 F1 F2
  | replaceLeft :
      forall Gamma1 Gamma2 Delta F1 F2 : Term Atoms,
      replace Gamma1 Gamma2 F1 F2 ->
      replace (Comma Gamma1 Delta) (Comma Gamma2 Delta) F1 F2
  | replaceRight :
      forall Gamma1 Gamma2 Delta F1 F2 : Term Atoms,
      replace Gamma1 Gamma2 F1 F2 ->
      replace (Comma Delta Gamma1) (Comma Delta Gamma2) F1 F2.

(*Inductive definition of replaceCommaDot such that when 
 (replaceCommaDot Gamma Gamma') then Gamma' is the result of replacing a 
number of commas in Gamma by the connector dot .
Example: forall (A,B:(Form Atoms)), (replaceCommaDot (A ,(A,B)) (A, (A.B))) 
where in this case only one occurrence of comma is replaced by a dot *)
Inductive replaceCommaDot (Atoms : Set) (T1 : Term Atoms) :
Term Atoms -> Set :=
  | noReplace : replaceCommaDot T1 T1
  | replaceOneComma :
      forall (T2 T3 : Term Atoms) (A B : Form Atoms),
      replaceCommaDot T1 T2 ->
      replace T2 T3 (Comma (OneForm A) (OneForm B)) (OneForm (Dot A B)) ->
      replaceCommaDot T1 T3.

(* transitivity of the replaceCommaDot *)
Definition replaceTransitive :
  forall T1 T2 T3 : Term Atoms,
  replaceCommaDot T2 T3 -> replaceCommaDot T1 T2 -> replaceCommaDot T1 T3.
 simple induction 1.
 auto.
 intros T4 T5 A B H0 H1 H2 H3.
 apply replaceOneComma with T4 A B; auto.
Defined.

(* Some theorem derived from the definition of replaceCommaDot *)
Definition replaceMonoRight :
  forall T1 T2 T3 : Term Atoms,
  replaceCommaDot T1 T2 -> replaceCommaDot (Comma T1 T3) (Comma T2 T3).
 simple induction 1.
 constructor 1.
 intros.
 eapply replaceOneComma.
 eauto.
 eapply replaceLeft.
 eauto.
Defined.

Definition replaceMonoLeft :
  forall T1 T2 T3 : Term Atoms,
  replaceCommaDot T1 T2 -> replaceCommaDot (Comma T3 T1) (Comma T3 T2).
 simple induction 1.
 constructor 1.
 intros; eapply replaceOneComma.
 eauto.
 eapply replaceRight.
 eauto.
Defined.

Definition replaceMono :
  forall T1 T2 T3 T4 : Term Atoms,
  replaceCommaDot T1 T2 ->
  replaceCommaDot T3 T4 -> replaceCommaDot (Comma T1 T3) (Comma T2 T4).

 intros T1 T2 T3 T4 H H0.
 apply replaceTransitive with (Comma T2 T3).
 apply replaceMonoLeft.
 assumption.
 apply replaceMonoRight.
 assumption.
Defined.



(* Definition which states that we can deduce (deltaTranslation T) from 
replacing a a number of Commas in T by Dots, and that is intuitively correct
 as in fact we replace recursively all Commas in T by Dots beginning first by 
leaves *)
Definition replaceTranslation :
  forall T : Term Atoms, replaceCommaDot T (OneForm (deltaTranslation T)).
 simple induction T.
 intro.
 simpl in |- *.
 apply noReplace.
 intros t H t0 H0.
 simpl in |- *.
 apply
  replaceTransitive
   with
     (Comma (OneForm (deltaTranslation t)) (OneForm (deltaTranslation t0))).
 eapply replaceOneComma.
 apply noReplace.
 eapply replaceRoot.
 apply replaceMono; assumption.
Defined.


Lemma replace_inv1 :
 forall (Gamma' Delta : Term Atoms) (X C : Form Atoms),
 replace (OneForm C) Gamma' (OneForm X) Delta -> Gamma' = Delta /\ X = C.
inversion 1; auto.
Qed.



Lemma replace_inv2 :
 forall (Gamma1 Gamma2 Gamma' Delta : Term Atoms) (X : Form Atoms),
 replace (Comma Gamma1 Gamma2) Gamma' (OneForm X) Delta ->
 sigT
   (fun Gamma'1 : Term Atoms =>
    {x_ : replace Gamma1 Gamma'1 (OneForm X) Delta |
    Gamma' = Comma Gamma'1 Gamma2}) +
 sigT
   (fun Gamma'2 : Term Atoms =>
    {x_ : replace Gamma2 Gamma'2 (OneForm X) Delta |
    Gamma' = Comma Gamma1 Gamma'2}).
inversion_clear 1.
left; exists Gamma3.
exists H0; auto.
right; exists Gamma3.
exists H0; auto.
Qed.

Definition doubleReplace :
  forall (Gamma Gamma' T1 T2 T3 : Term Atoms) (A : Form Atoms),
  replace Gamma Gamma' T1 T2 ->
  forall Gamma2 : Term Atoms,
  replace Gamma' Gamma2 (OneForm A) T3 ->
  sigT
    (fun T : Term Atoms =>
     (replace Gamma T (OneForm A) T3 * replace T Gamma2 T1 T2)%type) +
  sigT
    (fun T : Term Atoms =>
     (replace T2 T (OneForm A) T3 * replace Gamma Gamma2 T1 T)%type).


 simple induction 1.
 intros F1 F2 Gamma2 H0.
 right.
 split with Gamma2.
 split.
 auto.
 constructor 1.
 intros.
 elim (replace_inv2 H1); clear H1; intro H1; elim H1; clear H1; intros x H1;
  elim H1; clear H1; intros H1 H2.
 elim (H0 x H1); intro H3; elim H3; clear H3; intros x0 H3; elim H3; clear H3;
  intros H3 H4.
 left.
 split with (Comma x0 Delta).
 split.
 apply replaceLeft; auto.
 rewrite H2.
 apply replaceLeft; auto.
 right.
 split with x0.
 split.
 auto.
 rewrite H2.
 apply replaceLeft; auto.
 left.
 split with (Comma Gamma1 x).
 split.
 apply replaceRight; auto.
 rewrite H2.
 apply replaceLeft; auto.
 intros.
 elim (replace_inv2 H1); clear H1; intro H1; elim H1; clear H1; intros x H1;
  elim H1; clear H1; intros H1 H2.
 left.
 split with (Comma x Gamma1).
 split.
 apply replaceLeft; auto.
 rewrite H2.
 apply replaceRight; auto.
 elim (H0 x H1); intro H3; elim H3; clear H3; intros x0 H3; elim H3; clear H3;
  intros H3 H4.
 left.
 split with (Comma Delta x0).
 split.
 apply replaceRight; auto.
 rewrite H2.
 apply replaceRight; auto.
 right.
 split with x0.
 split.
 auto.
 rewrite H2; apply replaceRight; auto.
Defined.

Definition replaceSameP :
  forall T1 T2 T3 T4 : Term Atoms,
  replace T1 T2 T3 T4 ->
  forall T : Term Atoms,
  sigT
    (fun T' : Term Atoms => (replace T1 T' T3 T * replace T' T2 T T4)%type). 
 simple induction 1.
 intros.
 split with T.
 split; constructor 1.
 intros.
 elim (H0 T); clear H0; intros x H0.
 split with (Comma x Delta).
 elim H0.
 clear H0; intros.
 split; apply replaceLeft; auto.
 intros.
 elim (H0 T); clear H0; intros x H0.
 elim H0; clear H0; intros.
 split with (Comma Delta x).
 split; apply replaceRight; auto.
Defined.

Definition replaceTrans :
  forall T1 T2 T3 T4 : Term Atoms,
  replace T1 T2 T3 T4 ->
  forall T5 T6 : Term Atoms, replace T3 T4 T5 T6 -> replace T1 T2 T5 T6.
 simple induction 1.
 auto.
 intros.
 apply replaceLeft; auto.
 intros.
 apply replaceRight; auto.                   
Defined.

End replace_props.