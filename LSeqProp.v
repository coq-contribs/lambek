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

Require Export Sequent.
Set Implicit Arguments.
Unset Strict Implicit.
Section LProperties.
Variable Atoms : Set.

(* Definition of a function that takes two trees of formulas as parameters and
returns the tree obtained by adding the second tree to the most right node of 
the first one*)
Fixpoint addToEnd (Atoms : Set) (T1 T2 : Term Atoms) {struct T1} :
 Term Atoms :=
  match T1 with
  | OneForm f => Comma (OneForm f) T2
  | Comma L M => Comma L (addToEnd M T2)
  end.

(* some properties of addToEnd *)
Definition addToEndL :
  forall T1 T2 T3 : Term Atoms,
  addToEnd T1 (addToEnd T2 T3) = addToEnd (addToEnd T1 T2) T3.
 intros T1 T2 T3.
 elim T1.
 simpl in |- *.
 auto.
 intros t H t0 H0.
 simpl in |- *.
 rewrite H0.
 reflexivity.
Defined.

Definition addToEndCom :
  forall (T1 T2 : Term Atoms) (F : Form Atoms),
  addToEnd T1 T2 = OneForm F -> False.
 intros T1 T2 F.
 elim T1.
 simpl in |- *.
 intros f H.
 discriminate H.
 simpl in |- *.
 intros t H t0 H0 H1.
 discriminate H1.
Defined.

(* Definition of the function that takes a tree of formulas
and returns the corresponding flatten tree *)
Fixpoint convertTree (Atoms : Set) (T : Term Atoms) {struct T} :
 Term Atoms :=
  match T with
  | OneForm f => OneForm f
  | Comma T1 T2 => addToEnd (convertTree T1) (convertTree T2)
  end.


Definition replaceConvert :
  forall T1 T2 T3 T4 : Term Atoms,
  replace T1 T2 T3 T4 ->
  convertTree T3 = convertTree T4 -> convertTree T1 = convertTree T2.
 simple induction 1.
 auto.
 intros G1 G2 D F1 F2 r H0 H1.
 simpl in |- *.
 elim (H0 H1).
 auto.
 intros G1 G2 D F1 F2 r H0 H1.
 simpl in |- *.
 elim (H0 H1).
 auto.
Defined.


(* Inductive definition that generalises L_Sequent...
We have (LGeneralization T1 T2) iff T1 and T2 represents the same sequence
of formulas *)
Inductive LGeneralization (Atoms : Set) : Term Atoms -> Term Atoms -> Set :=
  | sameTerm : forall T : Term Atoms, LGeneralization T T
  | termL :
      forall T1 T2 G1 G2 T' : Term Atoms,
      LGeneralization T1 T2 ->
      L_Sequent G1 G2 -> replace T2 T' G1 G2 -> LGeneralization T1 T'.

(*some Properties of LGeneralization *)
Definition LGenTransitive :
  forall T1 T2 T3 : Term Atoms,
  LGeneralization T2 T3 -> LGeneralization T1 T2 -> LGeneralization T1 T3.
 simple induction 1.
 auto.
 intros T0 T4 G1 G2; intros.
 apply termL with T4 G1 G2; auto.
Defined.

Definition replaceSym :
  forall T1 T2 T3 T4 : Term Atoms, replace T1 T2 T3 T4 -> replace T2 T1 T4 T3.
 simple induction 1.
 constructor 1.
 intros.
 apply replaceLeft; auto.
 intros.
 apply replaceRight; auto.
Defined.

Definition LSequenTSym :
  forall T1 T2 : Term Atoms, L_Sequent T1 T2 -> L_Sequent T2 T1.
 simple induction 1.
 intros; constructor 2.
 intros; constructor 1.
Defined.

Definition LGenSymetrique :
  forall T1 T2 : Term Atoms, LGeneralization T1 T2 -> LGeneralization T2 T1.
 simple induction 1.
 constructor 1.
 intros.
 eapply LGenTransitive.
 eauto.
 eapply termL.
 constructor 1.
 eapply LSequenTSym; eauto.
 apply replaceSym; assumption.
Defined.

Definition LGenMonoLeft :
  forall T1 T2 T : Term Atoms,
  LGeneralization T1 T2 -> LGeneralization (Comma T T1) (Comma T T2).
 simple induction 1.
 constructor 1.
 intros.
 eapply termL.
 eauto.
 eauto.
 apply replaceRight; assumption.
Defined.

Definition LGenMonoRight :
  forall T1 T2 T : Term Atoms,
  LGeneralization T1 T2 -> LGeneralization (Comma T1 T) (Comma T2 T).
 simple induction 1.
 constructor 1.
 intros.
 eapply termL.
 eauto.
 eauto.
 apply replaceLeft; assumption.
Defined.

Definition LGenMono :
  forall T1 T2 T3 T4 : Term Atoms,
  LGeneralization T1 T2 ->
  LGeneralization T3 T4 -> LGeneralization (Comma T1 T3) (Comma T2 T4).
 intros T1 T2 T3 T4; intros.
 apply LGenTransitive with (Comma T1 T4).
 apply LGenMonoRight; auto.
 apply LGenMonoLeft; auto.
Defined.

Definition LGenAddToEnd :
  forall T1 T2 : Term Atoms, LGeneralization (addToEnd T1 T2) (Comma T1 T2).
 
 intros T1 T2.
 elim T1.
 simpl in |- *.
 constructor 1.
 intros t H t0 H0.
 simpl in |- *.
 apply LGenTransitive with (Comma t (Comma t0 T2)).
 eapply termL; [ constructor 1 | idtac | constructor 1 ].
 constructor 1.
 apply LGenMonoLeft; auto.
Defined.

Definition LGenConvertT :
  forall T : Term Atoms, LGeneralization (convertTree T) T.
 intro T.
 elim T.
 simpl in |- *.
 constructor 1.
 intros t H t0 H0.
 simpl in |- *.
 apply LGenTransitive with (Comma (convertTree t) (convertTree t0)).
 apply LGenMono; auto.
 apply LGenAddToEnd.
Defined.

Definition eqFlattenTreeL :
  forall T1 T2 : Term Atoms,
  LGeneralization T1 T2 -> convertTree T1 = convertTree T2.
 intros T1 T2 H.
 elim H.
 auto.
 intros T3 T4 G1 G2 T' l H0 l0 r.
 rewrite H0.
 eapply replaceConvert.
 eauto.
 elim l0.
 intros.
 simpl in |- *.
 apply addToEndL.
 intros.
 simpl in |- *.
 elim addToEndL.
 auto.
Defined.

Definition LgenEqFlattenTrees :
  forall T1 T2 : Term Atoms,
  convertTree T1 = convertTree T2 -> LGeneralization T1 T2.
 intros T1 T2 H.
 eapply LGenTransitive.
 eapply LGenConvertT.
 rewrite <- H.
 apply LGenSymetrique.
 apply LGenConvertT.
Defined.

Section sequentsLogicL.
Require Export NaturalDeduction.

Definition LGenSequent :
  forall (T1 T2 : Term Atoms) (F : Form Atoms),
  LGeneralization T1 T2 ->
  gentzenSequent L_Sequent T1 F -> gentzenSequent L_Sequent T2 F.
 simple induction 1.
 auto.
 intros.
 eapply SequentExtension; eauto.
Defined.

Definition LNaturalDeduction :
  forall (T1 T2 : Term Atoms) (F : Form Atoms),
  LGeneralization T1 T2 ->
  natDed L_Sequent T1 F -> natDed L_Sequent T2 F.
simple induction 1.
 auto.
 intros.
 eapply NatExt; eauto.
Defined.

End sequentsLogicL.
End LProperties.