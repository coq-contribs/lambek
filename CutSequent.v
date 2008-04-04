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

(* proof of the sub-formula property in the sequent calculus *)
Require Import Arith.
Require Import Max.
Require Export Sequent.
Set Implicit Arguments.
Unset Strict Implicit.

(* some arithmetic results that will be used in the final proof *)

Lemma maxNatL : forall n m : nat, max n m = 0 -> n = 0.
Proof. 
 intros m n H.
 cut (m <= 0).
 intro.
 cut (0 = m); auto. 
 apply le_n_O_eq.
 assumption.
 rewrite <- H.
 apply le_max_l.
Qed.

Lemma maxNatR : forall n m : nat, max n m = 0 -> m = 0.
Proof.
 intros m m' H.
 cut (0 = m'); auto.
 cut (m' <= 0).
 intro.
 apply le_n_O_eq.
 assumption.
 rewrite <- H.
 auto with arith.
Qed.
(* end of arithmetic part *)

(* definition of the degree of a formula recursively *)
 Fixpoint degreeFormula (Atoms : Set) (F : Form Atoms) {struct F} : nat :=
   match F with
   | At Atoms => 1
   | Slash F1 F2 => S (max (degreeFormula F1) (degreeFormula F2))
   | Backslash F1 F2 => S (max (degreeFormula F1) (degreeFormula F2))
   | Dot F1 F2 => S (max (degreeFormula F1) (degreeFormula F2))
   end.

(* Lemma that states that the degree of a formula is strictly positif *)
Lemma degreeForm_O :
 forall (Atoms : Set) (F : Form Atoms), 1 <= degreeFormula F.
Proof.
 intros Atoms F.
 elim F; intros; simpl in |- *; auto with arith.
Qed.

(* Recursive definition of the degree of a proof which is
 the max of the degree of its cut rules (the degree of a cut rule
 is the degree of the formula which is eliminated in the conclusion 
sequent )*)

Fixpoint degreeProof (Atoms : Set) (Gamma : Term Atoms) 
 (B : Form Atoms) (E : gentzen_extension) (p : gentzenSequent E Gamma B)
 {struct p} : nat :=
  match p with
  | Ax _ => 0
  | RightSlash _ _ _ H => degreeProof H
  | RightBackSlash _ _ _ H => degreeProof H
  | RightDot _ _ _ _ H1 H2 => max (degreeProof H1) (degreeProof H2)
  | LeftSlash _ _ _ _ _ _ R H1 H2 => max (degreeProof H1) (degreeProof H2)
  | LeftBackSlash _ _ _ _ _ _ R H1 H2 =>
      max (degreeProof H1) (degreeProof H2)
  | LeftDot _ _ _ _ _ R H => degreeProof H
  | CutRule _ _ _ A _ R H1 H2 =>
      max (max (degreeFormula A) (degreeProof H1)) (degreeProof H2)
  | SequentExtension _ _ _ _ _ E R H => degreeProof H
  end.

(* test *)

(* Eval Compute in (degreeProof (application A B E)).
     = (0)
     : nat*)

(* Inductive definition of the relation subFormula *)
Inductive subFormula (Atoms : Set) : Form Atoms -> Form Atoms -> Prop :=
  | equalForm : forall A : Form Atoms, subFormula A A
  | slashL :
      forall A B C : Form Atoms, subFormula A B -> subFormula A (Slash B C)
  | slashR :
      forall A B C : Form Atoms, subFormula A B -> subFormula A (Slash C B)
  | backslashL :
      forall A B C : Form Atoms,
      subFormula A B -> subFormula A (Backslash B C)
  | backslashR :
      forall A B C : Form Atoms,
      subFormula A B -> subFormula A (Backslash C B)
  | dotL :
      forall A B C : Form Atoms, subFormula A B -> subFormula A (Dot B C)
  | dotR :
      forall A B C : Form Atoms, subFormula A B -> subFormula A (Dot C B).

(*some lemmas concerning the relation subformula *)

(* Lemma that states that the only subformula of a primitif type 
is this primitif type itself *)
Lemma subAt :
 forall (Atoms : Set) (A : Form Atoms) (at_ : Atoms),
 subFormula A (At at_) -> A = At at_.
 intros Atoms A at_ H.
 inversion H.
 reflexivity.
Qed.


Lemma subSlash :
 forall (Atoms : Set) (A B C : Form Atoms),
 subFormula A (Slash B C) ->
 A = Slash B C \/ subFormula A B \/ subFormula A C.

 intros Atoms A B C H.
 inversion H; auto.
Qed.

Lemma subBackslash :
 forall (Atoms : Set) (A B C : Form Atoms),
 subFormula A (Backslash B C) ->
 A = Backslash B C \/ subFormula A B \/ subFormula A C.

 intros Atoms A B C H.
 inversion H; auto.
Qed.
 

Lemma subDot :
 forall (Atoms : Set) (A B C : Form Atoms),
 subFormula A (Dot B C) -> A = Dot B C \/ subFormula A B \/ subFormula A C.
 intros Atoms A B C H.
 inversion H; auto.

Defined.

Lemma subFormulaTrans :
 forall (Atoms : Set) (A B C : Form Atoms),
 subFormula A B -> subFormula B C -> subFormula A C.

 intros At A B C.
 elim C.
 intros a H H0.
 elim (subAt H0).
 assumption.
 intros f H f0 H0 H1 H2.
 elim (subSlash H2); intro H3.
 rewrite <- H3; auto.
 elim H3; intro.
 apply slashL; auto.
 apply slashR; auto.
 intros f H f0 H0 H1 H2.
 elim (subDot H2); intro H3.
 rewrite <- H3; auto.
 elim H3; intro.
 apply dotL; auto.
 apply dotR; auto.
 intros f H f0 H0 H1 H2.
 elim (subBackslash H2); intro H3.
 rewrite <- H3; auto.
 elim H3; clear H3; intro.
 apply backslashL; auto.
 apply backslashR; auto.
Qed.

Inductive subFormTerm (Atoms : Set) : Form Atoms -> Term Atoms -> Prop :=
  | eqFT :
      forall A B : Form Atoms, subFormula A B -> subFormTerm A (OneForm B)
  | comL :
      forall (A : Form Atoms) (T1 T2 : Term Atoms),
      subFormTerm A T1 -> subFormTerm A (Comma T1 T2)
  | comR :
      forall (A : Form Atoms) (T1 T2 : Term Atoms),
      subFormTerm A T1 -> subFormTerm A (Comma T2 T1).

Lemma oneFormSub :
 forall (Atoms : Set) (A B : Form Atoms),
 subFormTerm A (OneForm B) -> subFormula A B.
 intros Atoms A B H.
 inversion H.
 assumption.
Qed.

Lemma comSub :
 forall (Atoms : Set) (f : Form Atoms) (T1 T2 : Term Atoms),
 subFormTerm f (Comma T1 T2) -> subFormTerm f T1 \/ subFormTerm f T2.

 intros Atoms f T1 T2 H.
 inversion H.
 left; assumption.
 right; assumption.
Qed.

Definition subReplace1 :
  forall (Atoms : Set) (T1 T2 T3 T4 : Term Atoms) (F : Form Atoms),
  replace T1 T2 T3 T4 -> subFormTerm F T3 -> subFormTerm F T1.
 simple induction 1.
 auto.
 intros.
 apply comL.
 auto.
 intros.
 apply comR.
 auto.
Defined.

Definition subReplace2 :
  forall (Atoms : Set) (T1 T2 T3 T4 : Term Atoms) (F : Form Atoms),
  replace T1 T2 T3 T4 -> subFormTerm F T4 -> subFormTerm F T2.

 simple induction 1.
 auto.
 intros.
 apply comL.
 auto.
 intros.
 apply comR.
 auto.
Defined.


Definition subReplace3 :
  forall (Atoms : Set) (T1 T2 T3 T4 : Term Atoms) (x : Form Atoms),
  replace T1 T2 T3 T4 ->
  subFormTerm x T1 -> subFormTerm x T2 \/ subFormTerm x T3.

 simple induction 1.
 auto.
 intros.
 elim (comSub H1).
 intro.
 elim (H0 H2).
 intro; left; apply comL; auto.
 auto.
 intro; left; apply comR; auto.
 intros.
 elim (comSub H1).
 intro; left; apply comL; auto.
 intro H2.
 elim (H0 H2).
 intro; left; apply comR; auto.
 auto.
Defined.

Definition CutFreeProof (Atoms : Set) (Gamma : Term Atoms) 
  (B : Form Atoms) (E : gentzen_extension) (p : gentzenSequent E Gamma B) :=
  degreeProof p = 0 :>nat.

Lemma notCutFree :
 forall (Atoms : Set) (E : gentzen_extension) (T1 T2 D : Term Atoms)
   (A C : Form Atoms) (r : replace T1 T2 (OneForm A) D)
   (p1 : gentzenSequent E D A) (p2 : gentzenSequent E T1 C),
 ~ CutFreeProof (CutRule r p1 p2).

 intros At E T1 T2 D A C r p1 p2.
 red in |- *.
 unfold CutFreeProof in |- *.
 simpl in |- *.
 intro H.
 cut (1 <= degreeFormula A).
 intro H1.
 cut (degreeFormula A = 0).
 intro H3.
 rewrite H3 in H1.
 generalize H1.
 cut (~ 1 <= 0).
 auto.
 apply le_Sn_O.
 cut (max (degreeFormula A) (degreeProof p1) = 0).
 intro; eapply maxNatL; eauto.
 eapply maxNatL; eauto.
 apply degreeForm_O.
Qed.

Inductive subProofOne (Atoms : Set) (E : gentzen_extension) :
forall (Gamma1 Gamma2 : Term Atoms) (B C : Form Atoms),
gentzenSequent E Gamma1 B -> gentzenSequent E Gamma2 C -> Prop :=
  | rs :
      forall (Gamma : Term Atoms) (A B : Form Atoms)
        (p : gentzenSequent E (Comma Gamma (OneForm B)) A),
      subProofOne p (RightSlash p)
  | rbs :
      forall (Gamma : Term Atoms) (A B : Form Atoms)
        (p : gentzenSequent E (Comma (OneForm B) Gamma) A),
      subProofOne p (RightBackSlash p)
  | rd1 :
      forall (Gamma Delta : Term Atoms) (A B : Form Atoms)
        (p1 : gentzenSequent E Gamma A) (p2 : gentzenSequent E Delta B),
      subProofOne p1 (RightDot p1 p2)
  | rd2 :
      forall (Gamma Delta : Term Atoms) (A B : Form Atoms)
        (p1 : gentzenSequent E Gamma A) (p2 : gentzenSequent E Delta B),
      subProofOne p2 (RightDot p1 p2)
  | ls1 :
      forall (Delta Gamma Gamma' : Term Atoms) (A B C : Form Atoms)
        (r : replace Gamma Gamma' (OneForm A)
               (Comma (OneForm (Slash A B)) Delta))
        (p1 : gentzenSequent E Delta B) (p2 : gentzenSequent E Gamma C),
      subProofOne p1 (LeftSlash r p1 p2)
  | ls2 :
      forall (Delta Gamma Gamma' : Term Atoms) (A B C : Form Atoms)
        (r : replace Gamma Gamma' (OneForm A)
               (Comma (OneForm (Slash A B)) Delta))
        (p1 : gentzenSequent E Delta B) (p2 : gentzenSequent E Gamma C),
      subProofOne p2 (LeftSlash r p1 p2)
  | lbs1 :
      forall (Delta Gamma Gamma' : Term Atoms) (A B C : Form Atoms)
        (r : replace Gamma Gamma' (OneForm A)
               (Comma Delta (OneForm (Backslash B A))))
        (p1 : gentzenSequent E Delta B) (p2 : gentzenSequent E Gamma C),
      subProofOne p1 (LeftBackSlash r p1 p2)
  | lbs2 :
      forall (Delta Gamma Gamma' : Term Atoms) (A B C : Form Atoms)
        (r : replace Gamma Gamma' (OneForm A)
               (Comma Delta (OneForm (Backslash B A))))
        (p1 : gentzenSequent E Delta B) (p2 : gentzenSequent E Gamma C),
      subProofOne p2 (LeftBackSlash r p1 p2)
  | ld :
      forall (Gamma Gamma' : Term Atoms) (A B C : Form Atoms)
        (r : replace Gamma Gamma' (Comma (OneForm A) (OneForm B))
               (OneForm (Dot A B))) (p : gentzenSequent E Gamma C),
      subProofOne p (LeftDot r p)
  | cr1 :
      forall (Delta Gamma Gamma' : Term Atoms) (A C : Form Atoms)
        (r : replace Gamma Gamma' (OneForm A) Delta)
        (p1 : gentzenSequent E Delta A) (p2 : gentzenSequent E Gamma C),
      subProofOne p1 (CutRule r p1 p2)
  | cr2 :
      forall (Delta Gamma Gamma' : Term Atoms) (A C : Form Atoms)
        (r : replace Gamma Gamma' (OneForm A) Delta)
        (p1 : gentzenSequent E Delta A) (p2 : gentzenSequent E Gamma C),
      subProofOne p2 (CutRule r p1 p2)
  | se :
      forall (Gamma Gamma' T1 T2 : Term Atoms) (C : Form Atoms)
        (e : E Atoms T1 T2) (r : replace Gamma Gamma' T1 T2)
        (p : gentzenSequent E Gamma C),
      subProofOne p (SequentExtension e r p).

Inductive subProof (Atoms : Set) (E : gentzen_extension) :
forall (Gamma1 Gamma2 : Term Atoms) (B C : Form Atoms),
gentzenSequent E Gamma1 B -> gentzenSequent E Gamma2 C -> Prop :=
  | sameProof :
      forall (T : Term Atoms) (A : Form Atoms) (p : gentzenSequent E T A),
      subProof p p
  | subProof1 :
      forall (T1 T2 T3 : Term Atoms) (A1 A2 A3 : Form Atoms)
        (p1 : gentzenSequent E T1 A1) (p2 : gentzenSequent E T2 A2)
        (p3 : gentzenSequent E T3 A3),
      subProof p2 p1 -> subProofOne p3 p2 -> subProof p3 p1.


Lemma CutFreeSubProofOne :
 forall (Atoms : Set) (Gamma1 Gamma2 : Term Atoms) 
   (B C : Form Atoms) (E : gentzen_extension) (p : gentzenSequent E Gamma1 B)
   (q : gentzenSequent E Gamma2 C),
 subProofOne q p -> CutFreeProof p -> CutFreeProof q.

 simple induction 1; intros; unfold CutFreeProof in H0; simpl in H0;
  unfold CutFreeProof in |- *.
 assumption.
 auto.
 eapply maxNatL; eauto.
 eapply maxNatR; eauto.
 eapply maxNatL; eauto.
 eapply maxNatR; eauto.
 eapply maxNatL; eauto.
 eapply maxNatR; eauto.
 auto.
 cut (max (degreeFormula A) (degreeProof p1) = 0).
 intro.
 eapply maxNatR; eauto.
 eapply maxNatL; eauto.
 eapply maxNatR; eauto.
 auto.
Qed.

Lemma CutFreeSubProof :
 forall (Atoms : Set) (Gamma1 Gamma2 : Term Atoms) 
   (B C : Form Atoms) (E : gentzen_extension) (p : gentzenSequent E Gamma1 B)
   (q : gentzenSequent E Gamma2 C),
 subProof q p -> CutFreeProof p -> CutFreeProof q.

 simple induction 1.
 auto.
 intros T1 T2 T3 A1 A2 A3 p1 p2; intros.
 apply CutFreeSubProofOne with T2 A2 p2; auto.
Qed.


Definition extensionSub (Atoms : Set) (X : gentzen_extension) :=
  forall (T1 T2 : Term Atoms) (F : Form Atoms),
  X Atoms T1 T2 -> subFormTerm F T1 -> subFormTerm F T2.

Lemma subFormulaPropertyOne :
 forall (Atoms : Set) (Gamma1 Gamma2 : Term Atoms) 
   (B C x : Form Atoms) (E : gentzen_extension)
   (p : gentzenSequent E Gamma1 B) (q : gentzenSequent E Gamma2 C),
 extensionSub Atoms E ->
 subProofOne q p ->
 CutFreeProof p ->
 subFormTerm x Gamma2 \/ subFormula x C ->
 subFormTerm x Gamma1 \/ subFormula x B.

 intros Atoms G1 G2 B C x E p q Ex H.
 elim H; intros.
 elim H1; clear H1; intro H1.
 elim (comSub H1); clear H1; intro.
 auto.
 right; apply slashR; apply oneFormSub; auto.
 right; apply slashL; auto.
 elim H1; clear H1; intro H1.
 elim (comSub H1); intro.
 right; apply backslashL; apply oneFormSub; auto.
 auto.
 right; apply backslashR; auto.
 elim H1; clear H1; intro H1.
 left; apply comL; auto.
 right; apply dotL; auto.
 elim H1; clear H1; intro H1.
 left; apply comR; auto.
 right; apply dotR; auto.
 elim H1; clear H1; intro H1.
 left; eapply subReplace2; eauto.
 apply comR; auto.
 left; eapply subReplace2.
 eauto.
 apply comL; apply eqFT; apply slashR; auto.
 elim H1; clear H1; intro H1.
 elim (subReplace3 r H1).
 auto.
 intro; left; eapply subReplace2.
 eauto.
 apply comL; apply eqFT; apply slashL; apply oneFormSub; auto.
 auto.
 elim H1; clear H1; intro H1.
 left; eapply subReplace2.
 eauto.
 apply comL; auto.
 left; eapply subReplace2.
 eauto.
 apply comR; apply eqFT; apply backslashL; auto.
 elim H1; clear H1; intro H1.
 elim (subReplace3 r H1).
 auto.
 intro; left; eapply subReplace2.
 eauto.
 apply comR; apply eqFT; apply backslashR; apply oneFormSub; auto.
 auto.
 elim H1; clear H1; intro H1.
 elim (subReplace3 r H1).
 auto.
 intro H2.
 elim (comSub H2).
 intro; left; eapply subReplace2.
 eauto.
 apply eqFT; apply dotL; apply oneFormSub; auto.
 intro; left; eapply subReplace2.
 eauto.
 apply eqFT; apply dotR; apply oneFormSub; auto.
 auto.
 cut (~ CutFreeProof (CutRule r p1 p2)).
 intro H2.
 elim H2; auto.
 apply notCutFree.
 cut (~ CutFreeProof (CutRule r p1 p2)).
 intro H2; elim H2; auto.
 apply notCutFree.
 elim H1; clear H1; intro H1.
 elim (subReplace3 r H1); intro H2.
 auto.
 left; eapply subReplace2.
 eauto.
 unfold extensionSub in Ex.
 eapply Ex; eauto.
 auto.
Qed.

Lemma subFormulaProperty :
 forall (Atoms : Set) (Gamma1 Gamma2 : Term Atoms) 
   (B C x : Form Atoms) (E : gentzen_extension)
   (p : gentzenSequent E Gamma1 B) (q : gentzenSequent E Gamma2 C),
 extensionSub Atoms E ->
 subProof q p ->
 CutFreeProof p ->
 subFormTerm x Gamma2 \/ subFormula x C ->
 subFormTerm x Gamma1 \/ subFormula x B.

 simple induction 2.
 auto.
 intros T1 T2 T3 A1 A2 A3 p1 p2 p3; intros.
 apply H2. 
 auto.
 apply subFormulaPropertyOne with T3 A3 E p2 p3.
 auto.
 auto.
 apply CutFreeSubProof with T1 A1 p1; auto.
 auto.
Qed.
