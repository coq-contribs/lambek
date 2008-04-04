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

Section arrowGen.

Variable Atoms : Set.

(* Auxiliary lemma that will be used to prove that gentzen presentation 
   is equivalent to the axiomatic one *)

Definition replace_arrow :
  forall (T1 T2 Gamma Gamma' : Term Atoms) (X : arrow_extension),
  replace Gamma Gamma' T1 T2 ->
  arrow X (deltaTranslation T2) (deltaTranslation T1) ->
  arrow X (deltaTranslation Gamma') (deltaTranslation Gamma).
 simple induction 1.
 intros; auto with ctl.
 intros.
 simpl in |- *.
 apply Dot_mono_left.
 auto.
 intros.
 simpl in |- *.
 apply Dot_mono_right.
 auto.
Defined.

Definition replace_arrow' :
  forall (T1 T2 Gamma Gamma' : Term Atoms) (X : arrow_extension)
    (C : Form Atoms),
  replace Gamma Gamma' T1 T2 ->
  arrow X (deltaTranslation T2) (deltaTranslation T1) ->
  arrow X (deltaTranslation Gamma) C -> arrow X (deltaTranslation Gamma') C.
 intros T1 T2 Gamma.
 intros.
 apply comp with (deltaTranslation Gamma).
 eapply replace_arrow; eauto.
 assumption.
Defined.


(* from axiomatic presentation to sequent calculus *)

Definition arrowToGentzenExt (X : arrow_extension)
  (E : gentzen_extension) :=
  forall A B : Form Atoms, X Atoms A B -> gentzenSequent E (OneForm A) B.

Definition NLToNL_Sequent : arrowToGentzenExt NL NL_Sequent.
 unfold arrowToGentzenExt in |- *.
 simple induction 1.
Defined.

Definition NLPToNLP_Sequent : arrowToGentzenExt NLP NLP_Sequent.
 unfold arrowToGentzenExt in |- *.
 simple induction 1.
 intros.
 apply NLPextensionSimplDot.
 apply genExtendsRef.
 apply Ax.
Defined.

Definition LToL_Sequent : arrowToGentzenExt L L_Sequent.
 unfold arrowToGentzenExt in |- *.
 simple induction 1.
 intros.
 apply LextensionSimplDot'.
 apply genExtendsRef.
 apply Ax.
 intros.
 apply LextensionSimplDot.
 apply genExtendsRef.
 apply Ax.
Defined.

Definition LPToLP_Sequent : arrowToGentzenExt LP LP_Sequent.
 unfold arrowToGentzenExt in |- *.
 intros A B H.
 unfold LP in H.
 unfold add_extension in H.
 elim H.
 intro.
 apply gentzenExtends with NLP_Sequent.
 apply LPextendsNLP.
 apply genExtendsRef.
 apply NLPToNLP_Sequent.
 assumption.
 intro.
 apply gentzenExtends with L_Sequent.
 apply LPextendsL.
 apply genExtendsRef.
 apply LToL_Sequent.
 assumption.
Defined.



Definition arrowToGentzen :
  forall (A B : Form Atoms) (E : gentzen_extension) (X : arrow_extension),
  arrowToGentzenExt X E ->
  arrow X A B -> gentzenSequent E (OneForm A) B.
 intros A B E X H0 H.
 elim H.
 apply Ax.
 intros.
 eapply CutRuleSimpl; eauto.
 intros.
 apply RightSlashDot.
 assumption.
 intros.
 apply DotRightSlash'.
 assumption.
 intros.
 apply RightBackslashDot.
 assumption.
 intros.
 apply DotRightBackslash'.
 assumption.
 intros.
 unfold arrowToGentzenExt in H0.
 auto.
Defined.


(* particular cases for NLP, L; LP and NL systems *)
Definition arrowToGentzenNL :
  forall A B : Form Atoms,
  arrow NL A B -> gentzenSequent NL_Sequent (OneForm A) B.
 intros.
 apply arrowToGentzen with NL.
 apply NLToNL_Sequent.
 assumption.
Defined.


Definition arrowToGentzenNLP :
  forall A B : Form Atoms,
  arrow NLP A B -> gentzenSequent NLP_Sequent (OneForm A) B.
 intros.
 apply arrowToGentzen with NLP.
 apply NLPToNLP_Sequent.
 assumption.
Defined.

Definition arrowToGentzenL :
  forall A B : Form Atoms,
  arrow L A B -> gentzenSequent L_Sequent (OneForm A) B.
 intros.
 apply arrowToGentzen with L.
 apply LToL_Sequent.
 assumption.
Defined.


Definition arrowToGentzenLP :
  forall A B : Form Atoms,
  arrow LP A B -> gentzenSequent LP_Sequent (OneForm A) B.

 intros.
 apply arrowToGentzen with LP.
 apply LPToLP_Sequent.
 assumption.
Defined.




(* from sequent calculus to axiomatic presentation *)

(* condition on structural rules *)
Definition gentzenToArrowExt (E : gentzen_extension)
  (X : arrow_extension) :=
  forall T1 T2 : Term Atoms,
  E Atoms T1 T2 -> X Atoms (deltaTranslation T2) (deltaTranslation T1).



Definition NL_SequentToNL : gentzenToArrowExt NL_Sequent NL.
 unfold gentzenToArrowExt in |- *.
 intros.
 case H.
Defined.

Definition NLP_SequentToNLP : gentzenToArrowExt NLP_Sequent NLP.
 unfold gentzenToArrowExt in |- *.
 simple induction 1.
 simpl in |- *.
 constructor 1.
Defined.

Definition L_SequentToL : gentzenToArrowExt L_Sequent L.
 unfold gentzenToArrowExt in |- *.
 simple induction 1.
 simpl in |- *.
 constructor 2.
 simpl in |- *.
 constructor 1.
Defined.

Definition LP_SequentToLP : gentzenToArrowExt LP_Sequent LP.
 unfold gentzenToArrowExt in |- *. 
 simple induction 1.
 unfold LP in |- *.
 unfold add_extension in |- *.
 intro.
 left.
 apply NLP_SequentToNLP.
 assumption.
 intro.
 unfold LP in |- *.
 unfold add_extension in |- *.
 right.
 apply L_SequentToL.
 assumption.
Defined.
             

Definition gentzenToArrow :
  forall (T : Term Atoms) (A : Form Atoms) (X : arrow_extension)
    (E : gentzen_extension),
  gentzenToArrowExt E X ->
  gentzenSequent E T A -> arrow X (deltaTranslation T) A.
 intros T A X E H0 H.
 elim H.
 intros; simpl in |- *; auto with ctl.
 intros; simpl in |- *; auto with ctl.
 intros; simpl in |- *; auto with ctl.
 intros; simpl in |- *; apply Dot_mono; assumption.
 intros Delta Gamma.
 intros.
 eapply replace_arrow'; eauto.
 simpl in |- *.
 apply beta'.
 apply Slash_antimono_right.
 assumption.
 intros Delta Gamma.
 intros.
 eapply replace_arrow'; eauto.
 simpl in |- *.
 apply gamma'.
 apply Backslash_antimono_left.
 assumption.
 intro Gamma; intros.
 eapply replace_arrow'; eauto.
 simpl in |- *.
 apply one.
 intros Delta Gamma; intros.
 eapply replace_arrow'; eauto.
 intros.
 eapply replace_arrow'; eauto.
 unfold gentzenToArrowExt in H0.
 constructor 7.
 auto.
Defined.

Definition NLGentzenToArrow :
  forall (T : Term Atoms) (A : Form Atoms),
  gentzenSequent NL_Sequent T A -> arrow NL (deltaTranslation T) A.

 intros.
 eapply gentzenToArrow.
 apply NL_SequentToNL.
 assumption.
Defined.

Definition NLPGentzenToArrow :
  forall (T : Term Atoms) (A : Form Atoms),
  gentzenSequent NLP_Sequent T A -> arrow NLP (deltaTranslation T) A.
 intros.
 eapply gentzenToArrow.
 apply NLP_SequentToNLP.
 assumption.
Defined.

Definition LGentzenToArrow :
  forall (T : Term Atoms) (A : Form Atoms),
  gentzenSequent L_Sequent T A -> arrow L (deltaTranslation T) A.
 intros.
 eapply gentzenToArrow.
 apply L_SequentToL.
 assumption.
Defined.

Definition LPGentzenToArrow :
  forall (T : Term Atoms) (A : Form Atoms),
  gentzenSequent LP_Sequent T A -> arrow LP (deltaTranslation T) A.

 intros.
 eapply gentzenToArrow.
 apply LP_SequentToLP.
 assumption.
Defined.



End arrowGen.