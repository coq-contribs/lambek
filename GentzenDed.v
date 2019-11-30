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
Require Export NaturalDeduction.

Set Implicit Arguments.


(* these definitions will help us to prove that natural deduction is equivalent 
to gentzen calculus *)

Definition replaceGentzen :
  forall (Atoms: Set)(Gamma Gamma' Delta Delta' : Term Atoms) 
  (E : gentzen_extension),
  replace Gamma Gamma' Delta Delta' ->
  gentzenSequent E Delta' (deltaTranslation Delta) ->
  gentzenSequent E Gamma' (deltaTranslation Gamma).
 simple induction 1.
 auto.
 intros.
 simpl in |- *.
 apply RightDot; auto.
 apply axiomeGeneralisation.
 intros.
 simpl in |- *.
 apply RightDot.
 apply axiomeGeneralisation.
 auto.
Defined.

Definition replaceGentzen' :
  forall (Atoms:Set)(Gamma Gamma' Delta Delta' : Term Atoms) 
 (C : Form Atoms) (E : gentzen_extension),
  replace Gamma Gamma' Delta Delta' ->
  gentzenSequent E Delta' (deltaTranslation Delta) ->
  gentzenSequent E Gamma C -> gentzenSequent E Gamma' C.
 intros.
 apply CutRuleSimpl with (deltaTranslation Gamma).
 eapply replaceGentzen; eauto.
 apply TermToForm.
 assumption.
Defined.                                             

Definition replaceNatDed :
  forall (Atoms:Set) (Gamma Gamma' Delta Delta' : Term Atoms)
  (E : gentzen_extension),
  replace Gamma Gamma' Delta Delta' ->
  natDed E Delta' (deltaTranslation Delta) ->
  natDed E Gamma' (deltaTranslation Gamma). 
 simple induction 1.
 intros.
 assumption.
 intros.
 simpl in |- *.
 apply DotIntro.
 auto.
 apply axiomGen.
 intros.
 simpl in |- *.
 apply DotIntro.
 apply axiomGen.
 exact (H0 H1).
Defined.

Section cutNaturalDeduction.

Definition condCutExt (X : gentzen_extension) :=
  forall (Atoms:Set)(T T1 T2 T3 : Term Atoms) (A : Form Atoms),
  X _ T1 T2 ->
  replace T2 T (OneForm A) T3 ->
  { T' : Term Atoms & (X _ T' T * replace T1 T' (OneForm A) T3)%type }.
       


Definition conditionOKNLP : condCutExt NLP_Sequent.
 unfold condCutExt .
 intros Atoms T T1 T2 T3 A H.
 elim H.
 intros Delta1 Delta2 H0.
 elim (replace_inv2 H0); clear H0; intro H0; elim H0;
 clear H0; intros x H0; elim H0; clear H0; intros H0 H1.
 split with (Comma Delta1 x).
 split.
 rewrite H1.
 constructor 1.
 apply replaceRight; auto.
 split with (Comma x Delta2).
 split.
 rewrite H1.
 constructor 1.
 apply replaceLeft; auto.
Defined.

Definition conditionOKL : condCutExt L_Sequent.
 unfold condCutExt in |- *.
 intros Atoms T T1 T2 T3 A H.
 elim H.
 intros Delta1 Delta2 Delta3 H0.
 elim (replace_inv2 H0); clear H0; intro H0; elim H0; clear H0;
 intros x H0; elim H0; clear H0; intros H0 H1.
 elim (replace_inv2 H0); clear H0; intro H0; elim H0; clear H0; intros x0 H0;
 elim H0; clear H0; intros H0 H2.
 split with (Comma x0 (Comma Delta2 Delta3)).
 split.
 rewrite H1.
 rewrite H2.
 constructor 1.
 apply replaceLeft.
 auto.
 split with (Comma Delta1 (Comma x0 Delta3)).
 split.
 rewrite H1.
 rewrite H2.
 constructor 1.
 apply replaceRight.
 apply replaceLeft; auto.
 split with (Comma Delta1 (Comma Delta2 x)).
 split.
 rewrite H1.
 constructor 1.
 apply replaceRight; apply replaceRight; auto.
 intros Delta1 Delta2 Delta3 H0.
 elim (replace_inv2 H0); clear H0; intro H0; elim H0; clear H0; intros x H0;
  elim H0; clear H0; intros H0 H1.
 split with (Comma (Comma x Delta2) Delta3).
 split.
 rewrite H1.
 constructor 2.
 apply replaceLeft; apply replaceLeft; auto. 
 elim (replace_inv2 H0); clear H0; intro H0; elim H0; clear H0; intros x0 H0;
  elim H0; clear H0; intros H0 H2.
 split with (Comma (Comma Delta1 x0) Delta3).
 split.
 rewrite H1.
 rewrite H2.
 constructor 2.
 apply replaceLeft; apply replaceRight; auto.
 split with (Comma (Comma Delta1 Delta2) x0).
 split.
 rewrite H1.
 rewrite H2.
 constructor 2.
 apply replaceRight; auto.
Defined.

Definition condAddExt :
  forall X Y : gentzen_extension,
  condCutExt X ->
  condCutExt Y -> 
  condCutExt (add_genExtension X Y).

 intros X Y.
 unfold condCutExt in |- *.
 intros H H0.
 intros Atoms T T1 T2 T3 A H1 R.
 unfold add_genExtension in H1.
 elim H1; clear H1; intro H1.
 elim (H _ T T1 T2 T3 A H1 R).
 intros x H2.
 elim H2; clear H2; intros.
 split with x.
 split.
 unfold add_genExtension in |- *.
 left; auto.
 auto.
 elim (H0 _ T T1 T2 T3 A H1 R).
 intros x H2.
 elim H2; clear H2; intros.
 split with x.
 split.
 unfold add_genExtension in |- *.
 right; auto.
 auto.
Defined.

Definition CutNatDed:
  forall (Atoms: Set)(X : gentzen_extension) (Gamma Delta : Term Atoms)
    (C A : Form Atoms),
  condCutExt X ->
  natDed X Delta A ->
  natDed X Gamma C ->
  forall Gamma' : Term Atoms,
  replace Gamma Gamma' (OneForm A) Delta -> natDed X Gamma' C.
 intros At X Gamma Delta C A Cx H H0.
 elim H0; intros.
 elim (replace_inv1 H1).
 intros H2 H3.
 rewrite H2; rewrite <- H3.
 auto.
 apply SlashIntro.
 apply H1.
 apply replaceLeft; auto.
 apply BackSlashIntro.
 apply H1.
 apply replaceRight; assumption.
 elim (replace_inv2 H3); clear H3; intro H3; elim H3; clear H3; intros x H3;
  elim H3; clear H3; intros H3 H4.
 rewrite H4.
 apply DotIntro.
 apply H1; assumption.
 assumption.
 rewrite H4.
 apply DotIntro.
 auto.
 apply H2; auto.
 elim (replace_inv2 H3); clear H3; intro H3; elim H3; clear H3; intros x H3;
  elim H3; clear H3; intros H3 H4.
 rewrite H4.
 apply SlashElim with B.
 apply H1; auto.
 auto.
 rewrite H4.
 apply SlashElim with B.
 auto.
 apply H2; auto.
 elim (replace_inv2 H3); clear H3; intro H3; elim H3; clear H3; intros x H3;
  elim H3; clear H3; intros H3 H4.
 rewrite H4.
 apply BackSlashElim with B.
 apply H1; auto.
 auto.
 rewrite H4.
 apply BackSlashElim with B.
 auto.
 apply H2; auto.
 elim (doubleReplace r H3); intro H4; elim H4; clear H4; intros x H4; elim H4;
  clear H4; intros H4 H5.
 eapply DotElim.
 eauto. 
 auto.
 apply H2; auto.
 eapply DotElim.
 eauto.
 apply H1; auto.
 auto.
 unfold condCutExt in Cx.
 elim (doubleReplace r H2); intro H3; elim H3; clear H3; intros T H3; elim H3;
  clear H3; intros H3 H4.
 eapply NatExt.
 eauto.
 eauto.
 apply H1; assumption.
 elim (Cx _ T T1 T2 Delta A n H3).
 intros x H5.
 elim H5; clear H5; intros.
 elim (replaceSameP H4 x).
 intros x0 H5.
 elim H5; clear H5; intros.
 eapply NatExt.
 eauto.
 eauto.
 apply H1.
 eapply replaceTrans; eauto.
Defined.

Definition composition :
  forall (Atoms:Set)(X : gentzen_extension) (T : Term Atoms) (F1 F2 : Form Atoms),
  condCutExt X ->
  natDed X T F1 ->
  natDed X (OneForm F1) F2 -> natDed X T F2.

 intros.
 apply CutNatDed with (OneForm F1) T F1.
 auto.
 auto.
 auto.
 constructor 1.
Defined.

End cutNaturalDeduction.

Section EquivalenceNaturalGentzen.

Definition natDedToGentzen :
  forall (Atoms:Set)(T : Term Atoms) (C : Form Atoms) (E : gentzen_extension),
  natDed E T C -> gentzenSequent E T C.
 simple induction 1.
 constructor 1.
 intros.
 apply RightSlash.
 assumption.
 intros.
 apply RightBackSlash.
 assumption.
 intros.
 apply RightDot; assumption.
 intros Gamma Delta A B.
 intros.
 apply CutRule with Gamma (Comma (OneForm (Slash A B)) Delta) (Slash A B).
 apply replaceLeft.
 apply replaceRoot.
 assumption.
 apply LeftSlashSimpl.
 assumption.
 constructor 1.
 intros Gamma Delta A B.
 intros.
 apply
  CutRule with Delta (Comma Gamma (OneForm (Backslash B A))) (Backslash B A).
 apply replaceRight.
 apply replaceRoot.
 assumption.
 apply LeftBackSlashSimpl.
 assumption.
 apply Ax.
 intros.
 eapply replaceGentzen'; eauto.
 intros.
 eapply SequentExtension; eauto.
Defined.


Definition gentzenToNatDed:
  forall (Atoms:Set)(T : Term Atoms) (C : Form Atoms) (E : gentzen_extension),
  condCutExt E -> 
  gentzenSequent E T C ->
  natDed E T C.

 simple induction 2.
 constructor 1.
 intros.
 constructor 2; assumption.
 intros; constructor 3; assumption.
 intros; constructor 4; assumption.
 intros Delta Gamma; intros.
 apply composition with (deltaTranslation Gamma).
 auto.
 eapply replaceNatDed.
 eauto.
 simpl in |- *.
 eapply SlashElim.
 eapply Axi.
 assumption.
 apply TermToFormDed.
 assumption.
 intros Delta Gamma; intros.
 apply composition with (deltaTranslation Gamma).
 auto.
 eapply replaceNatDed.
 eauto.
 simpl in |- *.
 eapply BackSlashElim.
 eauto.
 constructor 1.
 apply TermToFormDed; assumption.
 intro Gamma; intros.
 apply composition with (deltaTranslation Gamma).
 auto.
 eapply replaceNatDed.
 eauto.
 simpl in |- *; constructor 1.
 apply TermToFormDed; assumption.
 intros Delta Gamma; intros.
 apply composition with (deltaTranslation Gamma).
 auto.
 eapply replaceNatDed.
 eauto.
 simpl in |- *; assumption.
 apply TermToFormDed.
 assumption.
 intros.
 eapply NatExt; eauto.
Defined.

End EquivalenceNaturalGentzen.

