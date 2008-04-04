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
Require Import ZArith.
Require Import ZArithRing.
Set Implicit Arguments.
Unset Strict Implicit.
Section PolarityTheorem.
Variable Atoms : Set.
Variable p : Atoms.

Hypothesis Atomseq_dec : forall y : Atoms, {p = y} + {p <> y}.

Fixpoint polarityForm (F : Form Atoms) : Z :=
  match F with
  | At a => match Atomseq_dec a with
            | left _ => 1%Z
            | right _ => 0%Z
            end
  | Slash F1 F2 => (polarityForm F1 - polarityForm F2)%Z
  | Backslash F1 F2 => (polarityForm F2 - polarityForm F1)%Z
  | Dot F1 F2 => (polarityForm F2 + polarityForm F1)%Z
  end.

Fixpoint polarityTerm (T : Term Atoms) : Z :=
  match T with
  | OneForm F => polarityForm F
  | Comma T1 T2 => (polarityTerm T1 + polarityTerm T2)%Z
  end.

Definition extensionPolarity (E : gentzen_extension) :=
  forall T1 T2 : Term Atoms,
  E Atoms T1 T2 -> polarityTerm T1 = polarityTerm T2.

Definition NLEqualPolarity : extensionPolarity NL_Sequent.
 unfold extensionPolarity in |- *.
 simple induction 1.
Defined.

Definition NLPEqualPolarity : extensionPolarity NLP_Sequent.
 unfold extensionPolarity in |- *.
 simple induction 1.
 simpl in |- *.
 intros.
 ring.
Defined.

Definition LEqualPolarity : extensionPolarity L_Sequent.
 unfold extensionPolarity in |- *.
 simple induction 1; simpl in |- *; intros; ring.
Defined.

Definition LPEqualPolarity : extensionPolarity LP_Sequent.
 unfold extensionPolarity in |- *.
 unfold LP_Sequent in |- *.
 unfold add_genExtension in |- *.
 intros T1 T2 H.
 elim H.
 intro.
 apply NLPEqualPolarity.
 assumption.
 intro.
 apply LEqualPolarity.
 assumption.
Defined.

Theorem replacePolarity :
 forall Gamma Gamma' Delta Delta' : Term Atoms,
 replace Gamma Gamma' Delta Delta' ->
 polarityTerm Delta = polarityTerm Delta' ->
 polarityTerm Gamma' = polarityTerm Gamma.

 simple induction 1.
 auto.
 intros.
 simpl in |- *.
 auto with zarith.
 intros.
 simpl in |- *.
 auto with zarith.
Qed.

Theorem equalPolarity :
 forall (Gamma : Term Atoms) (F : Form Atoms) (E : gentzen_extension),
 extensionPolarity E ->
 gentzenSequent E Gamma F -> polarityTerm Gamma = polarityForm F :>Z.
Proof.
 intros Gamma F E H H0.
 elim H0.
 simpl in |- *.
 auto.
 intros Gamma0 A B H1 H2.
 simpl in |- *.
 simpl in H2.
 rewrite <- H2.
 ring.
 intros Gamma0 A B H1 H2.
 simpl in |- *.
 simpl in H2.
 rewrite <- H2.
 ring.
 intros Gamma0 Delta A B H1 H2 H3 H4.
 simpl in |- *.
 rewrite <- H2.
 rewrite <- H4.
 ring.
 intros Delta Gamma0 Gamma' A B C H1 H2 H3 H4 H5.
 rewrite <- H5.
 eapply replacePolarity.
 eauto.
 simpl in |- *.
 rewrite <- H3.
 ring.
 intros Delta Gamma0 Gamma' A B C H1 H2 H3 H4 H5.
 rewrite <- H5.
 eapply replacePolarity.
 eauto.
 simpl in |- *.
 rewrite <- H3.
 ring.
 intros Gamma0 Gamma' A B C H1 H2 H3.
 rewrite <- H3.
 eapply replacePolarity.
 eauto.
 simpl in |- *.
 auto.
 ring.
 intros Delta Gamma0 Gamma' A C H1 H2 H3 H4 H5.
 rewrite <- H5.
 eapply replacePolarity.
 eauto.
 simpl in |- *.
 auto.
 intros Gamma0 Gamma' T1 T2 C H1 H2 H3 H4.
 rewrite <- H4.
 eapply replacePolarity.
 eauto.
 apply H.
 assumption.
Qed.


Theorem AbsPolarity :
 forall (Gamma : Term Atoms) (F : Form Atoms) (E : gentzen_extension),
 gentzenSequent E Gamma F ->
 extensionPolarity E -> polarityTerm Gamma <> polarityForm F -> False.
intros.
elim H1.
eapply equalPolarity; eauto.
Qed.

End PolarityTheorem.


Ltac Polartest at_ eqdec seq :=
  case (AbsPolarity (p:=at_) (Atomseq_dec:=eqdec) seq).



   
