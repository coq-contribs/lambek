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

(* Introduction to sequent calculs as proposed by Moortgat *)

Require Export ReplaceProp.

Set Implicit Arguments.
Unset Strict Implicit.

Section Sequent_calculus.
Variable Atoms : Set.

Section gentzen_def.
 Variable E : gentzen_extension.
(* gentzen presentation using sequents: sequent is a pair (Gamma, A) where 
Gamma is a term and A is a form *)
Inductive gentzenSequent (Atoms : Set) : Term Atoms -> Form Atoms -> Set :=
  | Ax : forall A : Form Atoms, gentzenSequent (OneForm A) A
  | RightSlash :
      forall (Gamma : Term Atoms) (A B : Form Atoms),
      gentzenSequent (Comma Gamma (OneForm B)) A ->
      gentzenSequent Gamma (Slash A B)
  | RightBackSlash :
      forall (Gamma : Term Atoms) (A B : Form Atoms),
      gentzenSequent (Comma (OneForm B) Gamma) A ->
      gentzenSequent Gamma (Backslash B A)
  | RightDot :
      forall (Gamma Delta : Term Atoms) (A B : Form Atoms),
      gentzenSequent Gamma A ->
      gentzenSequent Delta B -> gentzenSequent (Comma Gamma Delta) (Dot A B)
  | LeftSlash :
      forall (Delta Gamma Gamma' : Term Atoms) (A B C : Form Atoms),
      replace Gamma Gamma' (OneForm A) (Comma (OneForm (Slash A B)) Delta) ->
      gentzenSequent Delta B ->
      gentzenSequent Gamma C -> gentzenSequent Gamma' C
  | LeftBackSlash :
      forall (Delta Gamma Gamma' : Term Atoms) (A B C : Form Atoms),
      replace Gamma Gamma' (OneForm A)
        (Comma Delta (OneForm (Backslash B A))) ->
      gentzenSequent Delta B ->
      gentzenSequent Gamma C -> gentzenSequent Gamma' C
  | LeftDot :
      forall (Gamma Gamma' : Term Atoms) (A B C : Form Atoms),
      replace Gamma Gamma' (Comma (OneForm A) (OneForm B))
        (OneForm (Dot A B)) ->
      gentzenSequent Gamma C -> gentzenSequent Gamma' C
  | CutRule :
      forall (Delta Gamma Gamma' : Term Atoms) (A C : Form Atoms),
      replace Gamma Gamma' (OneForm A) Delta ->
      gentzenSequent Delta A ->
      gentzenSequent Gamma C -> gentzenSequent Gamma' C
  | SequentExtension :
      forall (Gamma Gamma' T1 T2 : Term Atoms) (C : Form Atoms),
      E T1 T2 ->
      replace Gamma Gamma' T1 T2 ->
      gentzenSequent Gamma C -> gentzenSequent Gamma' C.


Hint Resolve Ax RightSlash RightBackSlash RightDot: sequent.

  
 
(* Generalisation of the the sequent A=>A where A is a form ,we can easily 
deduce the sequent Gamma=>(deltaTranslation Gamma) for all terms Gamma ...*)
Definition axiomeGeneralisation :
  forall Gamma : Term Atoms, gentzenSequent Gamma (deltaTranslation Gamma).
 intro Gamma.
 elim Gamma.
 intro f.
 apply Ax.
 intros t H t0 H0.
 simpl in |- *.
 apply RightDot.
 assumption.
 assumption.
Defined.


Hint Resolve axiomeGeneralisation: sequent.



(* Some derived properties concerning gentzenSequent *) 
Definition LeftDotSimpl :
  forall A B C : Form Atoms,
  gentzenSequent (Comma (OneForm A) (OneForm B)) C ->
  gentzenSequent (OneForm (Dot A B)) C.

 intros A B C H.
 apply LeftDot with (Comma (OneForm A) (OneForm B)) A B.
 constructor 1.
 assumption. 
Defined.

Definition LeftDotGeneralized :
  forall (T1 T2 : Term Atoms) (C : Form Atoms),
  replaceCommaDot T1 T2 -> gentzenSequent T1 C -> gentzenSequent T2 C. 
 simple induction 1.
 auto.
 intros.
 eapply LeftDot.
 eauto.
 auto.
Defined.

Definition TermToForm :
  forall (T : Term Atoms) (C : Form Atoms),
  gentzenSequent T C -> gentzenSequent (OneForm (deltaTranslation T)) C.

 intros.
 apply LeftDotGeneralized with T.
 apply replaceTranslation.
 assumption.
Defined.

Definition LeftSlashSimpl:
  forall (T : Term Atoms) (A B C : Form Atoms),
  gentzenSequent T B ->
  gentzenSequent (OneForm A) C ->
  gentzenSequent (Comma (OneForm (Slash A B)) T) C.

 intros T A B C H0 H1.
 apply LeftSlash with T (OneForm A) A B.
 constructor 1.
 assumption.
 assumption.
Defined.

Definition LeftBackSlashSimpl :
  forall (T : Term Atoms) (A B C : Form Atoms),
  gentzenSequent T B ->
  gentzenSequent (OneForm A) C ->
  gentzenSequent (Comma T (OneForm (Backslash B A))) C.
 intros T A B C H H0.
 apply LeftBackSlash with T (OneForm A) A B.
 constructor 1.
 assumption.
 assumption.
Defined.

Definition CutRuleSimpl:
  forall (T : Term Atoms) (A C : Form Atoms),
  gentzenSequent T A -> 
  gentzenSequent (OneForm A) C -> 
  gentzenSequent T C.

 intros T A C H H0.
 apply CutRule with T (OneForm A) A.
 constructor 1.
 assumption.
 assumption.
Defined.



Definition DotRightSlash' :
  forall A B C : Form Atoms,
  gentzenSequent (OneForm A) (Slash C B) ->
  gentzenSequent (OneForm (Dot A B)) C.
 intros A B C H.
 apply LeftDotSimpl.
 apply CutRuleSimpl with (Dot (Slash C B) B).
 apply RightDot.
 assumption.
 apply Ax.
 apply LeftDotSimpl.
 apply LeftSlashSimpl; apply Ax.
Defined.


Definition DotRightBackslash' :
  forall A B C : Form Atoms,
  gentzenSequent (OneForm B) (Backslash A C) ->
  gentzenSequent (OneForm (Dot A B)) C.
 intros A B C H.
 apply LeftDotSimpl.
 apply CutRuleSimpl with (Dot A (Backslash A C)).
 apply RightDot.
 apply Ax.
 assumption.
 apply LeftDotSimpl.
 apply LeftBackSlashSimpl; apply Ax.
Defined.


End gentzen_def.
        

(* some definitions concerning extensions*)
Definition LextensionSimpl :
  forall (T1 T2 T3 : Term Atoms) (C : Form Atoms) (E : gentzen_extension),
  genExtends L_Sequent E ->
  gentzenSequent E (Comma T1 (Comma T2 T3)) C ->
  gentzenSequent E (Comma (Comma T1 T2) T3) C.

 intros T1 T2 T3 C E H H'.
 unfold genExtends in H.
 apply
  SequentExtension
   with
     (Comma T1 (Comma T2 T3))
     (Comma T1 (Comma T2 T3))
     (Comma (Comma T1 T2) T3).
 apply H.
 apply L_Intro_lr.
 apply replaceRoot.
 assumption.
Defined.

Definition LextensionSimplDot :
  forall (A B C D : Form Atoms) (E : gentzen_extension),
  genExtends L_Sequent E ->
  gentzenSequent E (OneForm (Dot A (Dot B C))) D ->
  gentzenSequent E (OneForm (Dot (Dot A B) C)) D.

 intros A B C D E H H0.
 apply LeftDotSimpl.
 apply LeftDot with (Comma (Comma (OneForm A) (OneForm B)) (OneForm C)) A B.
 apply replaceLeft.
 apply replaceRoot.
 apply LextensionSimpl.
 assumption.
 apply
  CutRuleSimpl
   with
     (deltaTranslation (Comma (OneForm A) (Comma (OneForm B) (OneForm C)))).
 apply axiomeGeneralisation.
 simpl in |- *.
 assumption.
Defined.


Definition LextensionSimpl' :
  forall (T1 T2 T3 : Term Atoms) (C : Form Atoms) (E : gentzen_extension),
  genExtends L_Sequent E ->
  gentzenSequent E (Comma (Comma T1 T2) T3) C ->
  gentzenSequent E (Comma T1 (Comma T2 T3)) C.

 intros T1 T2 T3 C E H H'.
 apply
  SequentExtension
   with
     (Comma (Comma T1 T2) T3)
     (Comma (Comma T1 T2) T3)
     (Comma T1 (Comma T2 T3)).
 apply H.
 apply L_Intro_rl.
 apply replaceRoot.
 assumption.
Defined.

Definition LextensionSimplDot' :
  forall (A B C D : Form Atoms) (E : gentzen_extension),
  genExtends L_Sequent E ->
  gentzenSequent E (OneForm (Dot (Dot A B) C)) D ->
  gentzenSequent E (OneForm (Dot A (Dot B C))) D.


 intros A B C D E H H0.
 apply LeftDotSimpl.
 apply LeftDot with (Comma (OneForm A) (Comma (OneForm B) (OneForm C))) B C.
 apply replaceRight.
 apply replaceRoot.
 apply LextensionSimpl'.
 assumption.
 apply
  CutRuleSimpl
   with
     (deltaTranslation (Comma (Comma (OneForm A) (OneForm B)) (OneForm C))).
 apply axiomeGeneralisation.
 simpl in |- *.
 assumption.
Defined.



Definition NLPextensionSimpl :
  forall (T1 T2 : Term Atoms) (C : Form Atoms) (E : gentzen_extension),
  genExtends NLP_Sequent E ->
  gentzenSequent E (Comma T1 T2) C -> gentzenSequent E (Comma T2 T1) C.

 intros T1 T2 C E H H0.
 apply SequentExtension with (Comma T1 T2) (Comma T1 T2) (Comma T2 T1).
 unfold genExtends in H.
 apply H.
 constructor 1.
 apply replaceRoot.
 assumption.
Defined.

Definition NLPextensionSimplDot :
  forall (A B C : Form Atoms) (E : gentzen_extension),
  genExtends NLP_Sequent E ->
  gentzenSequent E (OneForm (Dot A B)) C ->
  gentzenSequent E (OneForm (Dot B A)) C.


 intros A B C E H H0.
 apply LeftDotSimpl.
 apply NLPextensionSimpl.
 assumption.
 apply
  CutRuleSimpl with (deltaTranslation (Comma (OneForm A) (OneForm B))).
 apply axiomeGeneralisation.
 simpl in |- *.
 assumption.
Defined.

Definition gentzenExtends :
  forall (E E' : gentzen_extension) (T : Term Atoms) (F : Form Atoms),
  genExtends E E' -> gentzenSequent E T F -> gentzenSequent E' T F.

 intros E E' T F H H0.
 elim H0; intros.
 apply Ax.
 constructor 2.
 assumption.
 constructor 3.
 assumption.
 constructor 4.
 assumption.
 assumption.
 eapply LeftSlash; eauto.
 eapply LeftBackSlash; eauto.
 eapply LeftDot; eauto.
 eapply CutRule; eauto.
 unfold genExtends in H.
 eapply SequentExtension; eauto.
Defined.




(* Some theorems and derived properties *)
(* These definitions can be applied for all gentzen extensions *)

Definition application :
  forall (A B : Form Atoms) (E : gentzen_extension),
  gentzenSequent E (OneForm (Dot (Slash A B) B)) A.
 intros.
 apply LeftDotSimpl.
 apply LeftSlashSimpl; apply Ax.
Defined.

Definition RightSlashDot :
  forall (A B C : Form Atoms) (E : gentzen_extension),
  gentzenSequent E (OneForm (Dot A C)) B ->
  gentzenSequent E (OneForm A) (Slash B C).
 intros A B C E H.
 apply RightSlash.
 apply
  CutRuleSimpl with (deltaTranslation (Comma (OneForm A) (OneForm C))).
 apply axiomeGeneralisation.
 simpl in |- *.
 assumption.
Defined.

Definition application' :
  forall (A B : Form Atoms) (E : gentzen_extension),
  gentzenSequent E (OneForm (Dot B (Backslash B A))) A.
 intros.
 apply LeftDotSimpl.
 apply LeftBackSlashSimpl; apply Ax.
Defined.

Definition RightBackslashDot :
  forall (A B C : Form Atoms) (E : gentzen_extension),
  gentzenSequent E (OneForm (Dot B A)) C ->
  gentzenSequent E (OneForm A) (Backslash B C).

 intros A B C E H.
 apply RightBackSlash.
 apply
  CutRuleSimpl with (deltaTranslation (Comma (OneForm B) (OneForm A))).
 apply axiomeGeneralisation.
 simpl in |- *.
 assumption.
Defined.

Definition coApplication :
  forall (A B : Form Atoms) (E : gentzen_extension),
  gentzenSequent E (OneForm A) (Slash (Dot A B) B).

 intros.
 apply RightSlash.
 apply RightDot; apply Ax.
Defined.

Definition coApplication' :
  forall (A B : Form Atoms) (E : gentzen_extension),
  gentzenSequent E (OneForm A) (Backslash B (Dot B A)).
 intros.
 apply RightBackSlash.
 apply RightDot; apply Ax.
Defined.

Definition monotonicity :
  forall (A B C D : Form Atoms) (E : gentzen_extension),
  gentzenSequent E (OneForm A) B ->
  gentzenSequent E (OneForm C) D ->
  gentzenSequent E (OneForm (Dot A C)) (Dot B D).

 intros.
 apply LeftDotSimpl.
 apply RightDot; assumption.
Defined.

Definition isotonicity :
  forall (A B C : Form Atoms) (E : gentzen_extension),
  gentzenSequent E (OneForm A) B ->
  gentzenSequent E (OneForm (Slash A C)) (Slash B C).
 intros.
 apply RightSlash.
 apply CutRuleSimpl with A.
 apply LeftSlashSimpl; apply Ax.
 assumption.
Defined.

Definition isotonicity' :
  forall (A B C : Form Atoms) (E : gentzen_extension),
  gentzenSequent E (OneForm A) B ->
  gentzenSequent E (OneForm (Backslash C A)) (Backslash C B).
intros.
apply RightBackSlash.
apply CutRuleSimpl with A.
apply LeftBackSlashSimpl; apply Ax.
assumption.
Defined.

Definition antitonicity :
  forall (A B C : Form Atoms) (E : gentzen_extension),
  gentzenSequent E (OneForm A) B ->
  gentzenSequent E (OneForm (Slash C B)) (Slash C A).
 intros A B C E H.
 apply RightSlash.
 apply CutRuleSimpl with (Dot (Slash C B) B).
 apply RightDot.
 apply Ax.
 assumption.
 apply application.
Defined.

Definition antitonicity' :
  forall (A B C : Form Atoms) (E : gentzen_extension),
  gentzenSequent E (OneForm A) B ->
  gentzenSequent E (OneForm (Backslash B C)) (Backslash A C).
 intros A B C E H.
 apply RightBackSlash.
 apply CutRuleSimpl with (Dot B (Backslash B C)).
 apply RightDot.
 assumption.
 apply Ax.
 apply application'.
Defined.

Definition lifting :
  forall (A B C : Form Atoms) (E : gentzen_extension),
  gentzenSequent E (OneForm A) (Slash B (Backslash A B)).
 intros A B C E.
 apply RightSlash.
 apply CutRuleSimpl with (Dot A (Backslash A B)).
 apply RightDot; apply Ax.
 apply application'.
Defined.

Definition lifting' :
  forall (A B C : Form Atoms) (E : gentzen_extension),
  gentzenSequent E (OneForm A) (Backslash (Slash B A) B).

 intros A B C E.
 apply RightBackSlash.
 apply CutRuleSimpl with (Dot (Slash B A) A).
 apply RightDot; apply Ax.
 apply application.
Defined.

(*These definitions can be applied iff associativity is supported
 by our logical system *)

Definition mainGeach :
  forall (A B C : Form Atoms) (E : gentzen_extension),
  genExtends L_Sequent E ->
  gentzenSequent E (OneForm (Slash A B)) (Slash (Slash A C) (Slash B C)).

 intros A B C E H.
 apply RightSlash.
 apply RightSlash.
 apply LextensionSimpl.
 assumption.
 apply CutRuleSimpl with (Dot (Slash A B) B).
 apply RightDot.
 apply Ax.
 apply LeftSlashSimpl; apply Ax.
 apply application.
Defined.

Definition mainGeach' :
  forall (A B C : Form Atoms) (E : gentzen_extension),
  genExtends L_Sequent E ->
  gentzenSequent E (OneForm (Backslash B A))
    (Backslash (Backslash C B) (Backslash C A)).
 intros A B C E H.
 apply RightBackSlash.
 apply RightBackSlash.
 apply LextensionSimpl'.
 assumption.
 apply CutRuleSimpl with (Dot B (Backslash B A)).
 apply RightDot.
 apply LeftBackSlashSimpl; apply Ax.
 apply Ax.
 apply application'.
Defined.

Definition secondaryGeach :
  forall (A B C : Form Atoms) (E : gentzen_extension),
  genExtends L_Sequent E ->
  gentzenSequent E (OneForm (Slash B C)) (Backslash (Slash A B) (Slash A C)).
 intros A B C E H.
 apply RightBackSlash.
 apply RightSlash.
 apply LextensionSimpl.
 assumption.
 apply CutRuleSimpl with (Dot (Slash A B) B).
 apply RightDot.
 apply Ax.
 apply LeftSlashSimpl; apply Ax.
 apply application.
Defined.

Definition secondaryGeach' :
  forall (A B C : Form Atoms) (E : gentzen_extension),
  genExtends L_Sequent E ->
  gentzenSequent E (OneForm (Backslash C B))
    (Slash (Backslash C A) (Backslash B A)).

 intros A B C E H.
 apply RightSlash.
 apply RightBackSlash.
 apply LextensionSimpl'.
 assumption.
 apply CutRuleSimpl with (Dot B (Backslash B A)).
 apply RightDot.
 apply LeftBackSlashSimpl; apply Ax.
 apply Ax.
 apply application'.
Defined.

Definition composition :
  forall (A B C : Form Atoms) (E : gentzen_extension),
  genExtends L_Sequent E ->
  gentzenSequent E (OneForm (Dot (Slash A B) (Slash B C))) (Slash A C).
 intros A B C E H.
 apply
  CutRuleSimpl with (Dot (Slash (Slash A C) (Slash B C)) (Slash B C)).
 apply monotonicity.
 apply mainGeach.
 assumption.
 apply Ax.
 apply application.
Defined.

Definition composition' :
  forall (A B C : Form Atoms) (E : gentzen_extension),
  genExtends L_Sequent E ->
  gentzenSequent E (OneForm (Dot (Backslash C B) (Backslash B A)))
    (Backslash C A).

 intros A B C E H.
 apply
  CutRuleSimpl
   with (Dot (Slash (Backslash C A) (Backslash B A)) (Backslash B A)).
 apply monotonicity.
 apply secondaryGeach'.
 assumption.
 apply Ax.
 apply application.
Defined.

Definition restructuring :
  forall (A B C : Form Atoms) (E : gentzen_extension),
  genExtends L_Sequent E ->
  gentzenSequent E (OneForm (Slash (Backslash A B) C))
    (Backslash A (Slash B C)).

 intros A B C E H.
 apply RightBackSlash.
 apply RightSlash.
 apply LextensionSimpl.
 assumption.
 apply CutRuleSimpl with (Dot A (Backslash A B)).
 apply RightDot.
 apply Ax.
 apply LeftSlashSimpl; apply Ax.
 apply application'.
Defined.

Definition restructuring' :
  forall (A B C : Form Atoms) (E : gentzen_extension),
  genExtends L_Sequent E ->
  gentzenSequent E (OneForm (Backslash A (Slash B C)))
    (Slash (Backslash A B) C).

 intros A B C E H.
 apply RightSlash.
 apply RightBackSlash.
 apply LextensionSimpl'.
 assumption.
 apply CutRuleSimpl with (Dot (Slash B C) C).
 apply RightDot.
 apply LeftBackSlashSimpl; apply Ax.
 apply Ax.
 apply application.
Defined.

Definition currying :
  forall (A B C : Form Atoms) (E : gentzen_extension),
  genExtends L_Sequent E ->
  gentzenSequent E (OneForm (Slash A (Dot B C))) (Slash (Slash A C) B).
 intros.
 apply RightSlashDot.
 apply RightSlashDot.
 apply LextensionSimplDot.
 assumption.
 apply application.
Defined.

Definition currying' :
  forall (A B C : Form Atoms) (E : gentzen_extension),
  genExtends L_Sequent E ->
  gentzenSequent E (OneForm (Slash (Slash A C) B)) (Slash A (Dot B C)).
 intros A B C E H.
 apply RightSlashDot.
 apply LextensionSimplDot'.
 assumption.
 apply CutRuleSimpl with (Dot (Slash A C) C).
 apply monotonicity.
 apply application.
 apply Ax.
 apply application.
Defined.

Definition decurrying :
  forall (A B C : Form Atoms) (E : gentzen_extension),
  genExtends L_Sequent E ->
  gentzenSequent E (OneForm (Backslash (Dot A B) C))
    (Backslash B (Backslash A C)).
 intros.
 apply RightBackslashDot.
 apply RightBackslashDot.
 apply LextensionSimplDot'.
 assumption.
 apply application'.
Defined.

Definition decurrying' :
  forall (A B C : Form Atoms) (E : gentzen_extension),
  genExtends L_Sequent E ->
  gentzenSequent E (OneForm (Backslash B (Backslash A C)))
    (Backslash (Dot A B) C).
 intros A B C E H.
 apply RightBackslashDot.
 apply LextensionSimplDot.
 assumption.
 apply CutRuleSimpl with (Dot A (Backslash A C)).
 apply monotonicity.
 apply Ax.
 apply application'.
 apply application'.
Defined.

(* Theorem for systems that support commutativity :if its extension 
extends NLP_Sequent *)

Definition permutation :
  forall (A B C : Form Atoms) (E : gentzen_extension),
  genExtends NLP_Sequent E ->
  gentzenSequent E (OneForm A) (Backslash B C) ->
  gentzenSequent E (OneForm B) (Backslash A C).
 intros A B C E H H0.
 apply RightBackslashDot.
 apply NLPextensionSimplDot.
 assumption.
 apply CutRuleSimpl with (Dot B (Backslash B C)).
 apply monotonicity.
 apply Ax.
 assumption.
 apply application'.
Defined.

Definition exchange :
  forall (A B : Form Atoms) (E : gentzen_extension),
  genExtends NLP_Sequent E ->
  gentzenSequent E (OneForm (Slash A B)) (Backslash B A).
 intros.
 apply RightBackslashDot.
 apply NLPextensionSimplDot.
 assumption.
 apply application.
Defined.

Definition exchange' :
  forall (A B : Form Atoms) (E : gentzen_extension),
  genExtends NLP_Sequent E ->
  gentzenSequent E (OneForm (Backslash B A)) (Slash A B).
 intros.
 apply RightSlashDot.
 apply NLPextensionSimplDot.
 assumption.
 apply application'.
Defined.

Definition preposing :
  forall (A B : Form Atoms) (E : gentzen_extension),
  genExtends NLP_Sequent E ->
  gentzenSequent E (OneForm A) (Slash B (Slash B A)).
 intros.
 apply RightSlashDot.
 apply NLPextensionSimplDot.
 assumption.
 apply application.
Defined.

Definition postposing :
  forall (A B : Form Atoms) (E : gentzen_extension),
  genExtends NLP_Sequent E ->
  gentzenSequent E (OneForm A) (Backslash (Backslash A B) B).
 intros.
 apply RightBackslashDot.
 apply NLPextensionSimplDot.
 assumption.
 apply application'.
Defined.


(* For systems that support both commutativity and associativity ..*)

Definition mixedComposition :
  forall (A B C : Form Atoms) (E : gentzen_extension),
  genExtends LP_Sequent E ->
  gentzenSequent E (OneForm (Dot (Slash A B) (Backslash C B)))
    (Backslash C A).
 intros A B C E H.
 apply NLPextensionSimplDot.
 apply LPextendsNLP.
 assumption.
 apply RightBackslashDot.
 apply LextensionSimplDot'.
 apply LPextendsL.
 assumption.
 apply CutRuleSimpl with (Dot B (Slash A B)).
 apply monotonicity.
 apply application'.
 apply Ax.
 apply NLPextensionSimplDot.
 apply LPextendsNLP.
 assumption.
 apply application.
Defined.

Definition mixedComposition' :
  forall (A B C : Form Atoms) (E : gentzen_extension),
  genExtends LP_Sequent E ->
  gentzenSequent E (OneForm (Dot (Slash B C) (Backslash B A))) (Slash A C).


 intros A B C E H.
 apply NLPextensionSimplDot.
 apply LPextendsNLP.
 assumption.
 apply RightSlashDot.
 apply LextensionSimplDot.
 apply LPextendsL.
 assumption.
 apply CutRuleSimpl with (Dot (Backslash B A) B).
 apply monotonicity.
 apply Ax.
 apply application.
 apply NLPextensionSimplDot.
 apply LPextendsNLP.
 assumption.
 apply application'.
Defined.
                                              
End Sequent_calculus.

Hint Resolve Ax RightSlash RightBackSlash RightDot axiomeGeneralisation
  application RightSlashDot application' RightBackslashDot coApplication
  coApplication' monotonicity isotonicity isotonicity' antitonicity
  antitonicity' lifting lifting' mainGeach mainGeach' secondaryGeach
  secondaryGeach' composition composition' restructuring restructuring'
  currying currying' decurrying decurrying' permutation exchange exchange'
  preposing postposing mixedComposition mixedComposition': sequent.