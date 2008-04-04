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


(* Natural Deduction presentation of Lambek calculus
 using Introduction and Elimination rules *)

Require Export ReplaceProp.
Set Implicit Arguments.
Unset Strict Implicit.
Section Natural_Deduction.

Variable Atoms : Set.


Section deduction_def.

(* we consider the same type of extension that we've seen in 
 gentzen calculus *)
Variable N : gentzen_extension.

(* definition of the inference rules of this system *)
Inductive natDed (Atoms : Set) : Term Atoms -> Form Atoms -> Set :=
  | Axi : forall A : Form Atoms, natDed (OneForm A) A
  | SlashIntro :
      forall (Gamma : Term Atoms) (A B : Form Atoms),
      natDed (Comma Gamma (OneForm B)) A ->
      natDed Gamma (Slash A B)
  | BackSlashIntro :
      forall (Gamma : Term Atoms) (A B : Form Atoms),
      natDed (Comma (OneForm B) Gamma) A ->
      natDed Gamma (Backslash B A)
  | DotIntro :
      forall (Gamma Delta : Term Atoms) (A B : Form Atoms),
      natDed Gamma A ->
      natDed Delta B ->
      natDed (Comma Gamma Delta) (Dot A B)
  | SlashElim :
      forall (Gamma Delta : Term Atoms) (A B : Form Atoms),
      natDed Gamma (Slash A B) ->
      natDed Delta B -> natDed (Comma Gamma Delta) A
  | BackSlashElim :
      forall (Gamma Delta : Term Atoms) (A B : Form Atoms),
      natDed Gamma B ->
      natDed Delta (Backslash B A) ->
      natDed (Comma Gamma Delta) A
  | DotElim :
      forall (Gamma Gamma' Delta : Term Atoms) (A B C : Form Atoms),
      replace Gamma Gamma' (Comma (OneForm A) (OneForm B)) Delta ->
      natDed Delta (Dot A B) ->
      natDed Gamma C -> natDed Gamma' C
  | NatExt :
      forall (Gamma Gamma' T1 T2 : Term Atoms) (C : Form Atoms),
      N T1 T2 ->
      replace Gamma Gamma' T1 T2 ->
      natDed Gamma C -> natDed Gamma' C. 

Definition axiomGen :
  forall T : Term Atoms, natDed T (deltaTranslation T).
 simple induction T.
 simpl in |- *.
 constructor 1.
 intros.
 simpl in |- *.
 apply DotIntro; assumption.
Defined.

Definition DotElimGeneralized :
  forall (T1 T2 : Term Atoms) (C : Form Atoms),
  replaceCommaDot T1 T2 ->
  natDed T1 C ->
  natDed T2 C.

 simple induction 1.
 auto.
 intros.
 eapply DotElim.
 eauto.
 constructor 1.
 auto.
Defined.

Definition TermToFormDed :
  forall (T : Term Atoms) (C : Form Atoms),
  natDed T C -> natDed (OneForm (deltaTranslation T)) C.
 intros.
 apply DotElimGeneralized with T.
 apply replaceTranslation.
 assumption.
Defined.


                                                                                             

End deduction_def.


End Natural_Deduction.