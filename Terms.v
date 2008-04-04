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

Require Export Form.
Section Term_def.

Set Implicit Arguments.

(* definition of terms   S:= F|(S,S)*)

Inductive Term (Atoms:Set) : Set :=
  | OneForm : Form Atoms -> Term Atoms
  | Comma : Term Atoms -> Term Atoms -> Term Atoms.



(* definition of structural rules *)

(* Definitions of some extensions of sequent calculus like associativity 
or commutativity *)

Definition gentzen_extension :=
  forall Atoms : Set, Term Atoms -> Term Atoms -> Set.

Definition add_genExtension (E1 E2 : gentzen_extension) :
  gentzen_extension :=
  fun At Gamma Gamma' => (E1 At Gamma Gamma' + E2 At Gamma Gamma')%type.

Definition genExtends (X X' : gentzen_extension) :=
  forall (At : Set) (T1 T2 : Term At), X At T1 T2 -> X' At T1 T2.

Definition genExtendsRef : forall X : gentzen_extension, genExtends X X.
 intro.
 unfold genExtends in |- *.
 auto.
Defined.

(* no extension at all*)
Inductive NL_Sequent (Atoms:Set): Term Atoms -> Term Atoms -> Set :=.

(* commutativity*)
Inductive NLP_Sequent (Atoms:Set) : Term Atoms -> Term Atoms -> Set :=
    NLP_Intro :
      forall Delta1 Delta2 : Term Atoms,
      NLP_Sequent  (Comma Delta1 Delta2) (Comma Delta2 Delta1).

(*associativity *)
Inductive L_Sequent (Atoms: Set) : Term Atoms -> Term Atoms -> Set :=
  | L_Intro_lr :
      forall Delta1 Delta2 Delta3 : Term Atoms,
      L_Sequent (Comma Delta1 (Comma Delta2 Delta3))
        (Comma (Comma Delta1 Delta2) Delta3)
  | L_Intro_rl :
      forall Delta1 Delta2 Delta3 : Term Atoms,
      L_Sequent (Comma (Comma Delta1 Delta2) Delta3)
        (Comma Delta1 (Comma Delta2 Delta3)).

(* Both associativity and commutativity *)
Definition LP_Sequent : gentzen_extension :=
  add_genExtension NLP_Sequent L_Sequent.

(* Some definitions concerning relation between the extensions seen above*)

Definition LPextendsL :
  forall E : gentzen_extension,
  genExtends LP_Sequent E -> genExtends L_Sequent E.
 intros E H.
 unfold genExtends in |- *.
 unfold genExtends in H.
 intros.
 apply H.
 unfold LP_Sequent in |- *.
 unfold add_genExtension in |- *.
 auto.
Defined.

Definition LPextendsNLP :
  forall E : gentzen_extension,
  genExtends LP_Sequent E -> genExtends NLP_Sequent E.

 intros E H.
 unfold genExtends in |- *.
 unfold genExtends in H.
 intros.
 apply H.
 unfold LP_Sequent in |- *.
 unfold add_genExtension in |- *.
 auto.
Defined.

(* Definition of the function that translates terms to forms *)
Fixpoint deltaTranslation (Atoms:Set) (T : Term Atoms){ struct T} : Form Atoms :=
  match T with
  | OneForm f => f
  | Comma t1 t2 => Dot (deltaTranslation t1) (deltaTranslation t2)
  end.


                       
End Term_def.