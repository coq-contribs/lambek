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

Require Import Polarity.
Require Import ZArith.

Inductive atomsEx : Set :=
  | s : atomsEx
  | sn : atomsEx
  | n : atomsEx.

Lemma atomsEx_dec : forall x y : atomsEx, {x = y} + {x <> y}.
 intros x y.
 elim x; elim y; first [ left; reflexivity | right; discriminate ].
Defined.

Lemma notDerivableSequence :
 ~
 weak
   (gentzenSequent NL_Sequent
      (Comma (OneForm (At s)) (OneForm (Slash (At sn) (At n)))) (
      At s)). 

 Proof.
  red in |- *.
  intro H.
  elim H.
  intro H0.
  clear H.
  Polartest sn (atomsEx_dec sn) H0. 
  apply NLEqualPolarity.
  simpl in |- *.
  auto with zarith.
 Qed.