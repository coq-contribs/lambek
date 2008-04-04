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


Require Export GentzenDed.
Require Export ArrowGentzen.

Set Implicit Arguments.



Definition natDedToArrow :
  forall (Atoms:Set)(Gamma : Term Atoms) (F : Form Atoms) 
 (E : gentzen_extension)(X : arrow_extension),
  gentzenToArrowExt Atoms E X ->
  natDed E Gamma F -> arrow X (deltaTranslation Gamma) F.

 intros.
 eapply gentzenToArrow.
 eauto.
 apply natDedToGentzen.
 assumption.
Defined.


Definition arrowToNatDed :
  forall (Atoms:Set)(A B : Form Atoms) (E : gentzen_extension) (X : arrow_extension),
  condCutExt E ->
  arrowToGentzenExt Atoms X E ->
  arrow X A B -> natDed E (OneForm A) B.
 intros.
 apply gentzenToNatDed.
 auto.
 eapply arrowToGentzen.
 eauto.
 assumption.
Defined.
 
