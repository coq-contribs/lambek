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




Require Export NaturalDeduction.

(* Some examples *)

Require Import Sequent.

Inductive Atoms : Set :=
  | sn : Atoms
  | n : Atoms
  | s : Atoms.


Definition Ex1 :
  natDed NL_Sequent (OneForm (Dot (Slash (At sn) (At n)) (At n)))
    (At sn).
 eapply DotElim.
 constructor 1.
 constructor 1.
 eapply SlashElim.
 constructor 1.
 constructor 1.
Defined.


Definition Ex2 :
  natDed NL_Sequent
    (OneForm
       (Dot (At sn) (Dot (Slash (Backslash (At sn) (At n)) (At s)) (At s))))
    (At n).
eapply DotElim.
constructor 1.
constructor 1.
eapply DotElim.
constructor 3.
constructor 1.
constructor 1.
eapply BackSlashElim.
constructor 1.
eapply SlashElim; [ idtac | constructor 1 ].
constructor 1.
Defined.




