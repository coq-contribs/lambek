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

Require Import Tactics.

(* Derivation of the relative sentence 'that Peter wrote' in the 
system L using natural deduction rules of inference *)


Inductive Atoms : Set :=
  | np : Atoms
  | s : Atoms
  | r : Atoms.

Definition relativeSentence :
  natDed L_Sequent
    (Comma (OneForm (Slash (At r) (Slash (At s) (At np))))
       (Comma (OneForm (At np))
          (OneForm (Slash (Backslash (At np) (At s)) (At np))))) (
    At r).
 eapply SlashElim.
 constructor 1.
 apply SlashIntro.
 lNaturalTac (nil (A:=path)) LR.
 eapply BackSlashElim.
 constructor 1.
 eapply SlashElim; constructor 1.
Defined.