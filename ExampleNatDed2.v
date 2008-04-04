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
Require Import LSeqProp.

Set Implicit Arguments.
Unset Strict Implicit.
Inductive Atoms : Set :=
  | np : Atoms
  | n : Atoms
  | s : Atoms.

(* Example in the logic L where , is associative *)
(* Jean loves and Marie hates Tintin *)

 Definition sentence :=
   Comma (OneForm (At np))
     (Comma (OneForm (Slash (Backslash (At np) (At s)) (At np)))
        (Comma
           (OneForm
              (Slash
                 (Backslash (Slash (At s) (At np)) (Slash (At s) (At np)))
                 (Slash (At s) (At np))))
           (Comma (OneForm (At np))
              (Comma (OneForm (Slash (Backslash (At np) (At s)) (At np)))
                 (OneForm (At np)))))).


Definition sentenceWellOrg :=
  Comma
    (Comma
       (Comma (OneForm (At np))
          (OneForm (Slash (Backslash (At np) (At s)) (At np))))
       (Comma
          (OneForm
             (Slash (Backslash (Slash (At s) (At np)) (Slash (At s) (At np)))
                (Slash (At s) (At np))))
          (Comma (OneForm (At np))
             (OneForm (Slash (Backslash (At np) (At s)) (At np))))))
    (OneForm (At np)).

(* This def shows that in L we can derive the sequent np o ((np\s)/np) |-  s/np *)
Definition auxiliaryDef :
  natDed L_Sequent
    (Comma (OneForm (At np))
       (OneForm (Slash (Backslash (At np) (At s)) (At np))))
    (Slash (At s) (At np)).  

 apply SlashIntro.
 eapply NatExt; [ idtac | constructor 1 | idtac ].
 constructor 1.
 eapply BackSlashElim; [ constructor 1 | idtac ].
 eapply SlashElim; constructor 1.
Defined.

(* To test The new Tactic *)
Require Import Tactics.

Definition auxiliaryDef2 :
  natDed L_Sequent
    (Comma (OneForm (At np))
       (OneForm (Slash (Backslash (At np) (At s)) (At np))))
    (Slash (At s) (At np)).  

apply SlashIntro.
lNaturalTac (nil (A:=path)) LR.
eapply BackSlashElim; [ constructor 1 | idtac ].
eapply SlashElim; constructor 1.
Defined.

Definition sentenceCorrectL :
  natDed L_Sequent sentenceWellOrg (At s).
 unfold sentenceWellOrg in |- *.
 eapply SlashElim; [ idtac | constructor 1 ].
 apply BackSlashElim with (Slash (At s) (At np)).
 apply auxiliaryDef.
 apply SlashElim with (Slash (At s) (At np)).
 constructor 1.
 apply auxiliaryDef.
Defined.


Definition sentenceCorrect2L : natDed L_Sequent sentence (At s).
 apply LNaturalDeduction with sentenceWellOrg.
 apply LgenEqFlattenTrees.
 simpl in |- *.
 reflexivity.
 apply sentenceCorrectL.
Defined.