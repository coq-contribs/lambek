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

(* Some tactics using LTac language*)
Set Implicit Arguments.
Unset Strict Implicit.
Require Export Sequent.
Require Export NaturalDeduction.
Require Export List.

Ltac REPLACE :=
  repeat apply replaceRoot || apply replaceRight || apply replaceLeft.

Inductive path : Set :=
  | r : path
  | l : path.
             

Fixpoint getTermByPath (Atoms : Set) (T : Term Atoms) 
 (p : list path) {struct p} : option (Term Atoms) :=
  match T, p with
  | T, nil => Some T
  | OneForm _, p1 :: p2 => None (A:=Term Atoms)
  | Comma T1 T2, p1 :: p2 =>
      match p1 with
      | l => getTermByPath T1 p2
      | r => getTermByPath T2 p2
      end
  end.


Definition getDotForms (Atoms : Set) (T : Term Atoms) :
  option (Form Atoms * Form Atoms) :=
  match T with
  | OneForm A =>
      match A with
      | Dot A1 B1 => Some (A1, B1)
      | other => None (A:=Form Atoms * Form Atoms)
      end
  | other => None (A:=Form Atoms * Form Atoms)
  end.

            
Definition getSlashTerms (Atoms : Set) (T : Term Atoms) :
  option (Form Atoms * Form Atoms * Term Atoms) :=
  match T with
  | OneForm _ => None (A:=Form Atoms * Form Atoms * Term Atoms)
  | Comma F1 Delta =>
      match F1 with
      | OneForm A1 =>
          match A1 with
          | Slash A B => Some (A, B, Delta)
          | other => None (A:=Form Atoms * Form Atoms * Term Atoms)
          end
      | other => None (A:=Form Atoms * Form Atoms * Term Atoms)
      end
  end. 

Definition getBackSlashTerms (Atoms : Set) (T : Term Atoms) :
  option (Form Atoms * Form Atoms * Term Atoms) :=
  match T with
  | OneForm _ => None (A:=Form Atoms * Form Atoms * Term Atoms)
  | Comma Delta F =>
      match F with
      | OneForm A1 =>
          match A1 with
          | Backslash B A => Some (B, A, Delta)
          | other => None (A:=Form Atoms * Form Atoms * Term Atoms)
          end
      | other => None (A:=Form Atoms * Form Atoms * Term Atoms)
      end
  end. 

Fixpoint replaceTermByTerm (Atoms : Set) (T Tr : Term Atoms) 
 (p : list path) {struct p} : option (Term Atoms) :=
  match T, p with
  | _, nil => Some Tr
  | OneForm _, _ :: _ => None (A:=Term Atoms)
  | Comma T1 T2, p1 :: p2 =>
      match p1 with
      | l =>
          match replaceTermByTerm T1 Tr p2 with
          | None => None (A:=Term Atoms)
          | Some t => Some (Comma t T2)
          end
      | r =>
          match replaceTermByTerm T2 Tr p2 with
          | None => None (A:=Term Atoms)
          | Some t => Some (Comma T1 t)
          end
      end
  end.
(* test*)
(* Eval  Compute in (getSlashTerms (Comma (OneForm (Slash A B))(OneForm B))).
     = (Some ((Form Atoms)*(Form Atoms))*(Term Atoms)
         ((A, B),OneForm B))
     : (option ((Term Atoms)*(Term Atoms))*(Term Atoms))*)



Ltac leftSlashTac p :=
  match goal with
  |  |- (gentzenSequent _ ?X11 _) =>
      match eval compute in (getTermByPath X11 p) with
      | None => idtac
      | (Some ?X1) =>
          match eval compute in (getSlashTerms X1) with
          | None => idtac
          | (Some (?X2, ?X3, ?X4)) =>
              match eval compute in (replaceTermByTerm X11 (OneForm X2) p) with
              | None => idtac
              | (Some ?X5) =>
                  apply LeftSlash with X4 X5 X2 X3;
                   [ REPLACE | idtac | idtac ]
              end
          end
      end
  |  |- _ => idtac
  end.


Ltac leftBackSlashTac p :=
  match goal with
  |  |- (gentzenSequent _ ?X11 _) =>
      match eval compute in (getTermByPath X11 p) with
      | None => idtac
      | (Some ?X1) =>
          match eval compute in (getBackSlashTerms X1) with
          | None => idtac
          | (Some (?X2, ?X3, ?X4)) =>
              match eval compute in (replaceTermByTerm X11 (OneForm X3) p) with
              | None => idtac
              | (Some ?X5) =>
                  apply LeftBackSlash with X4 X5 X3 X2;
                   [ REPLACE | idtac | idtac ]
              end
          end
      end
  |  |- _ => idtac
  end.


Ltac leftDotTac p :=
  match goal with
  |  |- (gentzenSequent _ ?X11 _) =>
      match eval compute in (getTermByPath X11 p) with
      | None => idtac
      | (Some ?X1) =>
          match eval compute in (getDotForms X1) with
          | None => idtac
          | (Some (?X2, ?X3)) =>
              match eval compute in
                    (replaceTermByTerm X11 (Comma (OneForm X2) (OneForm X3))
                       p) with
              | None => idtac
              | (Some ?X5) =>
                  apply LeftDot with X5 X2 X3; [ REPLACE | idtac | idtac ]
              end
          end
      end
  |  |- _ => idtac
  end.


Ltac cutTac A p :=
  match goal with
  |  |- (gentzenSequent _ ?X11 _) =>
      match eval compute in (getTermByPath X11 p) with
      | None => idtac
      | (Some ?X1) =>
          match eval compute in (replaceTermByTerm X11 (OneForm A) p) with
          | None => idtac
          | (Some ?X5) =>
              apply CutRule with X1 X5 A; [ REPLACE | idtac | idtac ]
          end
      end
  |  |- _ => idtac
  end.

(* tactics for L system *)
Inductive directionL : Set :=
  | LR : directionL
  | RL : directionL.

Definition getTreeL (Atoms : Set) (dl : directionL) 
  (T : Term Atoms) : option (Term Atoms) :=
  match T with
  | OneForm _ => None (A:=Term Atoms)
  | Comma T1 T2 =>
      match dl with
      | LR =>
          match T1 with
          | OneForm _ => None (A:=Term Atoms)
          | Comma T3 T4 => Some (Comma T3 (Comma T4 T2))
          end
      | RL =>
          match T2 with
          | OneForm _ => None (A:=Term Atoms)
          | Comma T3 T4 => Some (Comma (Comma T1 T3) T4)
          end
      end
  end.


Ltac lSequentTac p d :=
  match goal with
  |  |- (gentzenSequent L_Sequent ?X1 _) =>
      match eval compute in (getTermByPath X1 p) with
      | None => idtac
      | (Some ?X2) =>
          match eval compute in (getTreeL d X2) with
          | None => idtac
          | (Some ?X3) =>
              match eval compute in (replaceTermByTerm X1 X3 p) with
              | None => idtac
              | (Some ?X4) =>
                  apply SequentExtension with X4 X3 X2;
                   [ apply L_Intro_lr || apply L_Intro_rl | REPLACE | idtac ]
              end
          end
      end
  |  |- _ => idtac
  end.

Ltac lNaturalTac p d :=
  match goal with
  |  |- (natDed L_Sequent ?X1 _) =>
      match eval compute in (getTermByPath X1 p) with
      | None => idtac
      | (Some ?X2) =>
          match eval compute in (getTreeL d X2) with
          | None => idtac
          | (Some ?X3) =>
              match eval compute in (replaceTermByTerm X1 X3 p) with
              | None => idtac
              | (Some ?X4) =>
                  apply NatExt with X4 X3 X2;
                   [ apply L_Intro_lr || apply L_Intro_rl | REPLACE | idtac ]
              end
          end
      end
  |  |- _ => idtac
  end.