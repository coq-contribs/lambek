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



(* Formalisation of the axiomatic presentation 
  of Lambek calculus . cf.Moortgat *)


Set Implicit Arguments.
Unset Strict Implicit.

Section CTL_def.

 (* atomic formulae *)

 (* The set of formulae built on Atoms ; we shall put an infix syntax 
    in a near future *)

 Inductive Form (Atoms : Set) : Set :=
   | At : Atoms -> Form Atoms
   | Slash : Form Atoms -> Form Atoms -> Form Atoms
   | Dot : Form Atoms -> Form Atoms -> Form Atoms
   | Backslash : Form Atoms -> Form Atoms -> Form Atoms.


(* The arrow relationship and its extensions (like associativity, 
  commutativity  etc. ) 
   Please notice that this relationship has sort Set in order to 
   consider derivations as data structures ; for some applications
   which need propositions (such as completeness proofs) one needs
   to coerce a data type like (arrow X A B) into the proposition
   (weak (arrow X A B)).
*)

 Definition arrow_extension :=
   forall Atoms : Set, Form Atoms -> Form Atoms -> Set.

 Definition add_extension (E1 E2 : arrow_extension) : arrow_extension :=
   fun At A B => (E1 At A B + E2 At A B)%type.
  
 Definition extends (X X' : arrow_extension) :=
   forall (At : Set) (A B : Form At), X At A B -> X' At A B.

 Definition no_extend : forall X : arrow_extension, extends X X. 
  unfold extends in |- *; auto.
 Defined.
 
 Definition add_extend_l :
   forall X X' : arrow_extension, extends X (add_extension X X').
  intros; unfold add_extension, extends in |- *.
  left; auto.
 Qed.

 Definition add_extend_r :
   forall X X' : arrow_extension, extends X' (add_extension X X').
  intros; unfold add_extension, extends in |- *.
  right; auto.
 Qed.
 
 Definition extends_trans :
   forall X Y Z : arrow_extension, extends X Y -> extends Y Z -> extends X Z.
 intros X Y Z.
 unfold extends in |- *; auto.
 Defined.
(* most popular extensions *)

Inductive NL (Atoms : Set) (A B : Form Atoms) : Set :=.


Inductive NLP (Atoms : Set) : Form Atoms -> Form Atoms -> Set :=
    Comm_intro : forall A B : Form Atoms, NLP (Dot A B) (Dot B A).

Inductive L (Atoms : Set) : Form Atoms -> Form Atoms -> Set :=
  | L_lr : forall A B C : Form Atoms, L (Dot A (Dot B C)) (Dot (Dot A B) C)
  | L_rl : forall A B C : Form Atoms, L (Dot (Dot A B) C) (Dot A (Dot B C)).


Definition LP : arrow_extension := add_extension NLP L.

Lemma NL_X : forall X : arrow_extension, extends NL X.
Proof.
  unfold extends in |- *; simple induction 1.
Qed.

Hint Resolve NL_X: ctl.

Lemma NLP_LP : extends NLP LP.
Proof.
 unfold extends, LP in |- *; left; assumption.
Qed.

Lemma L_LP : extends L LP.
Proof.
 unfold extends, LP in |- *; right; assumption.
Qed.


(* An inductive datatype for (arrow X A B) *)
Variable Atoms : Set.

Section arrow_def.
 Variable X : arrow_extension.

 Inductive arrow (Atoms : Set) : Form Atoms -> Form Atoms -> Set :=
   | one : forall A : Form Atoms, arrow A A
   | comp : forall A B C : Form Atoms, arrow A B -> arrow B C -> arrow A C
   | beta :
       forall A B C : Form Atoms, arrow (Dot A B) C -> arrow A (Slash C B)
   | beta' :
       forall A B C : Form Atoms, arrow A (Slash C B) -> arrow (Dot A B) C
   | gamma :
       forall A B C : Form Atoms,
       arrow (Dot A B) C -> arrow B (Backslash A C)
   | gamma' :
       forall A B C : Form Atoms,
       arrow B (Backslash A C) -> arrow (Dot A B) C
   | arrow_plus : forall A B : Form Atoms, X A B -> arrow A B.

 Hint Resolve one comp beta gamma arrow_plus: ctl.

 (* some derived rules for (arrow X) *)


 Definition Dot_mono_right :
   forall A B B' : Form Atoms, arrow B' B -> arrow (Dot A B') (Dot A B).
  intros A B B' H.
  apply gamma'.
  apply comp with B.
  assumption.
  apply gamma.
  apply one.
 Defined.


 Definition Dot_mono_left :
   forall A B A' : Form Atoms, arrow A' A -> arrow (Dot A' B) (Dot A B).
  intros A B A' H. 
  apply beta'.
  apply comp with A; auto.
  apply beta.
  apply one.
 Defined.



 Definition Dot_mono :
   forall A B C D : Form Atoms,
   arrow A C -> arrow B D -> arrow (Dot A B) (Dot C D).
 intros A B C D H H0.
 apply comp with (Dot C B).
 apply Dot_mono_left.
 assumption.
 apply Dot_mono_right; assumption.
Defined.


 Definition Slash_mono_left :
   forall C B C' : Form Atoms, arrow C' C -> arrow (Slash C' B) (Slash C B).
  intros C B C' H. 
  apply beta. 
  apply comp with C'.
  apply beta'.
  apply one.
  auto.
 Defined. 

 Definition Slash_antimono_right :
   forall C B B' : Form Atoms, arrow B' B -> arrow (Slash C B) (Slash C B').
  intros C B B' H.
  apply beta; apply gamma'.
  apply comp with B.
  assumption.
  apply gamma.
  apply beta'.
  apply one.
 Defined.

 Definition Backslash_antimono_left :
   forall A C A' : Form Atoms,
   arrow A A' -> arrow (Backslash A' C) (Backslash A C).
  intros A C A' H. 
  apply gamma. 
  apply beta'.
  apply comp with A'.
  assumption.
  apply beta.
  apply gamma'.
  apply one.
 Defined.

 Definition Backslash_mono_right :
   forall A C C' : Form Atoms,
   arrow C' C -> arrow (Backslash A C') (Backslash A C).
  intros A C C' H.
  apply gamma.
  apply comp with C'. 
  apply beta'.
  apply beta. 
  apply gamma'.
  apply one.
  assumption.
 Defined.

End arrow_def.

Hint Resolve one comp beta gamma arrow_plus: ctl.


Definition mono_X :
  forall X X' : arrow_extension,
  extends X X' -> forall A B : Form Atoms, arrow X A B -> arrow X' A B.
 simple induction 2.
 apply one.
 intros.
 eapply comp.
 eauto.
 auto.
 intros.
 apply beta.
 assumption.
 intros.
 apply beta'.
 auto.
 intros.
 apply gamma.
 assumption.
 intros.
 apply gamma'; assumption.
 intros; constructor 7.
 auto.
Defined.


Section weaken.
(* coercion to Prop *)

 Inductive weak (A : Set) : Prop :=
     weak_intro : forall a : A, weak A.

(* weak combinators for arrow   
*)

  Lemma weak_one :
   forall (X : arrow_extension) (A : Form Atoms), weak (arrow X A A).
 Proof.
  intros; split.
  apply one.
 Qed.

 Hint Resolve weak_one: ctl.

 Lemma weak_comp :
  forall (X : arrow_extension) (A B C : Form Atoms),
  weak (arrow X A B) -> weak (arrow X B C) -> weak (arrow X A C).
 Proof.
  intros X A B C H H0.
  case H; case H0.
  split.
  apply comp with B; auto.
 Qed.
  
 Hint Resolve weak_comp: ctl.
 
 Lemma weak_beta :
  forall (X : arrow_extension) (A B C : Form Atoms),
  weak (arrow X (Dot A B) C) -> weak (arrow X A (Slash C B)).
 Proof.
  intros X A B C H.
  case H.
  split.
  apply beta; auto.
 Qed.

 Hint Resolve weak_beta: ctl.

 Lemma weak_beta' :
  forall (X : arrow_extension) (A B C : Form Atoms),
  weak (arrow X A (Slash C B)) -> weak (arrow X (Dot A B) C).
 Proof.
  intros X A B C H.
  case H.
  split.
  apply beta'; auto.
 Qed.


 Lemma weak_gamma :
  forall (X : arrow_extension) (A B C : Form Atoms),
  weak (arrow X (Dot A B) C) -> weak (arrow X B (Backslash A C)).
 Proof.
  intros X A B C H. 
  case H.
  split.
  apply gamma; auto.
 Qed.

 Hint Resolve weak_gamma: ctl.

 Lemma weak_gamma' :
  forall (X : arrow_extension) (A B C : Form Atoms),
  weak (arrow X B (Backslash A C)) -> weak (arrow X (Dot A B) C).
 Proof.
  intros X A B C H.
  case H.
  split.
  apply gamma'; auto.
 Qed.

 Lemma weak_arrow_plus :
  forall (X : arrow_extension) (A B : Form Atoms),
  X _ A B -> weak (arrow X A B).
 Proof.
  split.
  apply arrow_plus; auto. 
 Qed.

 Hint Resolve weak_gamma: ctl.

 Lemma weak_Dot_mono :
  forall (A B C D : Form Atoms) (X : arrow_extension),
  weak (arrow X A C) ->
  weak (arrow X B D) -> weak (arrow X (Dot A B) (Dot C D)).
 Proof.
 intros A B C D X H H0.
 case H.
 case H0.
 intros.
 split.
 apply Dot_mono; auto.
Qed.

 Lemma weak_Dot_mono_right :
  forall (X : arrow_extension) (A B B' : Form Atoms),
  weak (arrow X B' B) -> weak (arrow X (Dot A B') (Dot A B)).
 Proof.
  intros X A B B' H.
  case H.
  split.
  apply Dot_mono_right; auto.
 Qed.

 Lemma weak_Dot_mono_left :
  forall (X : arrow_extension) (A B A' : Form Atoms),
  weak (arrow X A' A) -> weak (arrow X (Dot A' B) (Dot A B)).
 Proof.
  intros X A B A' H. 
  case H; split.
  apply Dot_mono_left; auto.
 Qed.

 Lemma weak_Slash_mono_left :
  forall (X : arrow_extension) (C B C' : Form Atoms),
  weak (arrow X C' C) -> weak (arrow X (Slash C' B) (Slash C B)).
 Proof.
  intros X C B C' H. 
  case H; split.
  apply Slash_mono_left; auto.
 Qed. 



 Lemma weak_Slash_antimono_right :
  forall (X : arrow_extension) (C B B' : Form Atoms),
  weak (arrow X B' B) -> weak (arrow X (Slash C B) (Slash C B')).
 Proof.
  intros X C B B' H.
  case H; split.
  apply Slash_antimono_right; auto. 
 Qed.


 Lemma weak_Backslash_antimono_left :
  forall (X : arrow_extension) (A C A' : Form Atoms),
  weak (arrow X A A') -> weak (arrow X (Backslash A' C) (Backslash A C)).
 Proof.
  intros X A C A' H. 
  case H; split.
  apply Backslash_antimono_left; auto. 
 Qed.

 Lemma weak_Backslash_mono_right :
  forall (X : arrow_extension) (A C C' : Form Atoms),
  weak (arrow X C' C) -> weak (arrow X (Backslash A C') (Backslash A C)).
 Proof.
  intros X A C C' H.
  case H; split. 
  apply Backslash_mono_right; auto.
 Qed.





End weaken.



(* combinators  pi and alpha *)



 Definition pi :
   forall X : arrow_extension,
   extends NLP X -> forall A B : Form Atoms, arrow X (Dot A B) (Dot B A).
  intros X H A B.
  apply arrow_plus.
  apply H.
  split.
 Defined.

 Definition pi_NLP : forall A B : Form Atoms, arrow NLP (Dot A B) (Dot B A).
  apply pi.
  apply no_extend.
 Defined.

 Definition pi_LP : forall A B : Form Atoms, arrow LP (Dot A B) (Dot B A). 
  apply pi.
  unfold LP in |- *. 
  apply add_extend_l.
 Defined. 


 Definition alpha :
   forall X : arrow_extension,
   extends L X ->
   forall A B C : Form Atoms, arrow X (Dot A (Dot B C)) (Dot (Dot A B) C).
  intros X H A B C.
  apply arrow_plus.
  apply H.
  left.
 Defined.

 Definition alpha_L :
   forall A B C : Form Atoms, arrow L (Dot A (Dot B C)) (Dot (Dot A B) C).
  apply alpha.
  apply no_extend.
 Defined.
 
 
 Definition alpha_LP :
   forall A B C : Form Atoms, arrow LP (Dot A (Dot B C)) (Dot (Dot A B) C).
  apply alpha.
  unfold LP in |- *; apply add_extend_r. 
 Defined.
 
 Definition alpha' :
   forall X : arrow_extension,
   (forall A B : Form Atoms, L A B -> X _ A B) ->
   forall A B C : Form Atoms, arrow X (Dot (Dot A B) C) (Dot A (Dot B C)).
  intros X H A B C.
  apply arrow_plus.
  apply H.
  right.
 Defined.

 Definition alpha'_L :
   forall A B C : Form Atoms, arrow L (Dot (Dot A B) C) (Dot A (Dot B C)).
  apply alpha'.
  auto.
 Defined.
 
 
 Definition alpha'_LP :
   forall A B C : Form Atoms, arrow LP (Dot (Dot A B) C) (Dot A (Dot B C)).
  apply alpha'.
  unfold LP, add_extension in |- *; auto.
 Defined.


End CTL_def.


Implicit Arguments Dot [Atoms].
Implicit Arguments Slash [Atoms].
Implicit Arguments Backslash [Atoms].


Hint Resolve one comp beta gamma arrow_plus: ctl.

Hint Resolve weak_one weak_comp weak_beta weak_gamma: ctl.

Hint Resolve NL_X L_LP NLP_LP: ctl.
