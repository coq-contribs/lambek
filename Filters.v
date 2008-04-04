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

(* Introduction to filters Cf Kurtonina's PhD Thesis
These filters will be used to give another proof of completeness *)

Set Implicit Arguments.
Unset Strict Implicit.
Require Export Form.

Section CompletenessFilters.
Variable Atoms : Set.
Section CompletenessDefs.
Variable X : arrow_extension.
Section Filter_Def.


Definition getSet (A : Type) (P : A -> Prop) (x : sigT P) :=
  match x with
  | existT s P => s
  end.


Definition weakFilter (S : Form Atoms -> Prop) : Prop :=
  forall A B : Form Atoms, S A /\ weak (arrow X A B) -> S B.

(* for additive connectives 
Definition filter: ((Form Atoms)->Prop)->Prop:=
[S:(Form Atoms)->Prop] (weakFilter S) /\ 
                       (A,B:(Form Atoms)) (S (Inter A B))<->
                                           (S A) /\ (S B) .

Definition primeFilter: ((Form Atoms)->Prop)->Prop:=
[S:(Form Atoms)->Prop] (filter S)/\
                         (A, B: (Form Atoms)) (S (Uni A B)) <->
                                              (S A)/\(S B) .

*)

Definition compSet (S1 S2 : Form Atoms -> Prop) (F : Form Atoms) : Prop :=
  exists x1 : Form Atoms,
    (exists x2 : Form Atoms, S1 x1 /\ S2 x2 /\ weak (arrow X (Dot x1 x2) F)).


Definition formDerivation (A1 A2 : Form Atoms) : Prop := weak (arrow X A1 A2).    

Definition isIncluded (E1 E2 : Form Atoms -> Prop) :=
  forall F : Form Atoms, E1 F -> E2 F.

Lemma formDerivWFilter : forall A : Form Atoms, weakFilter (formDerivation A).
Proof.
 intro A.
 unfold weakFilter in |- *.
 unfold formDerivation in |- *.
 intros A0 B H.
 elim H.
 clear H; intros H H0.
 eapply weak_comp; eauto.
Qed.

Lemma weakFilterComp :
 forall SF1 SF2 : Form Atoms -> Prop, weakFilter (compSet SF1 SF2).
Proof.
 intros SF1 SF2. 
 unfold weakFilter in |- *.
 unfold compSet in |- *.
 intros A B H.
 elim H; clear H; intros H H0.
 elim H; clear H; intros x1 H.
 elim H; clear H; intros x2 H.
 split with x1.
 split with x2.
 split.
 tauto.
 split.
 tauto.
 apply weak_comp with A.
 tauto.
 auto.
Qed.


End Filter_Def.

Section semanticDefs.
(* the same as in the file Semantics.v *)
Variables (W : Type) (R : W -> W -> W -> Prop) (v_at : Atoms -> W -> Prop). 

(* extension of some valuation on atoms to all formulae *)

Fixpoint val (F : Form Atoms) : W -> Prop :=
  match F with
  | At a => v_at a
  | Dot A B =>
      fun x => ex (fun y => ex (fun z => R x y z /\ val A y /\ val B z))
  | Slash C B => fun y => forall x z : W, R x y z -> val B z -> val C x
  | Backslash A C => fun z => forall x y : W, R x y z -> val A y -> val C x
  end.

End semanticDefs.
Section model_types.

 (* Kinds of models are caracterized wrt the ternary relation R *)

 Definition model_type := forall W : Type, (W -> W -> W -> Prop) -> Prop.

 Definition model_inter (P1 P2 : model_type) (W : Type)
   (R : W -> W -> W -> Prop) := P1 W R /\ P2 W R.
 Variable P : model_type.

  Definition sem_implies : Form Atoms -> Form Atoms -> Prop :=
    fun A B : Form _ =>
    forall (W : Type) (R : W -> W -> W -> Prop) (v_at : Atoms -> W -> Prop),
    P R -> forall w : W, val R v_at A w -> val R v_at B w.

 (* associativity and commutativity *)

 Definition ASS : model_type :=
   fun (W : Type) (R : W -> W -> W -> Prop) =>
   (forall x y z t u : W,
    R t x y -> R u t z -> exists v : W, R v y z /\ R u x v) /\
   (forall x y z v u : W,
    R v y z -> R u x v -> exists t : W, R t x y /\ R u t z).

 Definition COM : model_type :=
   fun (W : Type) (R : W -> W -> W -> Prop) =>
   forall x y z : W, R x y z -> R x z y.



(* canonical model *)
(* WK is the set of all weak filters *)

Definition WK := sigT weakFilter.

Definition RK (E1 E2 E3 : WK) :=
  isIncluded (compSet (getSet E2) (getSet E3)) (getSet E1).

Definition VatK (p : Atoms) (A : WK) := getSet A (At p).
End model_types.

Definition model_OK (P : model_type) := P _ RK.

 Definition complete (P : model_type) :=
   forall A B : Form Atoms, sem_implies P A B -> weak (arrow X A B).



Lemma getSetWeakFilter :
 forall (A : WK) (F1 F2 : Form Atoms),
 getSet A F1 -> weak (arrow X F1 F2) -> getSet A F2.
Proof.
 intro A.
 elim A.
 intros x p F1 F2 H H0.
 simpl in |- *.
 simpl in H.
 unfold weakFilter in p.
 eapply p; split; eauto.
Qed.

Lemma truthLemmaFilters :
 forall (F : Form Atoms) (A : WK), val RK VatK F A <-> getSet A F. 
 intro F.
 elim F.
 simpl in |- *.
 unfold VatK in |- *.
 tauto.
 intros f H f0 H0 A.
 split.
 intro H1.
 cut (compSet (getSet A) (formDerivation f0) f).
 intro H2.
 unfold compSet in H2.
 elim H2; clear H2; intros x1 H2.
 elim H2; clear H2; intros x2 H2.
 elim H2; clear H2; intros H2 H3.
 elim H3; clear H3; intros H3 H4.
 unfold formDerivation in H3.
 apply getSetWeakFilter with x1.
 assumption.
 apply weak_beta.
 apply weak_comp with (Dot x1 x2).
 apply weak_Dot_mono_right; assumption.
 assumption.
 cut (weakFilter (compSet (getSet A) (formDerivation f0))).
 intro H2.
 elim (H (existT weakFilter (compSet (getSet A) (formDerivation f0)) H2)).
 intros.
 apply H3.
 generalize H1.
 simpl in |- *.
 clear H1; intro H1.
 cut (weakFilter (formDerivation f0)).
 intro H5.
 apply H1 with (existT weakFilter (formDerivation f0) H5).
 unfold RK in |- *.
 simpl in |- *.
 unfold isIncluded in |- *.
 auto.
 elim (H0 (existT weakFilter (formDerivation f0) H5)).
 intros H6 H7.
 apply H7.
 simpl in |- *.
 unfold formDerivation in |- *.
 apply weak_one.
 apply formDerivWFilter.
 apply weakFilterComp.
 intro H1.
 simpl in |- *.
 unfold RK in |- *.
 unfold isIncluded in |- *.
 intros x z H2 H3.
 elim (H x); intros H4 H5.
 apply H5.
 apply (H2 f).
 unfold compSet in |- *.
 split with (Slash f f0).
 split with f0.
 split.
 auto.
 split.
 elim (H0 z); intros H6 H7.
 apply H6; assumption.
 apply weak_beta'.
 apply weak_one.
(* case where F=(Dot f f0) *)
 intros f H f0 H0.
 split.
 simpl in |- *.
 intro H1.
 elim H1.
 clear H1; intros x H1.
 elim H1; clear H1; intros z H1.
 elim H1; unfold RK in |- *; clear H1; intros H1 H2.
 elim H2; clear H2; intros H2 H3.
 unfold isIncluded in H1.
 apply H1.
 unfold compSet in |- *.
 split with f.
 split with f0.
 split.
 elim (H x); intros H4 H5.
 apply H4; exact H2.
 split.
 elim (H0 z).
 intros H4 H5.
 apply H4.
 assumption.
 apply weak_one.
 intro H1.
 simpl in |- *.
 assert (H2 : forall A : Form Atoms, weakFilter (formDerivation A)).
 exact formDerivWFilter.
 split with (existT weakFilter (formDerivation f) (H2 f)).
 split with (existT weakFilter (formDerivation f0) (H2 f0)).
 unfold RK in |- *.
 split.
 unfold isIncluded in |- *.
 simpl in |- *.
 unfold compSet in |- *.
 intros F0 H3.
 elim H3; clear H3; intros x1 H3. 
 elim H3; clear H3; intros x2 H3.
 apply getSetWeakFilter with (Dot x1 x2).
 apply getSetWeakFilter with (Dot f f0).
 assumption.
 apply weak_Dot_mono; tauto.
 tauto.
 split.
 elim (H (existT weakFilter (formDerivation f) (H2 f))).
 intros H3 H4.
 apply H4.
 simpl in |- *.
 unfold formDerivation in |- *.
 apply weak_one.
 elim (H0 (existT weakFilter (formDerivation f0) (H2 f0))).
 intros H3 H4.
 apply H4.
 simpl in |- *.
 unfold formDerivation in |- *; apply weak_one.
(* Case where F=(Backslash f f0) *)
 intros f H0 f0 H.
 split.
 intro H1.
 assert (L : compSet (formDerivation f) (getSet A) f0).
 simpl in H1.
 assert (H2 : weakFilter (compSet (formDerivation f) (getSet A))).
 apply weakFilterComp.
 elim (H (existT weakFilter (compSet (formDerivation f) (getSet A)) H2)).
 intros H4 H5.
 apply H4.
 assert (H6 : forall A : Form Atoms, weakFilter (formDerivation A)).
 exact formDerivWFilter.
 apply H1 with (existT weakFilter (formDerivation f) (H6 f)). 
 unfold RK in |- *.
 unfold isIncluded in |- *.
 simpl in |- *.
 auto.
 elim (H0 (existT weakFilter (formDerivation f) (H6 f))).
 intros H7 H8.
 apply H8.
 simpl in |- *.
 unfold formDerivation in |- *.
 apply weak_one.
 unfold compSet in L.
 elim L; clear L; intros x2 L.
 elim L; clear L; intros x3 L.
 apply getSetWeakFilter with x3.
 tauto.
 apply weak_gamma.
 apply weak_comp with (Dot x2 x3).
 apply weak_Dot_mono_left.
 unfold formDerivation in L.
 tauto.
 tauto.
 intro H1.
 simpl in |- *.
 intros x y H2 H3.
 elim (H x).
 intros H4 H5.
 apply H5.
 unfold RK in H2.
 unfold isIncluded in H2.
 apply H2.
 unfold compSet in |- *.
 split with f.
 split with (Backslash f f0).
 split.
 elim (H0 y).
 intros H6 H7.
 apply H6.
 exact H3.
 split.
 exact H1.
 apply weak_gamma'.
 apply weak_one.
Qed.

 Lemma completenessProof : forall P : model_type, model_OK P -> complete P.

Proof.
 unfold model_OK, complete, sem_implies in |- *.
 intros P H A B HO.
 unfold formDerivation in |- *.
 cut (formDerivation A B).
 unfold formDerivation in |- *.
 auto.
 assert (H1 : weakFilter (formDerivation A)).
 apply formDerivWFilter.
 set (w := existT weakFilter (formDerivation A) H1).
 cut (getSet w B).
 simpl in |- *.
 auto.
 elim (truthLemmaFilters B w).
 intros H2 H3.
 apply H2.
 apply HO.
 auto.
 elim (truthLemmaFilters A w).
 intros H4 H5.
 apply H5.
 simpl in |- *.
 unfold formDerivation in |- *; apply weak_one.
Qed.

End CompletenessDefs.

Lemma NL_OK : model_OK NL (fun _ _ => True).
Proof.
 unfold model_OK in |- *.
 auto.
Qed.

Lemma NL_complete : complete NL (fun _ _ => True).
Proof.
 apply completenessProof.
 apply NL_OK.
Qed.

Lemma NLP_OK : forall X : arrow_extension, extends NLP X -> model_OK X COM.
Proof.
 intros X H.
 unfold model_OK in |- *.
 unfold COM in |- *.
 unfold RK in |- *.
 unfold isIncluded in |- *.
 intros x y z H0 F H1.
 apply H0.
 unfold compSet in |- *.
 unfold compSet in H1.
 elim H1; clear H1; intros x1 H1.
 elim H1; clear H1; intros x2 H1.
 split with x2.
 split with x1.
 split.
 tauto.
 split.
 tauto.
 apply weak_comp with (Dot x1 x2).
 apply weak_arrow_plus.
 unfold extends in H.
 apply H.
 split.
 tauto.
Qed.

Lemma NLP_complete : complete NLP COM.
Proof.
 apply completenessProof.
 apply NLP_OK.
 apply no_extend.
Qed.

Lemma LcompSet :
 forall (F : Form Atoms) (X : arrow_extension) (x y z : WK X),
 extends L X ->
 compSet X (getSet x) (compSet X (getSet y) (getSet z)) F ->
 compSet X (compSet X (getSet x) (getSet y)) (getSet z) F.
Proof.
 intros F X x y z H H0.
 unfold compSet in |- *.
 unfold compSet in H0.
 elim H0; clear H0; intros x1 H0.
 elim H0; clear H0; intros x2 H0.
 elim H0; clear H0; intros H0 H1.
 elim H1; clear H1; intros H1 H2.
 elim H1; clear H1; intros x3 H1.
 elim H1; clear H1; intros x4 H1.
 split with (Dot x1 x3).
 split with x4.
 split.
 split with x1.
 split with x3.
 split.
 auto.
 split.
 tauto.
 apply weak_one. 
 split.
 tauto.
 apply weak_comp with (Dot x1 (Dot x3 x4)).
 apply weak_arrow_plus.
 unfold extends in H.
 apply H.
 constructor 2.
 apply weak_comp with (Dot x1 x2).
 apply weak_Dot_mono_right.
 tauto.
 assumption.
Qed.

Lemma LcompSet' :
 forall (F : Form Atoms) (X : arrow_extension) (x y z : WK X),
 extends L X ->
 compSet X (compSet X (getSet x) (getSet y)) (getSet z) F ->
 compSet X (getSet x) (compSet X (getSet y) (getSet z)) F.

Proof.
 intros F X x y z H H0.
 unfold compSet in |- *.
 unfold compSet in H0.
 elim H0; clear H0; intros x1 H0.
 elim H0; clear H0; intros x2 H0.
 elim H0; clear H0; intros H0 H1.
 elim H0; clear H0; intros x3 H0.
 elim H0; clear H0; intros x4 H0.
 split with x3.
 split with (Dot x4 x2).
 split.
 tauto.
 split.
 split with x4.
 split with x2.
 split.
 tauto.
 split.
 tauto.
 apply weak_one.
 apply weak_comp with (Dot (Dot x3 x4) x2).
 apply weak_arrow_plus.
 unfold extends in H.
 apply H. 
 constructor 1.
 apply weak_comp with (Dot x1 x2).
 apply weak_Dot_mono_left.
 tauto.
 tauto.
Qed.


Lemma compSetMono :
 forall (X : arrow_extension) (s1 s2 s3 s4 : Form Atoms -> Prop)
   (F : Form Atoms),
 isIncluded s1 s2 ->
 isIncluded s3 s4 -> compSet X s1 s3 F -> compSet X s2 s4 F.
Proof.
 intros X s1 s2 s3 s4 F.
 unfold isIncluded in |- *.
 unfold compSet in |- *.
 intros H H0 H1.
 elim H1; clear H1; intros x1 H1.
 elim H1; clear H1; intros x2 H1.
 split with x1.
 split with x2.
 split.
 apply H; tauto.
 split.
 apply H0; tauto.
 tauto.
Qed.

Lemma L_OK : forall X : arrow_extension, extends L X -> model_OK X ASS.

 intros X H.
 unfold model_OK, ASS, RK in |- *.
 split.
 intros x y z t u H0 H1.
 assert (L : weakFilter X (compSet X (getSet y) (getSet z))).
 apply weakFilterComp.
 split with (existT (weakFilter X) (compSet X (getSet y) (getSet z)) L).
 split.
 simpl in |- *; auto.
 simpl in |- *.
 unfold isIncluded in |- *; auto.
 unfold isIncluded in |- *; intros F H2.
 apply H1.
 apply compSetMono with (compSet X (getSet x) (getSet y)) (getSet z).
 auto.
 unfold isIncluded in |- *; auto.
 apply LcompSet; auto.
 intros x y z v u H0 H1.
 assert (L : weakFilter X (compSet X (getSet x) (getSet y))).
 apply weakFilterComp.
 split with (existT (weakFilter X) (compSet X (getSet x) (getSet y)) L).
 split.
 simpl in |- *.
 unfold isIncluded in |- *; auto.
 simpl in |- *.
 unfold isIncluded in |- *.
 intros F H2.
 apply H1.
 apply compSetMono with (getSet x) (compSet X (getSet y) (getSet z)).
 unfold isIncluded in |- *; auto.
 exact H0.
 apply LcompSet'; auto.
Qed.

Lemma L_complete : complete L ASS.
Proof.
 apply completenessProof.
 apply L_OK.
 apply no_extend.
Qed.


End CompletenessFilters.