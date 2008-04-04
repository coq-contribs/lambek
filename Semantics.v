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




Require Export Form.
Set Implicit Arguments.
Unset Strict Implicit.

Section Atoms_fixed.
Variable Atoms : Set.

Section semantic_defs.

(* Models for CTL *)

Variables (W : Set) (R : W -> W -> W -> Prop) (v_at : Atoms -> W -> Prop). 

(* extension of some valuation on atoms to all formulae *)

Fixpoint val (F : Form Atoms) : W -> Prop :=
  match F with
  | At a => v_at a
  | Dot A B =>
      fun x => exists y : W, (exists z : W, R x y z /\ val A y /\ val B z)
  | Slash C B => fun y => forall x z : W, R x y z -> val B z -> val C x
  | Backslash A C => fun z => forall x y : W, R x y z -> val A y -> val C x
  end.

Definition satisfies (w : W) (A : Form Atoms) : Prop := val A w.

End semantic_defs.

Section model_types.

 (* Kinds of models are caracterized wrt the ternary relation R *)

 Definition model_type := forall W : Set, (W -> W -> W -> Prop) -> Prop.

 Definition model_inter (P1 P2 : model_type) (W : Set)
   (R : W -> W -> W -> Prop) := P1 W R /\ P2 W R.
 Variable P : model_type.
 
 Definition sem_implies : Form Atoms -> Form Atoms -> Prop :=
   fun A B : Form _ =>
   forall (W : Set) (R : W -> W -> W -> Prop) (v_at : Atoms -> W -> Prop),
   P R -> forall w : W, satisfies R v_at w A -> satisfies R v_at w B.

 (* semantic versions of derivation rules *)

 Lemma ONE : forall A : Form Atoms, sem_implies A A.
 Proof.
  unfold sem_implies, satisfies in |- *; auto.
 Qed.

 Lemma COMP :
  forall A B C : Form Atoms,
  sem_implies A B -> sem_implies B C -> sem_implies A C.
 Proof.
  unfold sem_implies, satisfies in |- *; auto.
 Qed.

 Lemma GAMMA' :
  forall A B C : Form Atoms,
  sem_implies B (Backslash A C) -> sem_implies (Dot A B) C.
 Proof.
  unfold sem_implies, satisfies in |- *; simpl in |- *; auto.
  intros A B C H W R v_at w H0 H1.
  case H1; intros y H2.
  case H2; intros z H3.
  case H3; intros H4 H5.
  case H5; eauto.
 Qed.


 Lemma GAMMA :
  forall A B C : Form _,
  sem_implies (Dot A B) C -> sem_implies B (Backslash A C).
 Proof.
  unfold sem_implies, satisfies in |- *; simpl in |- *; auto.
  intros A B C H W R v_at H0 w H1 x y H2 H3.
  apply H.
  assumption.
  exists y; exists w; auto.
 Qed.

 Lemma BETA' :
  forall A B C : Form Atoms,
  sem_implies A (Slash C B) -> sem_implies (Dot A B) C.
 Proof.
  unfold sem_implies, satisfies in |- *; simpl in |- *; auto.
  intros A B C H W R v_at w H0 H1.
  case H1; intros y H2.
  case H2; intros z H3.
  case H3; intros H4 H5.
  case H5; eauto.
 Qed.

 Lemma BETA :
  forall A B C : Form _, sem_implies (Dot A B) C -> sem_implies A (Slash C B).
 Proof.
  unfold sem_implies, satisfies in |- *; simpl in |- *; auto.
  intros A B C H W R v_at H0 w H1 x y H2 H3.
  apply H.
  assumption.
  exists w; exists y; auto.
 Qed.


 Lemma GAMMA'BETA :
  forall A B C : Form _,
  sem_implies B (Backslash A C) -> sem_implies A (Slash C B).
 Proof.
  unfold sem_implies, satisfies in |- *; simpl in |- *; eauto.
 Qed.

 End model_types.


(* associativity and commutativity *)

 Definition ASS : model_type :=
   fun (W : Set) (R : W -> W -> W -> Prop) =>
   (forall x y z t u : W,
    R t x y -> R u t z -> exists v : W, R v y z /\ R u x v) /\
   (forall x y z v u : W,
    R v y z -> R u x v -> exists t : W, R t x y /\ R u t z).

 Definition COM : model_type :=
   fun (W : Set) (R : W -> W -> W -> Prop) =>
   forall x y z : W, R x y z -> R x z y.

 Section soundness.

 Definition sound (E : arrow_extension) (P : model_type) :=
   forall A B : Form _, arrow E A B -> sem_implies P A B.



 Lemma sem_implies_inter :
  forall (P1 P2 : model_type) (A B : Form _),
  sem_implies P1 A B ->
  sem_implies P2 A B -> sem_implies (model_inter P1 P2) A B.
 Proof.                             
  unfold model_inter, sem_implies in |- *; intros P1 P2 A B H H0 W R v_at H1.
  case H1; auto.
 Qed.
 


 Lemma ASS_lemma :
  forall (W : Set) (R : W -> W -> W -> Prop) (v_at : Atoms -> W -> Prop),
  ASS R ->
  forall (A B C : Form _) (w : W),
  satisfies R v_at w (Dot A (Dot B C)) ->
  satisfies R v_at w (Dot (Dot A B) C).
 Proof.
  intros W R v_at H A B C w H0.
  elim H; intros H1 H2.
  clear H; simpl in |- *.
  simpl in H0.
  elim H0; intros y Hy; clear H0.
  elim Hy; intros z Hz; clear Hy.
  elim Hz; intros H3 H4; elim H4; intros H5 H6; clear Hz H4.
  elim H6; intros y0 Hy0; clear H6.
  elim Hy0; intros z0 Hz0; clear Hy0.
  elim Hz0; intros H6 H7; elim H7; intros H8 H9; clear Hz0 H7.
  elim (H2 _ _ _ _ _ H6 H3); intros x H; case H; intros; clear H.
  exists x.
  exists z0; split.
  auto.
  split; auto.   
  exists y; exists y0; auto.
 Qed.


 Lemma ASS_lemma_R :
  forall (W : Set) (R : W -> W -> W -> Prop) (v_at : Atoms -> W -> Prop),
  ASS R ->
  forall (A B C : Form _) (w : W),
  satisfies R v_at w (Dot (Dot A B) C) ->
  satisfies R v_at w (Dot A (Dot B C)).
 Proof.
  intros W R v_at H A B C w H0.
  elim H; intros H1 H2.
  clear H; simpl in |- *.
  simpl in H0.
  elim H0; intros y Hy; clear H0.
  elim Hy; intros z Hz; clear Hy.
  elim Hz; intros H3 H4; elim H4; intros H5 H6; clear Hz H4.
  elim H5; intros y0 Hy0; clear H5.
  elim Hy0; intros z0 Hz0; clear Hy0.
  elim Hz0; intros H5 H7; elim H7; intros H8 H9; clear Hz0 H7.
  elim (H1 _ _ _ _ _ H5 H3); intros x H; case H; intros; clear H.
  exists y0.
  exists x; split.
  auto.
  split; auto. 
  exists z0; exists z; auto.
 Qed.


 Lemma COM_lemma :
  forall (W : Set) (R : W -> W -> W -> Prop) (v_at : Atoms -> W -> Prop),
  COM R ->
  forall (A B : Form _) (w : W),
  satisfies R v_at w (Dot A B) -> satisfies R v_at w (Dot B A).
 Proof.
  intros W R v_at H A B w H0.
  simpl in |- *.
  simpl in H0.
  case H0; intros y Hy; clear H0.
  case Hy; intros y0 Hy0; clear Hy.
  exists y0; exists y; auto.
  case Hy0.
  simple destruct 2; auto. 
 Qed.

 Lemma soundX :
  forall (X : arrow_extension) (P : model_type),
  (forall A B : Form Atoms, X _ A B -> sem_implies P A B) -> sound X P.
 Proof.
  intros X P H.
  unfold sound in |- *; simple induction 1.
  apply ONE.
  intros; eapply COMP; eauto.
  intros; apply GAMMA'BETA; apply GAMMA; auto.
  intros; apply BETA'; assumption.  
  intros; apply GAMMA; auto.
  
intros; apply GAMMA'; assumption.
  exact H.
 Qed.


Lemma soundness_NL : sound NL (fun W R => True). 
 Proof.
  apply soundX.
  simple induction 1.
Qed.  


 Lemma sound_add :
  forall (E1 E2 : arrow_extension) (M1 M2 : model_type),
  sound E1 M1 ->
  sound E2 M2 -> sound (add_extension E1 E2) (model_inter M1 M2).
 Proof.
  intros E1 E2 M1 M2 H H0; apply soundX.
  unfold add_extension in |- *; simpl in |- *.
  simple induction 1. 
  intro H2.
  unfold sem_implies in |- *.
  intros.
  case H3; intros.
  unfold sound in H.  
  unfold sem_implies in H.
  eapply H.
  constructor 7.
  eexact H2.
  assumption.
  assumption.
  intro H2.
  unfold model_inter in |- *.
  unfold sem_implies in |- *.
  intros.
  case H3; intros.
  unfold sound in H0.  
  unfold sem_implies in H0.
  eapply H0.
  constructor 7.
  eexact H2.
  assumption.
  assumption.  
 Qed.

 Lemma sound_NLP : sound NLP COM.
 Proof.
  apply soundX.
  unfold sem_implies in |- *.
  simple destruct 1; intros.
  apply COM_lemma; auto.
 Qed.

 Lemma sound_L : sound L ASS.
 Proof.
  apply soundX.
  unfold sem_implies in |- *.
  simple destruct 1; intros.
  apply ASS_lemma; auto.
  apply ASS_lemma_R; auto.
 Qed.

 Lemma sound_LP : sound LP (model_inter COM ASS).
 Proof.
  unfold LP in |- *; apply sound_add.
  apply sound_NLP.
  apply sound_L.
 Qed.
 
 End soundness.
 
 Section completeness.

 Section truth_lemma_spec.
 
 Variable X : arrow_extension.

 (* the syntactical models *)

 Definition WK : Set := Form Atoms.
 Definition RK (A B C : Form Atoms) := weak (arrow X A (Dot B C)).
 Definition valK (p : Atoms) (A : WK) : Prop := weak (arrow X A (At p)).

 (* The truth lemma (for X) provides us a tool to prove completeness *)

 Definition truth_lemma :=
   forall phi A : Form _, weak (arrow X A phi) <-> satisfies RK valK A phi.


 End truth_lemma_spec.
  
 
 Definition model_OK (P : model_type) (X : arrow_extension) := P _ (RK X).

 Definition complete (P : model_type) (X : arrow_extension) :=
   forall A B : Form Atoms, sem_implies P A B -> weak (arrow X A B).


 Lemma truth_lemma_X : forall X : arrow_extension, truth_lemma X.
 Proof.
  intro X.
  unfold truth_lemma, satisfies in |- *; simple induction phi.
  (* atomic formulae *) 
  unfold WK, RK, valK in |- *; simpl in |- *; tauto.
  (* phi = C/B *)
  intros C HC B HB A.
  split; intro.
  simpl in |- *; intros x z H0 H1.
  elim (HB A); intros.
  cut (weak (arrow X z B)).
  intro.
  cut (weak (arrow X x C)).
  intro.
  elim (HC x); tauto.
  apply weak_comp with (Dot A B).
  apply weak_comp with (Dot A z).
  apply H0.
  apply weak_Dot_mono_right; auto.
  apply weak_beta'.  
  auto.
  elim (HB z); tauto.
  simpl in H.
  apply weak_beta.
  elim (HC (Dot A B)); intros H0 H1.
  apply H1.
  apply (H (Dot A B) B).
  unfold RK in |- *; auto with ctl.
  elim (HB B); intros.
  apply H2.
  auto with ctl.

  (* phi =  (B o C) *)
  intros B HB C HC A.
  split; intro.
  simpl in |- *.
  exists B; exists C.
  split.
  unfold RK in |- *; auto.
  split. 
  elim (HB B); auto with ctl.
  elim (HC C); auto with ctl.
  simpl in H; elim H.
  clear H.
  simple induction 1.
  intros x0 H0.
  case H0; intros H1 H2.
  case H2; intros H3 H4.
  apply weak_comp with (Dot x x0).
  apply H1.
  apply weak_comp with (Dot B x0).
  apply weak_Dot_mono_left.
  elim (HB x); auto.
  apply weak_Dot_mono_right.
  elim (HC x0); auto.
 
  (* phi = A\C *)
  intros A HA C HC B.
  split; intro.
  simpl in |- *.
  intros x y H0 H1.
  elim (HC (Dot A B)); intros H2 H3.
  elim (HC x); intros.
  apply H4.
  apply weak_comp with (Dot A B).
  apply weak_comp with (Dot y B).
  auto.
  apply weak_Dot_mono_left.
  elim (HA y); auto.
  apply weak_gamma'.
  auto.
  apply weak_gamma.
  simpl in H.
  elim (HC (Dot A B)); intros.
  apply H1.
  eapply H.
  unfold RK in |- *; apply weak_one.
  elim (HA A); auto with ctl.
 Qed.


 Lemma compl_X :
  forall (X : arrow_extension) (A B : Form Atoms),
  (forall w : WK,
   satisfies (RK X) (valK X) w A -> satisfies (RK X) (valK X) w B) ->
  weak (arrow X A B).
 Proof.
  intros X A B H.
  elim (truth_lemma_X X B A).
  intros.
  apply H1.
  apply H.
  elim (truth_lemma_X X A A).
  auto with ctl.
 Qed.


 Lemma X_complete :
  forall (P : model_type) (X : arrow_extension), model_OK P X -> complete P X.
 Proof.
  unfold complete in |- *; intros P X H0 A B H.        
  apply compl_X; auto.
 Qed.
 
 Lemma NL_OK : model_OK (fun _ _ => True) NL.
 Proof.
  unfold model_OK in |- *; auto.
 Qed.

 Lemma NL_complete : complete (fun _ _ => True) NL.
 Proof.
  apply X_complete; apply NL_OK; auto.
 Qed.

 Lemma LX_OK : forall X : arrow_extension, extends L X -> model_OK ASS X.
 Proof.
  intros X HX.
  unfold model_OK, ASS in |- *.
  unfold RK in |- *; split.
  intros x y z t u H0 H1.
  case H0; intro H2.
  case H1; intro H3.
  exists (Dot y z).
  split.
  split. 
  apply one. 
  apply weak_comp with (Dot (Dot x y) z).
  split.
  apply comp with (Dot t z).
  assumption.
  apply Dot_mono_left.
  assumption.
  split.
  apply alpha'.
  apply HX.
  intros x y z v u H0 H1.
  case H0; intro H2.
  case H1; intro H3.
  exists (Dot x y).
  split.
  split. 
  apply one. 
  apply weak_comp with (Dot x (Dot y z)).
  split.
  apply comp with (Dot x v).
  assumption.
  apply Dot_mono_right.
  assumption.
  split.
  apply alpha.
  apply HX.
 Qed.
 

 Lemma L_OK : model_OK ASS L.
 Proof. 
  apply LX_OK.  
  unfold extends in |- *; auto.
 Qed.


 Lemma L_complete : complete ASS L.
 Proof.
  apply X_complete; apply L_OK.
 Qed.
 
 Lemma NLP_X_OK : forall X : arrow_extension, extends NLP X -> model_OK COM X.
 Proof.
  intros X HX; unfold model_OK, COM, RK in |- *; intros x y z H.
  apply weak_comp with (Dot y z).
  assumption.
  case H.
  intro H1.
  split.  
  apply pi.
  exact HX.
 Qed.

 Lemma NLP_OK : model_OK COM NLP.
 Proof.
  apply NLP_X_OK.
  unfold extends in |- *; auto.
 Qed.

 Lemma NLP_complete : complete COM NLP.
 Proof.
  apply X_complete.
  apply NLP_OK.
 Qed.

 Lemma LPX_OK :
  forall X : arrow_extension,
  extends LP X -> model_OK (model_inter ASS COM) X.
 Proof.
  intros X HX.
  unfold model_inter in |- *.
  unfold model_OK, RK in |- *; split.
  generalize LX_OK.
  unfold model_OK in |- *. 
  intros H.
  unfold RK in H. 
  apply H.
  apply extends_trans with LP.
  unfold LP, extends in |- *; right; auto.
  auto.
  generalize NLP_X_OK.
  unfold model_OK in |- *. 
  intro H.
  unfold RK in H. apply H.
  apply extends_trans with LP.
  unfold LP, extends in |- *; left; auto.
  auto.
 Qed.

Lemma LP_OK : model_OK (model_inter ASS COM) LP.
 Proof.
  apply LPX_OK.  
  unfold extends in |- *; auto.
 Qed.

 Lemma LP_complete : complete (model_inter ASS COM) LP.
 Proof.
  apply X_complete; apply LP_OK.
 Qed.

 End completeness.

End Atoms_fixed.
