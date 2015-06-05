Require Import Coq.Setoids.Setoid.
Require Setoid.

Generalizable All Variables.

Reserved Notation "A ~> B" (at level 70, right associativity).
Reserved Notation "g <<< f" (at level 45).

(* =============== Categories =============== *)

(* Definition 3.1 *)
Class Category
      (Ob : Type)
      (hom: Ob -> Ob -> Type) :=
  {
    (* The quadruple *)
    Ob    := Ob;
    hom   := hom
             where "A ~> B" := (hom A B);
    id    :  `(hom A A);
    comp  :  forall A B C, (hom A B) -> (hom B C) -> (hom A C)
             where "g <<< f" := (comp _ _ _ f g);

    (* Constraints *)
    assoc :  forall A B C D (f: A~>B) (g: B~>C) (h: C~>D),
             h <<< (g <<< f) = (h <<< g) <<< f;
    id_l  :  forall `(f: A~>B), f <<< id A = f;
    id_r  :  forall `(f: A~>B), id B <<< f = f
  }.

Notation "A ~> B"         := (@hom _ _ _ A B)  :category_scope.
Notation "g <<< f"        := (comp _ _ _ f g)  :category_scope.

Open Scope category_scope.

Lemma juggle1 :
  forall `{_:Category}`(f:A~>B)`(g:B~>C)`(h:C~>D)`(k:D~>E),
    k <<< (h <<< (g <<< f)) = k <<< (h <<< g) <<< f.
Proof.
  intros; repeat rewrite -> assoc; reflexivity.
Qed.

Lemma juggle2 :
  forall `{_:Category}`(f:A~>B)`(g:B~>C)`(h:C~>D)`(k:D~>E),
    ((k <<< h) <<< g) <<< f = k <<< (h <<< g) <<< f.
Proof.
  intros; repeat rewrite -> assoc; reflexivity.
Qed.

Lemma juggle3 :
  forall `{_:Category}`(f:A~>B)`(g:B~>C)`(h:C~>D)`(k:D~>E),
    (k <<< h) <<< (g <<< f) = k <<< (h <<< g) <<< f.
Proof.
  intros; repeat rewrite -> assoc; reflexivity.
Qed.

(* Remark 3.2 *)

Definition dom Ob H `(c: Category Ob H) `(_ : H A B)
  := A.

Definition cod Ob H `(c: Category Ob H) `(_ : H A B)
  := B.

(* =============== The Duality Principle =============== *)

(* Definition 3.5 *)
(* Definition dual Ob H (c: Category Ob H) : Category Ob H. *)
(* Proof. *)
(*   destruct c. *)
(*   apply Build_Category *)
(*   with (id := id0) *)
(*        (comp := fun a b c f g => a b c g f). *)
(* Defined. *)

(* Remark 3.7 *)
(* Lemma double_dual : forall Ob H (c: Category Ob H), (dual (dual c)) = c. *)
(* Proof. destruct c; reflexivity. Qed. *)

(* How can we formalize the duality principle? *)

(* =============== Isomorphism =============== *)

(* Definition 3.8 *)
Class Inversion `{c: Category} `(f: A~>B) g : Prop :=
  {
    inv_comp1 : g <<< f = id A;
    inv_comp2 : f <<< g = id B
  }.

Class Isomorphism `{c: Category} `(f: A ~> B) : Prop :=
  {
    iso_comp1: exists g, Inversion f g
  }.

(* Proposition 3.10 *)
Theorem morph_equal :
  forall `(c: Category) `(f: A ~> B) (g h: B ~> A),
    g <<< f = id A -> f <<< h = id B -> g = h.
Proof.
  intros O H c A B f g h Hfg Hhf.
  rewrite <- id_r.
  rewrite <- Hfg.
  rewrite <- assoc.
  rewrite -> Hhf.
  rewrite -> id_l.
  reflexivity.
Qed.

(* Corollary 3.11 *)
Theorem inv_unique :
  forall `(c: Category) `(f: A ~> B) g h,
    Inversion f g -> Inversion f h -> g = h.
Proof.
  intros O H c A B f g h Hgf Hhf.
  apply (morph_equal _ f).
  - destruct Hgf; assumption.
  - destruct Hhf; assumption.
Qed.

(* Proposition 3.14 *)

Lemma inv_symm :
  forall `(_: Category) `(f: A ~> B) g,
    Inversion f g -> Inversion g f.
Proof.
  intros O H c A B f g Hfg.
  apply Build_Inversion; destruct Hfg; assumption.
Qed.

Theorem iso_inv :
  forall `(_: Category) `(f: A ~> B) g,
    Isomorphism f -> Inversion f g -> Isomorphism g.
Proof.
  intros O H c A B f g Hf Hfg.
  apply Build_Isomorphism.
  exists f.
  apply inv_symm; assumption.
Qed.

Theorem double_inv :
  forall `(_: Category) `(f: A ~> B) g h,
    Inversion f g -> Inversion g h -> f = h.
Proof.
  intros O H c A B f g h Hfg Hgh.
  apply (morph_equal _ g).
  - destruct Hfg; assumption.
  - destruct Hgh; assumption.
Qed.

Theorem inv_comp :
  forall `(_: Category) `(f: A ~> B) `(g: B ~> C) f' g',
    Inversion f f' ->
    Inversion g g' ->
    Inversion (g <<< f) (f' <<< g').
Proof.
  intros O H c A B f C g f' g' Hf Hg.
  destruct Hf; destruct Hg.
  apply Build_Inversion.
  - rewrite -> juggle3; rewrite -> inv_comp5.
    rewrite -> id_l; assumption.
  - rewrite -> juggle3; rewrite -> inv_comp4.
    rewrite -> id_l; assumption.
Qed.

Theorem iso_comp :
  forall `(_: Category) `(f: A ~> B) `(g: B ~> C),
    Isomorphism f -> Isomorphism g -> Isomorphism (g <<< f).
Proof.
  intros O H c A B f C g Hf Hg.
  apply Build_Isomorphism.
  destruct Hf as [comp_f]; destruct Hg as [comp_g].
  destruct comp_f; destruct comp_g.
  exists (x <<< x0).
  apply inv_comp; assumption.
Qed.

(* Definition 3.15 *)
Class Isomorphic `{c: Category} (A B: Ob) : Prop :=
  {
    iso_ex : exists f: A ~> B, Isomorphism f
  }.
