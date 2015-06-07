Generalizable All Variables.

Reserved Notation "a ~> b" (at level 70, right associativity).
Reserved Notation "g << f" (at level 45).
Reserved Notation "G <<< F" (at level 45).

(* =============== Categories =============== *)

(* Definition 3.1 *)
Class Category :=
  {
    (* The quadruple *)
    Ob    :  Type;
    hom   :  Ob -> Ob -> Type
             where "a ~> b" := (hom a b);
    id    :  `(hom a a);
    comp  :  forall a b c, (hom a b) -> (hom b c) -> (hom a c)
             where "g << f" := (comp _ _ _ f g);

    (* Constraints *)
    assoc :  forall a b c d (f: a~>b) (g: b~>c) (h: c~>d),
             h << (g << f) = (h << g) << f;
    id_l  :  forall `(f: a~>b), f << id a = f;
    id_r  :  forall `(f: a~>b), id b << f = f
  }.

Notation "a ~> b"        := (@hom _ a b)  :category_scope.
Notation "g << f"        := (comp _ _ _ f g)  :category_scope.

Open Scope category_scope.

Lemma juggle1 :
  forall `{_:Category}`(f:a~>b)`(g:b~>c)`(h:c~>d)`(k:d~>e),
    k << (h << (g << f)) = k << (h << g) << f.
Proof.
  intros; repeat rewrite -> assoc; reflexivity.
Qed.

Lemma juggle2 :
  forall `{_:Category}`(f:a~>b)`(g:b~>c)`(h:c~>d)`(k:d~>e),
    ((k << h) << g) << f = k << (h << g) << f.
Proof.
  intros; repeat rewrite -> assoc; reflexivity.
Qed.

Lemma juggle3 :
  forall `{_:Category}`(f:a~>b)`(g:b~>c)`(h:c~>d)`(k:d~>e),
    (k << h) << (g << f) = k << (h << g) << f.
Proof.
  intros; repeat rewrite -> assoc; reflexivity.
Qed.

(* Remark 3.2 *)

Definition dom `(C: Category) (a b: Ob) (_ : a ~> b)
  := a.

Definition cod `(C: Category) (a b: Ob) (_ : a ~> b)
  := b.

(* Example 3.3 *)

Instance catSet : Category :=
  {
    Ob   := Type;
    hom  := fun a b => a -> b;
    id   := fun a x => x;
    comp := fun a b c (f: a -> b) (g: b -> c) x => g (f x)
  }.
Proof.
  trivial.
  trivial.
  trivial.
Defined.

(* =============== The Duality Principle =============== *)

(* Definition 3.5 *)
Definition dual `(C: Category) :
  Category.
Proof.
  apply (Build_Category)
  with (Ob := Ob)
       (hom := (fun a b => b ~> a))
       (id := id)
       (comp := fun a b c f g => comp c b a g f).
  - symmetry; apply assoc.
  - intros; apply id_r.
  - intros; apply id_l.
Defined.

(* Remark 3.7 *)
Lemma double_dual : forall `(C: Category), (dual (dual C)) = C.
Proof.
  Admitted.

(* TODO: How can we formalize the duality principle? *)

(* =============== Isomorphism =============== *)

(* Definition 3.8 *)
Class Inversion `{C: Category} `(f: a~>b) g : Prop :=
  {
    inv_comp1 : g << f = id a;
    inv_comp2 : f << g = id b
  }.

Class Isomorphism `{C: Category} `(f: a ~> b) : Prop :=
  {
    iso_comp1: exists g, Inversion f g
  }.

(* Proposition 3.10 *)
Theorem morph_equal :
  forall `(_: Category) `(f: a ~> b) (g h: b ~> a),
    g << f = id a -> f << h = id b -> g = h.
Proof.
  intros C a b f g h Hfg Hhf.
  rewrite <- id_r.
  rewrite <- Hfg.
  rewrite <- assoc.
  rewrite -> Hhf.
  rewrite -> id_l.
  reflexivity.
Qed.

(* Corollary 3.11 *)
Theorem inv_unique :
  forall `(_: Category) `(f: a ~> b) g h,
    Inversion f g -> Inversion f h -> g = h.
Proof.
  intros C a b f g h Hgf Hhf.
  apply (morph_equal _ f).
  - destruct Hgf; assumption.
  - destruct Hhf; assumption.
Qed.

(* Proposition 3.14 *)

Lemma inv_symm :
  forall `(_: Category) `(f: a ~> b) g,
    Inversion f g -> Inversion g f.
Proof.
  intros C a b f g Hfg.
  apply Build_Inversion; destruct Hfg; assumption.
Qed.

Theorem iso_inv :
  forall `(_: Category) `(f: a ~> b) g,
    Isomorphism f -> Inversion f g -> Isomorphism g.
Proof.
  intros C a b f g Hf Hfg.
  apply Build_Isomorphism.
  exists f.
  apply inv_symm; assumption.
Qed.

Theorem double_inv :
  forall `(_: Category) `(f: a ~> b) g h,
    Inversion f g -> Inversion g h -> f = h.
Proof.
  intros C a b f g h Hfg Hgh.
  apply (morph_equal _ g).
  - destruct Hfg; assumption.
  - destruct Hgh; assumption.
Qed.

Theorem inv_comp :
  forall `(_: Category) `(f: a ~> b) `(g: b ~> c) f' g',
    Inversion f f' ->
    Inversion g g' ->
    Inversion (g << f) (f' << g').
Proof.
  intros C a b f c g f' g' Hf Hg.
  destruct Hf; destruct Hg.
  apply Build_Inversion.
  - rewrite -> juggle3; rewrite -> inv_comp5.
    rewrite -> id_l; assumption.
  - rewrite -> juggle3; rewrite -> inv_comp4.
    rewrite -> id_l; assumption.
Qed.

Theorem iso_comp :
  forall `(_: Category) `(f: a ~> b) `(g: b ~> c),
    Isomorphism f -> Isomorphism g -> Isomorphism (g << f).
Proof.
  intros C a b f c g Hf Hg.
  apply Build_Isomorphism.
  destruct Hf as [comp_f]; destruct Hg as [comp_g].
  destruct comp_f; destruct comp_g.
  exists (x << x0).
  apply inv_comp; assumption.
Qed.

(* Definition 3.15 *)
Class Isomorphic `{c: Category} (a b: Ob) : Prop :=
  {
    iso_ex : exists f: a ~> b, Isomorphism f
  }.
