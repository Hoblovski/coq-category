Generalizable All Variables.

Require Import facts.
Require Import ch03_1_categories.

(*** =============== Functors =============== ***)

(****************** Definition 3.17 ******************)

Class Functor (C : Category) (D : Category) :=
  {
    fobj      : (@Ob C) -> (@Ob D);
    fmor      : forall {a b}, a ~> b -> (fobj a) ~> (fobj b);
    fmor_comp : forall `(f: a ~> b) `(g: b ~> c),
                  fmor (g << f) = (fmor g) << (fmor f);
    fmor_id   : forall a, fmor (id a) = id (fobj a)
  }.

Implicit Arguments fobj [ C D ].
Implicit Arguments fmor [ C D a b ].

Lemma Functor_eq :
  forall `(C: Category) `(D: Category) (F G: Functor C D)
    (Oeq: fobj F = fobj G),
    ((fun a b =>
        match Oeq in _ = V return a ~> b -> (V a) ~> (V b)
        with
          eq_refl => @fmor _ _ F a b
        end)
     = (fmor G))
    -> F = G.
Proof.
  intros C D F G Oeq Meq.
  destruct F; destruct G; simpl in *.
  destruct Oeq.
  assert ((fun a b : Ob => fmor0 a b) = fmor0);
    try apply eta_expansion_dep.
  rewrite H in Meq.
  destruct Meq.
  destruct (proof_irrelevance _ fmor_comp0 fmor_comp1).
  destruct (proof_irrelevance _ fmor_id0 fmor_id1).
  reflexivity.
Qed.

(*** =============== Properties of Functors =============== ***)

(****************** Example 3.20 ******************)
Instance Fnt_id (C: Category) : Functor C C :=
  {
    fmor := fun _ _ f => f
  }.
Proof.
  reflexivity.
  reflexivity.
Defined.

Instance Fnt_const (C D: Category)(b: @Ob D) : Functor C D :=
  {
    fmor := fun _ _ _ => id b
  }.
Proof.
  rewrite -> id_r; reflexivity.
  reflexivity.
Defined.

(****************** Proposition 3.21 ******************)
Theorem Fnt_preserv_iso :
  forall `(F: Functor) `(f: A ~> B),
    Isomorphism f -> Isomorphism (fmor F f).
Proof.
  intros C D F A B f Hf.
  destruct Hf as [[f' [inv_comp_a inv_comp_b]]].
  apply Build_Isomorphism.
  exists (fmor F f').
  apply Build_Inversion; rewrite <- fmor_comp; rewrite <- fmor_id.
  - rewrite -> inv_comp_a; reflexivity.
  - rewrite -> inv_comp_b; reflexivity.
Qed.

(****************** Proposition 3.23 ******************)
Definition Fnt_comp
           (C D E: Category)
           (F: @Functor C D) (G: @Functor D E) : Functor C E.
Proof.
  apply Build_Functor
  with (fmor := (fun _ _ f => fmor G (fmor F f))).
  - intros; repeat rewrite -> fmor_comp; reflexivity.
  - intros; repeat rewrite -> fmor_id; reflexivity.
Defined.
Notation "G <<< F" := (@Fnt_comp _ _ _ F G)  :category_scope.

Lemma Fnt_id_l :
  forall `(F: Functor), F <<< (Fnt_id C) = F.
Proof.
  intros C D F.
  assert (fobj (F <<< Fnt_id C) = fobj F) as Hfobj.
  { simpl. apply eta_expansion_dep. }
  apply Functor_eq with (Oeq := Hfobj); simpl.
  extensionality a; extensionality b; extensionality f.
  transitivity (match Hfobj in _ = V return (V a) ~> (V b) with eq_refl => (fun f0 : a ~> b => fmor F f0) f end).
  destruct Hfobj; trivial.
  apply JMeq_eq.
  destruct Hfobj; trivial.
Qed.

Lemma Fnt_id_r :
  forall `(F: Functor), (Fnt_id D) <<< F = F.
  intros C D F.
  assert (fobj (Fnt_id D <<< F) = fobj F) as Hfobj.
  { simpl; apply eta_expansion_dep. }
  apply Functor_eq with (Oeq := Hfobj); simpl.
  extensionality a; extensionality b; extensionality f.
  transitivity (match Hfobj in _ = V return (V a) ~> (V b) with eq_refl => (fun f0 : a ~> b => fmor F f0) f end).
  destruct Hfobj; trivial.
  apply JMeq_eq.
  destruct Hfobj; trivial.
Qed.

Lemma Fnt_assoc :
  forall `{C0: Category} `{C1: Category} `{C2: Category} `{C3: Category}
    (F: Functor C0 C1) (G: Functor C1 C2) (H: Functor C2 C3),
    H <<< (G <<< F) = (H <<< G) <<< F.
Proof.
  intros C0 C1 C2 C3 F G H.
  assert (fobj (H <<< (G <<< F)) = fobj ((H <<< G) <<< F)) as Hfobj;
    try trivial.
  apply Functor_eq with (Oeq := Hfobj); simpl.
  extensionality a; extensionality b; extensionality f.
  transitivity (match Hfobj in _ = V return (V a) ~> (V b) with eq_refl => (fun f0 : a ~> b => fmor H (fmor G (fmor F f0))) f end).
  destruct Hfobj; trivial.
  apply JMeq_eq.
Admitted.

Lemma fjuggle :
  forall `{C0: Category} `{C1: Category} `{C2: Category}
    `{C3: Category} `{C4: Category}
    (F: Functor C0 C1) (G: Functor C1 C2)
    (H: Functor C2 C3) (K: Functor C3 C4),
    (K <<< H) <<< (G <<< F) = K <<< (H <<< G) <<< F.
Proof.
  intros; repeat rewrite -> Fnt_assoc; reflexivity.
Qed.

(* Instance catCategory : Category := *)
(*   { *)
(*     Ob   := Category; *)
(*     hom  := fun C D => Functor C D; *)
(*     id   := fun C => Fnt_id C; *)
(*     comp := Fnt_comp *)
(*   }. *)
(* Proof. *)
(*   intros; apply Fnt_assoc. *)
(*   intros; apply Fnt_id_l. *)
(*   intros; apply Fnt_id_r. *)
(* Defined. *)

(****************** Definition 3.24 ******************)
Class F_Inversion
      {C D: Category} (F: Functor C D) (G: Functor D C) :=
  {
    finv_comp1 : G <<< F = Fnt_id C;
    finv_comp2 : F <<< G = Fnt_id D
  }.

Class F_Isomorphism
      `(F: Functor) :=
  {
    fiso_comp1:
      exists G : Functor D C, F_Inversion F G
  }.

Class F_Isomorphic (C D: Category) : Prop :=
  {
    fiso_ex : exists F: Functor C D, F_Isomorphism F
  }.

(****************** Remark 3.25 ******************)
(*** The lemmas and theorems are identical to those in 3.14 ***)
Lemma FInv_symm :
  forall `(F: Functor) G,
    F_Inversion F G -> F_Inversion G F.
Proof.
  intros C D F G HFG.
  apply Build_F_Inversion; destruct HFG; assumption.
Qed.

Lemma FIso_finv :
  forall `(F: Functor) G,
    F_Isomorphism F -> F_Inversion F G -> F_Isomorphism G.
Proof.
  intros C D F G HF HFG.
  apply Build_F_Isomorphism.
  exists F.
  apply FInv_symm; assumption.
Qed.

Lemma Fnt_equal :
  forall {C D: Category} (F: Functor C D) (G H: Functor D C),
    G <<< F = Fnt_id C -> F <<< H = Fnt_id D -> G = H.
Proof.
  intros C D F G H Hfg Hhf.
  rewrite <- Fnt_id_r.
  rewrite <- Hfg.
  rewrite <- Fnt_assoc.
  rewrite -> Hhf.
  rewrite -> Fnt_id_l.
  reflexivity.
Qed.

Theorem double_finv :
  forall `(F: Functor) G H,
    F_Inversion F G -> F_Inversion G H -> F = H.
Proof.
  intros C D F G H Hfg Hgh.
  apply (Fnt_equal _ F _).
  - destruct Hfg; assumption.
  - destruct Hgh; assumption.
Qed.

Theorem finv_comp :
  forall {C D E: Category} (F: Functor C D) (G: Functor D E) F' G',
    F_Inversion F F' ->
    F_Inversion G G' ->
    F_Inversion (G <<< F) (F' <<< G').
Proof.
  intros C D E F G F' G' HF HG.
  destruct HF; destruct HG.
  apply Build_F_Inversion.
  - rewrite -> fjuggle; rewrite -> finv_comp5.
    rewrite -> Fnt_id_l; assumption.
  - rewrite -> fjuggle; rewrite -> finv_comp4.
    rewrite -> Fnt_id_l; assumption.
Qed.

(****************** Definition 3.27 ******************)
Definition F_Injective {C D: Category} (F: Functor C D) :=
  forall (c c': @Ob C), fobj F c = fobj F c' -> c = c'.

Definition F_Surjective {C D: Category} (F: Functor C D) :=
  forall (d: @Ob D), {c: @Ob C | fobj F c = d}.

Definition F_Faithful {C D: Category} (F: Functor C D) :=
  forall (a b: @Ob C) (h h': a ~> b), fmor F h = fmor F h' -> h = h'.

Definition F_Full {C D: Category} (F: Functor C D) :=
  forall (a b: @Ob C) (h': fobj F a ~> fobj F b),
    {h: a ~> b | fmor F h = h'}.

(**
 * A faithful but not injective functor is not an embedding.
 * To see why, think of a functor (Functor C D) that is faithful
 * but all objects in C are mapped to the same object in D. In
 * this case there can exist multiple morphisms (with different
 * domain and codomain) in C that maps to the same morphism in D.
 *)

Class Embedding `(F: Functor):=
  {
    emb_f         := F;
    emb_faithful  :  F_Faithful emb_f;
    emb_injective :  F_Injective emb_f
  }.
Coercion emb_f : Embedding >-> Functor.

(****************** Proposition 3.30 ******************)
Theorem fiso_comp :
  forall {C D E: Category} (F: Functor C D) (G: Functor D E),
    F_Isomorphism F -> F_Isomorphism G -> F_Isomorphism (G <<< F).
Proof.
  intros C D E F G HF HG.
  apply Build_F_Isomorphism.
  destruct HF as [comp_F]; destruct HG as [comp_G].
  destruct comp_F as [F' HF']; destruct comp_G as [G' HG'].
  exists (F' <<< G').
  apply finv_comp; assumption.
Qed.

Theorem Fnt_comp_injective :
  forall {C D E: Category} (F: Functor C D) (G: Functor D E),
    F_Injective F -> F_Injective G -> F_Injective (G <<< F).
Proof.
  unfold F_Injective; intros C D E F G HF HG c c' H.
  apply HF; apply HG; assumption.
Qed.

Theorem Fnt_comp_faithful :
  forall {C D E: Category} (F: Functor C D) (G: Functor D E),
    F_Faithful F -> F_Faithful G -> F_Faithful (G <<< F).
Proof.
  unfold F_Faithful; intros C D E F G HF HG a b h h' H.
  apply HF; apply HG; assumption.
Qed.

Theorem Fnt_comp_full :
  forall {C D E: Category} (F: Functor C D) (G: Functor D E),
    F_Full F -> F_Full G -> F_Full (G <<< F).
Proof.
  unfold F_Full; intros C D E F G HF HG a b h'.
  destruct HG with (a := fobj F a)(b := fobj F b)(h' := h') as [h2 Hh2].
  destruct HF with (a := a)(b := b)(h' := h2) as [h1 Hh1].
  exists h1.
  rewrite <- Hh1 in Hh2; assumption.
Qed.

Theorem Emb_comp :
  forall {C D E: Category} (F: Functor C D) (G: Functor D E),
    Embedding F -> Embedding G -> Embedding (G <<< F).
Proof.
  intros C D E F G HF HG.
  destruct HF as [F' F_faithful F_injective];
    destruct HG as [G' G_faithful G_injective].
  apply Build_Embedding.
  apply Fnt_comp_faithful; assumption.
  apply Fnt_comp_injective; assumption.
Qed.

Lemma Fnt_injective_partial :
  forall {C D E: Category} (F: Functor C D) (G: Functor D E),
    F_Injective (G <<< F) -> F_Injective F.
Proof.
  unfold F_Injective; intros C D E F G HFG c c' H.
  apply HFG; simpl. rewrite -> H. reflexivity.
Qed.

Lemma Fnt_faithful_partial :
  forall {C D E: Category} (F: Functor C D) (G: Functor D E),
    F_Faithful (G <<< F) -> F_Faithful F.
Proof.
  unfold F_Faithful. intros C D E F G HFG a b h h' H.
  apply HFG; simpl. rewrite -> H. reflexivity.
Qed.

Theorem Emb_partial :
  forall {C D E: Category} (F: Functor C D) (G: Functor D E),
    Embedding (G <<< F) -> Embedding F.
Proof.
  intros C D E F G HFG.
  destruct HFG as [FG FG_faithful FG_injective].
  apply Build_Embedding.
  apply (Fnt_faithful_partial F G); assumption.
  apply (Fnt_injective_partial F G); assumption.
Qed.

Theorem Prop_3_30_3 :
  forall {C D E: Category} (F: Functor C D) (G: Functor D E),
    F_Surjective F -> F_Full (G <<< F) -> F_Full G.
Proof.
  unfold F_Surjective; unfold F_Full; intros C D E F G HF HFG a' b' h'.
  destruct HF with (d := a') as [a Ha].
  destruct HF with (d := b') as [b Hb].
  destruct Ha; destruct Hb.
  destruct HFG with (a := a)(b := b)(h' := h') as [h Hh].
  exists (fmor F h). apply Hh.
Qed.

(****************** Proposition 3.31 ******************)
Theorem Prop_3_31_1 :
  forall A B (F: Functor A B),
    F_Full F -> F_Faithful F ->
    forall a a' g,
      (exists (f: a ~> a'), fmor F f = g) /\
      (forall (f1 f2: a ~> a'), fmor F f1 = fmor F f2 -> f1 = f2).
Proof.
  intros A B F full faithful a a' g.
  split.
  - destruct full with (a := a)(b := a')(h' := g).
    exists x; assumption.
  - intros f1 f2 Heq.
    apply faithful with (a := a)(b := a')(h := f1)(h' := f2);
      trivial.
Qed.

Theorem Prop_3_31_2 :
  forall A B (F: Functor A B),
    F_Full F -> F_Faithful F ->
    forall a a' (f : a ~> a'),
      (Isomorphism f <-> Isomorphism (fmor F f)).
Proof.
  intros A B F full faithful a a' f.
  split; intros Hiso.
  - apply Fnt_preserv_iso; assumption.
  - destruct Hiso as [[g' [inv_comp1]]].
    (* Here we need fullness *)
    assert (exists (f: a' ~> a), fmor F f = g').
    { apply Prop_3_31_1; assumption. }
    destruct H as [f' Hf'].
    rewrite <- Hf' in *.
    rewrite <- fmor_comp in inv_comp1;
      rewrite <- fmor_comp in inv_comp2;
      rewrite <- fmor_id in inv_comp1;
      rewrite <- fmor_id in inv_comp2.
    (* Here we need faithfulness *)
    assert (forall (f1 f2: a ~> a), fmor F f1 = fmor F f2 -> f1 = f2).
    { apply Prop_3_31_1; try trivial; apply id. }
    apply H in inv_comp1.
    assert (forall (f1 f2: a' ~> a'), fmor F f1 = fmor F f2 -> f1 = f2).
    { apply Prop_3_31_1; try trivial; apply id. }
    apply H0 in inv_comp2.
    apply Build_Isomorphism; exists f'; apply Build_Inversion; trivial.
Qed.
