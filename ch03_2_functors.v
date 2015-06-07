Generalizable All Variables.

Require Import facts.
Require Import ch03_1_categories.

(* =============== Functors =============== *)

(* Definition 3.17 *)
Class Functor
      `(C0 : Category) `(C1 : Category) :=
  {
    fobj      : Ob0 -> Ob1;
    fmor      : forall {a b}, a ~> b -> (fobj a) ~> (fobj b);
    fmor_comp : forall `(f: a ~> b) `(g: b ~> c),
                  fmor (g << f) = (fmor g) << (fmor f);
    fmor_id   : forall a, fmor (id a) = id (fobj a)
  }.

Implicit Arguments fobj [ Ob0 hom0 Ob1 hom1 C0 C1].
Implicit Arguments fmor [ Ob0 hom0 Ob1 hom1 C0 C1 a b].

Lemma Functor_eq :
  forall `(C0: Category) `(C1: Category)
    (F G: Functor C0 C1)
    (Oeq: fobj F = fobj G),
    ((fun a b =>
        match Oeq in _ = V return a ~> b -> (V a) ~> (V b)
        with
          eq_refl => @fmor _ _ _ _ _ _ F a b
        end)
     = (fmor G))
    -> F = G.
Proof.
  intros O0 H0 C0 O1 H1 C1 F G Oeq Meq.
  destruct F; destruct G; simpl in *.
  destruct Oeq.
  assert ((fun a b : O0 => fmor0 a b) = fmor0);
    try apply eta_expansion_dep.
  rewrite H in Meq.
  destruct Meq.
  destruct (proof_irrelevance _ fmor_comp0 fmor_comp1).
  destruct (proof_irrelevance _ fmor_id0 fmor_id1).
  reflexivity.
Qed.

(* Example 3.20 *)
Example fnt_id : forall `(C: Category), Functor C C.
Proof.
  intros O H C.
  apply Build_Functor
  with (fmor := fun _ _ f => f); try reflexivity.
Defined.

Example fnt_const :
  forall `(C0: Category) `(C1: Category) (b: Ob1),
    Functor C0 C1.
Proof.
  intros O0 H0 C0 O1 H1 C1 b.
  apply Build_Functor
  with (fmor := fun _ _ _ => id b); try reflexivity.
  rewrite -> id_r; reflexivity.
Defined.

(* Proposition 3.21 *)
Theorem fnt_preserv_iso :
  forall `(F: Functor) `(f: A ~> B),
    Isomorphism f -> Isomorphism (fmor F f).
Proof.
  intros O0 H0 C0 O1 H1 C1 F A B f Hf.
  destruct Hf as [[f' [inv_comp_a inv_comp_b]]].
  apply Build_Isomorphism.
  exists (fmor F f').
  apply Build_Inversion; rewrite <- fmor_comp; rewrite <- fmor_id.
  - rewrite -> inv_comp_a; reflexivity.
  - rewrite -> inv_comp_b; reflexivity.
Qed.

(* Proposition 3.23 *)
Definition fnt_comp
           `(C0: Category) `(C1: Category) `(C2: Category)
           `(F: @Functor _ _ C0 _ _ C1)
           `(G: @Functor _ _ C1 _ _ C2)
  : Functor C0 C2.
Proof.
  apply Build_Functor
  with (fmor := (fun _ _ f => fmor G (fmor F f))).
  - intros; repeat rewrite -> fmor_comp; reflexivity.
  - intros; repeat rewrite -> fmor_id; reflexivity.
Defined.
Notation "G <<< F" := (@fnt_comp _ _ _ _ _ _ _ _ _ F G)  :category_scope.

Lemma fnt_id_l :
  forall `(F: Functor), F <<< (fnt_id C0) = F.
Proof.
  intros O0 H0 C0 O1 H1 C1 F.
  assert (fobj (F <<< fnt_id C0) = fobj F) as Hfobj.
  { simpl. apply eta_expansion_dep. }
  apply Functor_eq with (Oeq := Hfobj); simpl.
  extensionality a; extensionality b; extensionality f.
  transitivity (match Hfobj in _ = V return (V a) ~> (V b) with eq_refl => (fun f0 : a ~> b => fmor F f0) f end).
  destruct Hfobj; trivial.
  apply JMeq_eq.
  destruct Hfobj; trivial.
Qed.

Lemma fnt_id_r :
  forall `(F: Functor), (fnt_id C1) <<< F = F.
  intros O0 H0 C0 O1 H1 C1 F.
  assert (fobj (fnt_id C1 <<< F) = fobj F) as Hfobj.
  { simpl; apply eta_expansion_dep. }
  apply Functor_eq with (Oeq := Hfobj); simpl.
  extensionality a; extensionality b; extensionality f.
  transitivity (match Hfobj in _ = V return (V a) ~> (V b) with eq_refl => (fun f0 : a ~> b => fmor F f0) f end).
  destruct Hfobj; trivial.
  apply JMeq_eq.
  destruct Hfobj; trivial.
Qed.

Lemma fnt_assoc :
  forall `{C0: Category} `{C1: Category} `{C2: Category} `{C3: Category}
    (F: Functor C0 C1) (G: Functor C1 C2) (H: Functor C2 C3),
    H <<< (G <<< F) = (H <<< G) <<< F.
Proof.
  intros O0 H0 C0 O1 H1 C1 O2 H2 C2 O3 H3 C3 F G H.
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
  intros; repeat rewrite -> fnt_assoc; reflexivity.
Qed.

(* Definition 3.24 *)
Class F_Inversion
      `{C0: Category} `{C1: Category}
      (F: Functor C0 C1) (G: Functor C1 C0) :=
  {
    finv_comp1 : G <<< F = fnt_id C0;
    finv_comp2 : F <<< G = fnt_id C1
  }.

Class F_Isomorphism
      `{C0: Category} `{C1: Category}
      (F: Functor C0 C1) :=
  {
    fiso_comp1:
      exists G : Functor C1 C0, F_Inversion F G
  }.

Class F_Isomorphic
      `{C0: Category} `{C1: Category} : Prop :=
  {
    fiso_ex : exists F: Functor C0 C1, F_Isomorphism F
  }.

(* Remark 3.25 *)
(* The lemmas and theorems below are identical to those in section 3.14 *)

Lemma finv_symm :
  forall `(F: Functor C0 C1) G,
    F_Inversion F G -> F_Inversion G F.
Proof.
  intros O0 H0 C0 O1 H1 C1 F G HFG.
  apply Build_F_Inversion; destruct HFG; assumption.
Qed.

Lemma fiso_finv :
  forall `(F: Functor C0 C1) G,
    F_Isomorphism F ->
    F_Inversion F G ->
    F_Isomorphism G.
Proof.
  intros O0 H0 C0 O1 H1 C1 F G HF HFG.
  apply Build_F_Isomorphism.
  exists F.
  apply finv_symm; assumption.
Qed.

Lemma fnt_equal :
  forall `{C0: Category} `{C1: Category}
    (F: Functor C0 C1) (G H: Functor C1 C0),
    G <<< F = fnt_id C0 -> F <<< H = fnt_id C1 -> G = H.
Proof.
  intros O0 H0 C0 O1 H1 C1 F G H Hfg Hhf.
  rewrite <- fnt_id_r.
  rewrite <- Hfg.
  rewrite <- fnt_assoc.
  rewrite -> Hhf.
  rewrite -> fnt_id_l.
  reflexivity.
Qed.

Theorem double_finv :
  forall `(F: Functor C0 C1) G H,
    F_Inversion F G -> F_Inversion G H -> F = H.
Proof.
  intros O0 H0 C0 O1 H1 C1 F G H Hfg Hgh.
  apply (fnt_equal _ F _).
  - destruct Hfg; assumption.
  - destruct Hgh; assumption.
Qed.

Theorem finv_comp :
  forall `{C0: Category} `{C1: Category} `{C2: Category}
    (F: Functor C0 C1) (G: Functor C1 C2) F' G',
    F_Inversion F F' ->
    F_Inversion G G' ->
    F_Inversion (G <<< F) (F' <<< G').
Proof.
  intros O0 H0 C0 O1 H1 C1 O2 H2 C2 F G F' G' HF HG.
  destruct HF; destruct HG.
  apply Build_F_Inversion.
  - rewrite -> fjuggle; rewrite -> finv_comp5.
    rewrite -> fnt_id_l; assumption.
  - rewrite -> fjuggle; rewrite -> finv_comp4.
    rewrite -> fnt_id_l; assumption.
Qed.

Theorem fiso_comp :
  forall `{C0: Category} `{C1: Category} `{C2: Category}
    (F: Functor C0 C1) (G: Functor C1 C2),
    F_Isomorphism F -> F_Isomorphism G -> F_Isomorphism (G <<< F).
Proof.
  intros O0 H0 C0 O1 H1 C1 O2 H2 C2 F G HF HG.
  apply Build_F_Isomorphism.
  destruct HF as [comp_F]; destruct HG as [comp_G].
  destruct comp_F as [F' HF']; destruct comp_G as [G' HG'].
  exists (F' <<< G').
  apply finv_comp; assumption.
Qed.
