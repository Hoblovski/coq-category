Reserved Notation "a ~> b" (at level 70, right associativity).
Reserved Notation "b <<< a" (at level 45).
Reserved Notation "a == b" (at level 54).
Reserved Notation "a ~~{ C }~~> b"  (at level 100).

(* definition 3.1 *)
Class Category (O : Type) (hom : O -> O -> Type) :=
  {
    (* The quadruple *)
    Ob    := O;
    hom   := hom
             where "a ~> b" := (hom a b);
    id    :  forall o, (hom o o);
    comp  :  forall a b c, a~>b -> b~>c -> a~>c
             where "g <<< f" := (comp _ _ _ f g);

    (* Conditions *)
    eqv   :  forall a b, (a~>b) -> (a~>b) -> Prop
             where "f == g" := (eqv _ _ f g);
    assoc :  forall a b c d (f: a~>b) (g: b~>c) (h: c~>d),
             h <<< (g <<< f) == (h <<< g) <<< f;
    id_l  :  forall a b (f: a~>b), f <<< id a == f;
    id_r  :  forall a b (f: a~>b), id b <<< f == f
  }.

Notation "a ~> b"         := (@hom _ _ _ a b)      :category_scope.
Notation "f == g"         := (@eqv _ _ _ _ _ f g)  :category_scope.
Notation "g <<< f"        := (comp _ _ _ f g)      :category_scope.
Notation "a ~~{ C }~~> b" := (@hom _ _ C a b) (at level 100) :category_scope.

Open Scope category_scope.
