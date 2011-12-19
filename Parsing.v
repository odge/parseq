Require Import List Arith Omega Program.
Require Import Noncomputational.

Section Parser.

  Variables s : Set.
  Variable eq_s_dec : forall x y : s, {x = y} + {x <> y}.

  Definition Pre := list s -> Prop.
  Definition Post (t : Set) := list s -> t -> list s -> Prop.

  Program Definition Parser (pre : Pre) (t : Set) (post : Post t) : Set :=
    forall i : { t : list s | pre t },
      list ({ (x, r) : t * list s | post i x r }).

  Program Definition Return (t : Set) (a : t) : Parser (fun _ => True) t (fun i x o => x = a /\ i = o) :=
    fun inp => (a, inp) :: nil.

  Program Definition Bind (a b : Set) P1 P2 Q1 Q2
    (m : Parser P1 a Q1)
    (f : (forall x : a, Parser (P2 x) b (Q2 x))) :
    Parser (fun i => P1 i /\ forall x o, Q1 i x o -> P2 x o)
           b
           (fun i x' o' => exists x o, Q1 i x o /\ Q2 x o x' o') :=
    fun i => @flat_map ({ (x, o) : a * list s | Q1 i x o }) _
      (fun xo => match xo with (x,o) => noncomputational_map _ _ _ _ (f x o) end)
      (m i).
  Next Obligation.
    eauto.
  Defined.

  Definition Fail t : Parser (fun _ => True) t (fun _ _ _ => False) :=
    fun inp =>
      nil.

  Definition Plus t P Q : Parser P t Q -> Parser P t Q -> Parser P t Q :=
    fun m n =>
      fun inp =>
        m inp ++ n inp.

  Program Definition Fix t {P Q} :
    (forall i : { t : list s | P t },
      Parser (fun i' => length i' < length i /\ P i') t Q ->
      list ({ (x, o) : t * list s | Q i x o })) ->
    Parser P t Q :=
    fun Rec =>
      well_founded_induction
        (well_founded_ltof ({ i : list s | P i }) (fun i => length i))
        (fun i => list ({ (x, o) : t * list s | Q i x o }))
        (fun x Rec' => Rec x (fun i => Rec' i _)).

  Program Definition Symbol (x : s) : Parser (fun _ => True) s (fun xs y ys => y = x /\ xs = y :: ys) :=
    fun inp =>
      match inp with
        | nil => nil
        | i::is =>
          if eq_s_dec x i
            then (x, is) :: nil
            else nil
      end.

  Definition fudge_pre_and_post_conditions {t} {P P' : Pre} {Q Q' : Post t} :
    (forall i, P' i -> P i) -> (forall i x r, Q i x r -> Q' i x r) ->
    Parser P t Q -> Parser P' t Q'.
  unfold Parser; intros t P P' Q Q' strength weak f [i iPrf].
  generalize (f (exist (fun t => P t) i (strength i iPrf))).
  apply (@noncomputational_map (t * list s)).
  intros [x r].
  apply weak.
  Defined.

End Parser.

Implicit Arguments Return [s t].
Notation "m >>= f" := (@Bind _ _ _ _ _ _ _ m f) (right associativity, at level 20).
