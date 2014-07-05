Require Import List.

Section Noncomputational.

  Variable T : Type.
  Variables P Q : T -> Prop.

  Variable cast : forall x, P x -> Q x.

  Fixpoint noncomputational_map (ps : list ({ t | P t })) : list ({ t | Q t }) :=
    match ps with
      | nil =>
        nil
      | exist x xPrf :: ps =>
        exist (fun x => Q x) x (cast x xPrf) :: noncomputational_map ps
    end.

  Theorem noncomputational_map_identity :
    forall l,
      map (@proj1_sig _ _) l = map (@proj1_sig _ _) (noncomputational_map l).
    induction l as [|[x xPrf] l]; simpl; congruence.
  Qed.

End Noncomputational.

Extract Inlined Constant noncomputational_map => "id".

