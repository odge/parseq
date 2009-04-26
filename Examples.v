Require Import List Arith Omega Program.
Require Import Parsing.

(*
 * example 1:
 *  <par> ::= <epsilon> | '(' <par> ')' <par>
 *
 * example 2:
 *  <mul>  ::= <sum>  | <sum> '*' <mul>  | <sum> '/' <mul>
 *  <sum>  ::= <unit> | <unit> '+' <sum> | <unit> '-' <unit>
 *  <unit> ::= <num>  | '(' <mul> ')'
 *
 *)

Module Example_1.
  
  Inductive token := open | close.
  
  Definition eq_token_dec : forall t t' : token, {t = t'} + {t <> t'}.
  decide equality.
  Defined.
  
  Inductive par := epsilon : par | wrappend : par -> par -> par.
  
  Fixpoint print (p : par) : list token :=
    match p with
      | epsilon => nil
      | wrappend m n => (open::nil) ++ print m ++ (close::nil) ++ print n
    end.
  
  Program Definition par_parser : Parser token (fun _ => True) par (fun x p y => x = print p ++ y /\ length y <= length x) :=
    Fix token par (fun i parRec =>
      Plus _ _ (fun i' => i = i') _
        (fudge_pre_and_post_conditions _ _ _
          (Return epsilon))
        (fudge_pre_and_post_conditions _ _ _
          (Symbol token eq_token_dec open >>= fun _ =>
           parRec >>= fun m =>
           Symbol token eq_token_dec close >>= fun _ =>
           parRec >>= fun n =>
           Return (wrappend m n)))
      i).
  
  Next Obligation.
    intuition; subst; simpl in *; auto.
  Defined.
  Next Obligation.
    intuition; subst; simpl in *; auto.
    rewrite app_ass; reflexivity.
    omega.
  Defined.

  Definition parse : list token -> option par :=
    fun input =>
      (fix result_loop results :=
        match results with
          | exist (pair x nil) _ :: _ => Some x
          | _ :: results => result_loop results
          | nil => None
        end)
      (par_parser (exist (fun _ => True) input I)).
  
  Eval compute in parse (open::open::close::nil).
  Eval compute in parse (open::open::close::close::nil).
  Eval compute in parse (open::open::close::open::close::close::nil).
  
End Example_1.

Module Example_2.
  
  Inductive token := mul | div | add | sub | open | close | num (_:nat).
  
  Definition eq_token_dec : forall t t' : token, {t = t'} + {t <> t'}.
  destruct t; destruct t';
    try (left; congruence) || (right; discriminate).
  destruct (eq_nat_dec n n0).
    left; congruence.
    right; intro Q; injection Q; assumption.
  Defined.
  
  Inductive mulP := mul1 (_:sumP) | mul2 (_:sumP) (_:mulP) | mul3 (_:sumP) (_:mulP)
       with sumP := sum1 (_:unitP) | sum2 (_:unitP) (_:sumP) | sum3 (_:unitP) (_:sumP)
       with unitP := unit1 (_:nat) | unit2 (_:mulP).
  
  Fixpoint printM (m : mulP) : list token :=
    match m with
      | mul1 s => printS s
      | mul2 s m => printS s ++ (mul::nil) ++ printM m
      | mul3 s m => printS s ++ (div::nil) ++ printM m
    end
  with printS (s : sumP) : list token :=
    match s with
      | sum1 u => printU u
      | sum2 u s => printU u ++ (add::nil) ++ printS s
      | sum3 u s => printU u ++ (sub::nil) ++ printS s
    end
  with printU (u : unitP) : list token :=
    match u with
      | unit1 n => num n::nil
      | unit2 m => (open::nil) ++ printM m ++ (close::nil)
    end.
  
  Program Definition NumToken : Parser token (fun _ => True) nat (fun xs y ys => xs = num y :: ys) :=
    fun inp =>
      match inp with
        | num n::xs => (n, xs) :: nil
        | _ => nil
      end.
  
  Definition par_parser : Parser token (fun _ => True) mulP (fun x p y => x = printM p ++ y /\ length y <= length x).
  refine (
    Fix token mulP (fun i mulRec =>
      let unitParser : Parser token (fun i' => length i' <= length (proj1_sig i)) unitP (fun x p y => x = printU p ++ y /\ length y <= length x) :=
        Plus _ _ _ _
         (fudge_pre_and_post_conditions _ _ _
           (NumToken >>= fun n =>
            Return (unit1 n)))
         (fudge_pre_and_post_conditions _ _ _
           (Symbol token eq_token_dec open >>= fun _ =>
            mulRec >>= fun m =>
            Symbol token eq_token_dec close >>= fun _ =>
            Return (unit2 m))) in
      let sumParser : Parser token (fun i' => length i' <= length (proj1_sig i)) sumP (fun x p y => x = printS p ++ y /\ length y <= length x) :=
        Fix token sumP (fun i sumRec =>
          fudge_pre_and_post_conditions _ _ _
            (Plus _ _ (fun i' => i' = proj1_sig i)
                      (fun x p y => x = printS p ++ y /\ length y <= length x)
              (fudge_pre_and_post_conditions _ _ _
                (unitParser >>= fun u =>
                 Return (sum1 u)))
            (Plus _ _ (fun i' => i' = proj1_sig i)
                      (fun x p y => x = printS p ++ y /\ length y <= length x)
              (fudge_pre_and_post_conditions _ _ _
                (unitParser >>= fun u =>
                 Symbol token eq_token_dec add >>= fun _ =>
                 sumRec >>= fun s =>
                 Return (sum2 u s)))
              (fudge_pre_and_post_conditions _ _ _
                (unitParser >>= fun u =>
                 Symbol token eq_token_dec sub >>= fun _ =>
                 sumRec >>= fun s =>
                 Return (sum3 u s)))))
            (exist _ (proj1_sig i) (refl_equal (proj1_sig i)))) in
      fudge_pre_and_post_conditions _ _ _
        (Plus _ _ (fun i' => i' = proj1_sig i)
                  (fun x p y => x = printM p ++ y /\ length y <= length x)
          (fudge_pre_and_post_conditions _ _ _
            (sumParser >>= fun s =>
             Return (mul1 s)))
        (Plus _ _ (fun i' => i' = proj1_sig i)
                  (fun x p y => x = printM p ++ y /\ length y <= length x)
          (fudge_pre_and_post_conditions _ _ _
            (sumParser >>= fun s =>
             Symbol token eq_token_dec mul >>= fun _ =>
             mulRec >>= fun m =>
             Return (mul2 s m)))
          (fudge_pre_and_post_conditions _ _ _
            (sumParser >>= fun s =>
             Symbol token eq_token_dec div >>= fun _ =>
             mulRec >>= fun m =>
             Return (mul3 s m)))))
        (exist _ (proj1_sig i) (refl_equal (proj1_sig i))))
  );
  
  try solve [
    intuition; destruct_conjs; subst; simpl in *;
      ( reflexivity || congruence || omega ||
        trivial || auto || rewrite app_ass; reflexivity ) ].
  
  Defined.
  
  Inductive expr :=
  | mulE : expr -> expr -> expr
  | divE : expr -> expr -> expr
  | addE : expr -> expr -> expr
  | subE : expr -> expr -> expr
  | natE : nat -> expr.
  
  Fixpoint exprifyM (m : mulP) : expr :=
    match m with
      | mul1 s => exprifyS s
      | mul2 s m => mulE (exprifyS s) (exprifyM m)
      | mul3 s m => divE (exprifyS s) (exprifyM m)
    end
  with exprifyS (s : sumP) : expr :=
    match s with
      | sum1 u => exprifyU u
      | sum2 u s => addE (exprifyU u) (exprifyS s)
      | sum3 u s => subE (exprifyU u) (exprifyS s)
    end
  with exprifyU (u : unitP) : expr :=
    match u with
      | unit1 n => natE n
      | unit2 m => exprifyM m
    end.
  
  Program Fixpoint mulifyE (e : expr) : { m : mulP | exprifyM m = e } :=
    match e with
      | mulE x y => mul2 (sumifyE x) (mulifyE y)
      | divE x y => mul3 (sumifyE x) (mulifyE y)
      | addE x y => mul1 (sum2 (unitifyE x) (sumifyE y))
      | subE x y => mul1 (sum3 (unitifyE x) (sumifyE y))
      | natE n => mul1 (sum1 (unit1 n))
    end
  with sumifyE (e : expr) : { s : sumP | exprifyS s = e } :=
    match e with
      | addE x y => sum2 (unitifyE x) (sumifyE y)
      | subE x y => sum3 (unitifyE x) (sumifyE y)
      | natE n => sum1 (unit1 n)
      | mulE x y => sum1 (unit2 (mul2 (sumifyE x) (mulifyE y)))
      | divE x y => sum1 (unit2 (mul3 (sumifyE x) (mulifyE y)))
    end
  with unitifyE (e : expr) : { u : unitP | exprifyU u = e } :=
    match e with
      | natE n => unit1 n
      | mulE x y => unit2 (mul2 (sumifyE x) (mulifyE y))
      | divE x y => unit2 (mul3 (sumifyE x) (mulifyE y))
      | addE x y => unit2 (mul1 (sum2 (unitifyE x) (sumifyE y)))
      | subE x y => unit2 (mul1 (sum3 (unitifyE x) (sumifyE y)))
    end.
  
  Program Definition expr_parser : Parser token (fun _ => True) expr (fun _ _ _ => True) :=
    fudge_pre_and_post_conditions _ _ _
      (par_parser >>= fun m =>
       Return (exprifyM m)).
  
  Definition test_parser (l : list token) : option expr :=
    (fix loop results :=
      match results with
        | nil => None
        | exist (pair x nil) _ :: _ => Some x
        | _ :: results => loop results
      end)
    (expr_parser (exist _ l I)).
  
  (*
     (1+1*3-7*(6+4))/24
  *)
  
  Eval vm_compute in test_parser
    (open::num 1::add::num 1::mul::num 3::sub::num 7::mul::open::num 6::add::num 4::close::close::div::num 24::nil).

  (*
   * = Some
   *     (divE
   *        (mulE (addE (natE 1) (natE 1))
   *           (mulE (subE (natE 3) (natE 7)) (addE (natE 6) (natE 4))))
   *        (natE 24))
   *)

End Example_2.
