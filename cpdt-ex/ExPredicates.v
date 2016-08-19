(* Second set of exercises from CPDT *)
(* Dhruv Makwana *)
(* PS. I miss Vim *)

(* NOTE: Type-level equality is basically Prolog-style unification.
		 `destruct` and `induction` work fine across values and types
			 WHEN THEY ARE VARIABLES (universally quantified/forall)
		 but for instantiated values in type constructors,
			 they are replaced with variables
			 THEN CASE ANALYSED
		 so in this case use `inversion`.

 * NOTE: `auto` does a proof search using ONLY REGISTERED HINTS.

 * NOTE: ?Metavar is a way to unify auto-gen variable to a metavariable (match in proofs).

 * NOTE: eapply and eauto are (for now) propositional (finite depth) tactics with unification variables

 * NOTE: for flexibility (in multiple induction), use nested foralls
    - should have folllowed this earlier for Q4.
 
 *)

Require Import Basics Bool Arith List Cpdt.CpdtTactics.

Module Q1.
  Theorem true_false : (True \/ False) /\ (False \/ True).

    split.
    left.
    constructor.
    right.
    constructor.

  Qed.

  Theorem double_neg_id : forall P : Prop, P -> ~~P.

    intros.
    unfold not.
    intros.
    apply H0.
    assumption.

  Qed.

  Theorem and_dist_or : forall (P Q R : Prop),
      P /\ (Q \/ R) -> (P /\ Q) \/ (P /\ R).

    intros.
    destruct H as [A [B | C]].
    - left.
      + split.
        assumption.
        assumption.
      
    - right.
      + split.
        assumption.
        assumption.
  Qed.

End Q1.

Module Q2.
  Variables (T : Set)
            (x : T)
            (P : T -> Prop)
            (Q : T -> T -> Prop)
            (f : T -> T).

  Theorem taut :
    P x -> (forall x, P x -> exists y,  Q x y)
    -> (forall x y, Q x y -> Q y (f y))
    -> exists z, Q z (f z).

    intros.
    assert (exists y : T, Q x y).
    apply (H0 x H).
    destruct H2.
    assert (Q x0 (f x0)).
    apply (H1 x x0 H2).
    exists x0.
    assumption.

  Qed.

End Q2.

Module Q3.

  Inductive six_mult : nat -> Prop :=
  | Six_O : six_mult 0
  | Six_M : forall n : nat, six_mult n -> six_mult (6 + n).

  Inductive ten_mult : nat -> Prop :=
  | Ten_O : ten_mult 0
  | Ten_M  : forall n : nat, ten_mult n -> ten_mult (10 + n).

  Inductive six_or_ten : nat -> Prop :=
  | SixTen : forall n : nat, six_mult n \/ ten_mult n -> six_or_ten n.

  (* Deeply unsatisfying but oh well, automation comes later *)
  Theorem thirteen_not_six_or_ten : ~ (six_or_ten 13).

    unfold not.
    inversion 1.
    destruct H0 as [A | B].
    - inversion A.
      inversion H2.
      inversion H4.

    - inversion B.
      inversion H2.

  Qed.

  Inductive odd_nat : nat -> Prop :=
  | OddN : forall m : nat, (exists n : nat, m = 1 + n + n) -> odd_nat m.

  Lemma six_not_odd : forall n : nat, six_mult n -> ~(odd_nat n).

    induction 1; crush.
    - inversion H; crush.

    - induction IHsix_mult.
      inversion H0; crush.
      constructor.
      exists (x-3).
      apply (fun n m => plus_reg_l n m 6).
      crush.

  Qed.

  Lemma ten_not_odd : forall n : nat, ten_mult n -> ~(odd_nat n).

    induction 1; crush.
    - inversion H; crush.

    - induction IHten_mult.
      inversion H0; crush.
      constructor.
      exists (x-5).
      apply (fun n m => plus_reg_l n m 10).
      crush.

  Qed.
  
  Theorem six_ten_not_odd :
    forall n : nat, six_mult n \/ ten_mult n -> ~(odd_nat n).

    crush.
    apply (six_not_odd n); assumption.
    apply (ten_not_odd n); assumption.
    
  Qed.

End Q3.

Module Q4.

  Set Implicit Arguments.

  (* a: var as a synonym for nat *)
  Definition var := nat.

  (*
  Inductive type : Set :=
  | Nat
  | Pair : type -> type -> type.
  
  Inductive exp : type -> Set :=
  | NatExp : nat -> exp Nat
  | Plus : exp Nat -> exp Nat -> exp Nat
  | PairExp : forall t1, exp t1  -> forall t2, exp t2 -> exp (Pair t1 t2)
  | Fst : forall t1 t2, exp (Pair t1 t2) -> exp t1
  | Snd : forall t1 t2, exp (Pair t1 t2) -> exp t2
  | VarExp : var -> forall t, exp t.

  Check PairExp (NatExp 0) (NatExp 0).
  *)

  (* b *)
  Inductive exp : Set :=
  | NatExp : nat -> exp
  | Plus : nat -> nat -> exp
  | PExp : exp -> exp -> exp
  | Fst : exp -> exp
  | Snd : exp -> exp
  | VarExp : var -> exp.

  (* c *)
  Inductive cmd : Set :=
  | Exp : exp -> cmd
  | Assign: var -> exp -> cmd -> cmd.

  Section rules.
    Variable T : Set.
    Variables (unary : nat -> T) (pair : T -> T -> T).
    
    Fixpoint eval (e : exp) (env : var -> T) : T :=
      match e with
      | NatExp n => unary n
      | Plus m n => unary (m + n)
      | VarExp n => env n
      | PExp e1 e2 => pair (eval e1 env) (eval e2 env)
      (* Since we don't have exceptions [totality ftw] and optionals are just
       * too much effort, Fst and Snd on non-Pair expressions are no-ops *)
      | Fst e => match e with
                 | PExp e _
                 | e => eval e env
                 end
      | Snd e => match e with
                 | PExp _ e
                 | e => eval e env
                 end
      end.

    Definition insert (key : var) (val : T) (env : var -> T) (n : var) :=
      if eq_nat_dec key n then val else env n.
    
    Fixpoint run (cmd : cmd) (env : var -> T) : T :=
      match cmd with
      | Exp exp => eval exp env
      | Assign var exp cmd =>
        let v := eval exp env in
        run cmd (insert var v env)
      end.

  End rules.

  (* d *)
  Inductive val : Set :=
  | Val : nat -> val
  | PVal : val -> val -> val.

  (* e: variable assignments have type var -> val *)
  (* f: big-step evaluation of expressions *)
  Definition eval_val (e : exp) (env : var -> val) :=
    eval Val PVal e env.

  (* g: big-step evaluation of run *)
  Definition run_val (cmd : cmd) (env : var -> val) :=
    run Val PVal cmd env.
  
  (* h: variable typings *)
  Inductive type : Set :=
  | Nat
  | PType : type -> type -> type.

  (* i : typing judgements for expressions *)
  Definition eval_type (e : exp) (env : var -> type) :=
    eval (fun _ => Nat)  PType e env.

  (* i : typing judgement for commands *)
  Definition run_type (cmd : cmd) (env : var -> type) :=
    run (fun _ => Nat) PType cmd env.

  Eval simpl in eval_type (Fst (NatExp 0)) (fun _ => Nat).

  Fixpoint type_of (v : val) : type :=
    match v with
    | Val _ => Nat
    | PVal v1 v2 => PType (type_of v1) (type_of v2)
    end.

  (* j: predicate of agreement of variable assignment and variable typing *)
  Definition varsType (val_env : var -> val) (type_env : var -> type) : Prop :=
    forall (key : var), type_of (val_env key) = type_env key.

  Theorem env_ind :
    forall (val_env : var -> val)
           (type_env : var -> type)
           (P : val -> type -> Prop)
           (newkey : var)
           (newval : val)
           (newtype : type),
      (forall (key : var), P (val_env key) (type_env key)) ->
      P newval newtype ->
      (forall (key : var),
          P (insert newkey newval val_env key) (insert newkey newtype type_env key)).

    
    intros;
      unfold insert;
      match goal with
      | [ |- context [ Nat.eq_dec ?X ?Y ]] =>  destruct (Nat.eq_dec X Y)
      end;
      crush.

  Qed.

  (* Arguments env_ind {_} {_} _ _ _ _ _ _ _. *)
  (* Check env_ind. *)
  
  Theorem updateEnv : forall (val_env : var -> val) (type_env : var -> type),
      varsType val_env type_env ->
      forall (v : val) (t : type),
		  type_of v = t ->
		  forall (k : var), varsType (insert k v val_env) (insert k t type_env).

    unfold varsType;
      unfold insert;
      crush;
      match goal with
      | [ |- context [ Nat.eq_dec ?X ?Y ]] =>  destruct (Nat.eq_dec X Y)
      end;
      crush.
    
  Qed.

  (* k: How you express the theorems is very important *)
  Theorem type_preserve_exp :
    forall (val_env : var -> val) (type_env : var -> type) (e : exp),
          varsType val_env type_env ->
          type_of (eval_val e val_env) = eval_type e type_env.

    induction e; crush;
      induction e; crush.
    
  Qed.

  (* This took me 4 days. As it turns out, stating the formula in this way is possibly the only way to show this (nicely) *)
  Theorem type_preserve_cmd :
    forall (c : cmd),
      (forall (ve : var -> val) (te : var -> type),
          varsType ve te -> type_of (run_val c ve) = run_type c te).

    induction c;
      crush' (type_preserve_exp, updateEnv) tt.
    
    apply IHc;
      crush' (type_preserve_exp, updateEnv) tt;
      apply (updateEnv H);
      crush.

  Qed.
  
End Q4.
