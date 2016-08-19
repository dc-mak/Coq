(* First set of exercises from CPDT *)
(* Dhruv Makwana *)
(* PS. I miss Vim *)

Require Import Basics Bool Arith List Cpdt.CpdtTactics.

Module Q1.
  (* Q1: ternary truth with commutative `and` and `or` functions. *)
  Inductive truth : Set :=
  | Yes
  | No
  | Maybe.

  Definition not (v1 : truth) : truth :=
    match v1 with
    | Yes => No
    | No => No
    | Maybe => Maybe
    end.

  Definition and (v1 v2 : truth) : truth :=
    match v1, v2 with
    | Yes, Yes => Yes
    | No, _ | _, No => No
    | Maybe, _ | _, Maybe => Maybe
    end.

  Definition or (v1 v2 : truth) : truth :=
    match v1, v2 with
    | No, No => No
    | Yes, _ | _, Yes => Yes
    | Maybe, _ | _, Maybe => Maybe
    end.

  Theorem comm_and : forall v1 v2 : truth, and v1 v2 = and v2 v1.  
    induction v1, v2; crush.
  Qed.

  Theorem comm_or : forall v1 v2 : truth, or v1 v2 = or v2 v1.
    induction v1, v2; crush.
  Qed.

End Q1.

Module Q2.
  (* Q2: Constant time concatenation lists. *)
  Section slist.
    Variable T : Set.

    Inductive slist : Set :=
    | Empty : slist
    | Sing : T -> slist
    | Concat : slist -> slist -> slist.

    Fixpoint flatten (xs : slist) : list T :=
      match xs with
      | Empty => nil
      | Sing x => cons x nil
      | Concat ys zs => flatten ys ++ flatten zs
      end.

    (* This seems too simple, maybe I'm misusnderstanding the question *)
    Theorem flatten_dist_concat : forall ls1 ls2 : slist,
        flatten (Concat ls1 ls2) = flatten ls1 ++ flatten ls2.
      reflexivity.
    Qed.

  End slist.

End Q2.

Module Q3.
  (* Q3: Add variables to the language of Chapter 2 *)
  Inductive binop : Set :=
  | Plus
  | Times.

  Inductive exp : Set :=
  | Const : nat -> exp
  | Binop : binop -> exp -> exp -> exp
  | Var : nat -> exp.

  Definition binopDenote (b : binop) : nat -> nat -> nat :=
    match b with
    | Plus => plus
    | Times => mult
    end.

  Definition var : Set := nat.

  Fixpoint expDenote (e : exp) (env : var -> nat) : nat :=
    match e with
    | Const n => n
    | Var n => env n
    | Binop b e1 e2 => (binopDenote b) (expDenote e1 env) (expDenote e2 env)
    end.

  Fixpoint foldCont (e : exp) : exp :=
    match e with
    | Const _ | Var _ => e
    | Binop b e1 e2 =>
      match foldCont e1, foldCont e2 with
      | Const n1, Const n2 => Const ((binopDenote b) n1 n2)
      | e1', e2' => Binop b e1 e2
      end
    end.

  (* I'll admit, this seems a bit magical, but it does make sense as well. *)
  Theorem foldCont_preserves_expDenote :
    forall (e : exp) (env : var -> nat), expDenote e env = expDenote (foldCont e) env.
    induction e; crush.
    induction foldCont, foldCont; crush.
  Qed.

End Q3.

Module Q4.
  (* Q4: Mutually inductive types instead of dependent ones. *)

  (* Binary operations *)
  (* nat -> nat -> nat *)
  Inductive nat_binop : Set :=
  | NPlus
  | NTimes.

  (* nat -> nat -> bool (to keep things simple) *)
  Inductive bool_binop : Set :=
  | BEqn
  | Blt.

  (* Semantics of binary operations *)
  Definition nat_binop_den (nb : nat_binop) : nat -> nat -> nat :=
    match nb with
    | NPlus => plus
    | NTimes => mult
    end.

  Definition bool_binop_den (bb : bool_binop) : nat -> nat -> bool :=
    match bb with
    | BEqn => beq_nat
    | Blt => leb
    end.

  (* Expressions *)
  Inductive nat_exp : Set :=
  | NConst : nat -> nat_exp
  | NVar : nat -> nat_exp
  | NBinop : nat_binop -> nat_exp -> nat_exp -> nat_exp
  | NIf : bool_exp -> nat_exp -> nat_exp -> nat_exp                               

  with bool_exp : Set :=
       | BConst : bool -> bool_exp
       | BBinop : bool_binop -> nat_exp -> nat_exp -> bool_exp.

  Definition var : Set := nat.
  (* Semantics of expressions *)
  Fixpoint nat_exp_den (e : nat_exp) (env : var -> nat) : nat :=
    match e with
    | NConst n => n
    | NVar n => env n
    | NBinop bn n1 n2 => (nat_binop_den bn) (nat_exp_den n1 env) (nat_exp_den n2 env)
    | NIf b n1 n2 => nat_exp_den (if bool_exp_den b env then n1 else n2) env
    end

  with bool_exp_den (e : bool_exp) (env : var -> nat) : bool :=
         match e with
         | BConst b => b
         | BBinop bb n1 n2 => (bool_binop_den bb) (nat_exp_den n1 env) (nat_exp_den n2 env)
         end.

  (* Constant-folding *)
  Fixpoint nat_constFold (e : nat_exp) : nat_exp :=
    match e with
    | NConst _ | NVar _ => e
    | NBinop nb e1 e2 =>
      match nat_constFold e1, nat_constFold e2 with
      | NConst n1, NConst n2 => NConst (nat_binop_den nb n1 n2)
      | e1', e2' => NBinop nb e1' e2'
      end
    | NIf cond e1 e2 =>
      match bool_constFold cond with
      | BConst b => if b then nat_constFold e1 else nat_constFold e2
      | BBinop bb n1 n2 as cond => NIf cond (nat_constFold e1) (nat_constFold e2)
      end
    end

  with bool_constFold (e : bool_exp) : bool_exp :=
         match e with
         | BConst _ => e
         | BBinop bb n1 n2 =>
           match nat_constFold n1, nat_constFold n2 with
           | NConst n1', NConst n2' => BConst (bool_binop_den bb n1' n2')
           | n1', n2' => BBinop bb n1' n2'
           end
         end.

  Scheme nat_exp_mut := Induction for nat_exp Sort Prop
  with bool_exp_mut := Induction for bool_exp Sort Prop.

  (* Probably not the best proof-script style. However, I don't know how to improve it (yet). *)
  Theorem nat_constFold_preserves_nat_exp_den :
    forall (e : nat_exp) (env : var -> nat),
      nat_exp_den e env = nat_exp_den (nat_constFold e) env.

    apply (nat_exp_mut
             (fun (e : nat_exp) => forall (env : var -> nat),
                  nat_exp_den e env = nat_exp_den (nat_constFold e) env)
             (fun (e : bool_exp) => forall (env : var -> nat),
                  bool_exp_den e env = bool_exp_den (bool_constFold e) env)); crush.

    induction nat_constFold, nat_constFold; crush.
    induction bool_constFold; crush.
    destruct b0; crush.
    induction bool_binop_den; crush.
    induction nat_constFold, nat_constFold; crush.
    
  Qed.

End Q4.

Module Q5.

  (* Q5: Mutually inductive even and odd natural numbers. *)
  Inductive even_nat : Set :=
  | Z : even_nat
  | ES : odd_nat -> even_nat

  with odd_nat : Set :=
       | OS : even_nat -> odd_nat.


  Scheme even_nat_mut := Induction for even_nat Sort Prop
  with odd_nat_mut := Induction for odd_nat Sort Prop.

  Fixpoint even_add (n1 n2 : even_nat) : even_nat :=
    match n1 with
    | Z => n2
    | ES n1' =>  ES (odd_add n1' n2)
    end

  with odd_add (n1 : odd_nat) (n2 : even_nat) : odd_nat :=
     match n1 with
     | OS n1' => OS (even_add n1' n2)
     end.

  (* Although this one was easy in the end, it took a *loong* time to get here.
   * My only advice is to
   *     (a) REALLY PAY ATTENTION TO THE GOAL: mirror the form exactly for the first case
   *     (b) Think and try to get as close a form for the mutual cases. *)
  Theorem even_add_comm : forall (n1 n2 : even_nat), even_add n1 n2 = even_add n2 n1.

    apply (even_nat_mut
             (fun n1 : even_nat => forall n2 : even_nat,
                  even_add n1 n2 = even_add n2 n1)
             (fun n1 : odd_nat => forall n2 : even_nat,
                  ES (odd_add n1 n2) = even_add n2 (ES n1))
          ); crush.

    apply (even_nat_mut
             (fun n1 : even_nat => n1 = even_add n1 Z)
             (fun n1 : odd_nat => n1 = odd_add n1 Z)
          ); crush.

    apply (even_nat_mut
             (fun n1 : even_nat => forall n2 : even_nat,
                  ES (OS (even_add n1 n2)) = even_add n1 (ES (OS n2)))
             (fun n1 : odd_nat => forall n2 : even_nat,
                  OS (ES (odd_add n1 n2)) = odd_add n1 (ES (OS n2)))
          ); crush.
  Qed.
  
End Q5.

Module Q6.

  (* Reflexive (inductive) types *)
  Inductive nat_tree : Set :=
  | Lf : nat -> nat_tree
  | Br : (nat -> nat_tree) -> nat_tree.

  Fixpoint increment (tr : nat_tree) : nat_tree :=
    match tr with
    | Lf n => Lf (S n)
    | Br f => Br (fun n => increment (f n))
    end.

  Fixpoint leapfrog (i : nat) (nt : nat_tree) : nat :=
    match nt with
    | Lf n => n
    | Br f => leapfrog (S i) (f i)
    end.

  Theorem increment_leapfrog : forall (nt : nat_tree) (i : nat),
      S (leapfrog i nt) = leapfrog i (increment nt).

    induction nt; crush.

  Qed.

End Q6.

Module Q7.

  (* Nested inductive types *)
  Inductive btree (T : Set) : Set :=
  | Lf : T -> btree T
  | Br : btree T -> btree T -> btree T.

  Arguments Lf {T} _.
  Arguments Br {T} _ _.
  
  Inductive trexp : Set :=
  | Base : nat -> trexp
  | BTr  : btree trexp -> trexp.

  Fixpoint sum (tr : trexp) : nat :=
    match tr with
    | Base n => n
    | BTr tr' =>
      (fix sum_btree (btr : btree trexp) : nat :=
         match btr with
         | Lf t => sum t
         | Br t1 t2 => sum_btree t1 + sum_btree t2
         end) tr'
    end.

  Fixpoint increment (tr : trexp) : trexp :=
    match tr with
    | Base n => Base (S n)
    | BTr tr' =>
      BTr ((fix incr_btree (btr : btree trexp) : btree trexp :=
              match btr with
              | Lf t => Lf (increment t)
              | Br t1 t2 => Br (incr_btree t1) (incr_btree t2)
              end) tr')
    end.

  Section trexp_ind'.

    (* Computing a "type" = theorem for an arbitrary btree *)
    Fixpoint All {T : Set} (P : T -> Prop) (btr : btree T) : Prop :=
      match btr with
      | Lf lf => P lf
      | Br t1 t2 => All P t1 /\ All P t2
      end.

    (* I did look at the solutions, but this does makes sense now.
     * The tricky bit for me was the term/type "distinction" of proof/value vs theorem/type and
     * understanding the meaning of the syntax. *)

    (* Synonyms for "global" implicit arguments *)
    Variable P : trexp -> Prop.
    Hypothesis Base_case : forall (n : nat), P (Base n).
    Hypothesis BTr_case : forall (btr : btree trexp), All P btr -> P (BTr btr).


    Fixpoint trexp_ind' (tr : trexp) : P tr :=
      match tr with
      | Base n => Base_case n
      | BTr tr' =>
        (* Constructing a proof of the type of the theorem we assumed earlier *)
        BTr_case tr' ((fix btree_ind (btr : btree trexp) : All P btr :=
                     match btr with
                     | Lf lf => trexp_ind' lf
                     | Br t1 t2 => conj (btree_ind t1) (btree_ind t2)
                     end) tr')
      end.
  End trexp_ind'.

  Theorem incr_larger_total : forall (tr : trexp), sum (increment tr) >= sum tr.
    induction tr using trexp_ind'; crush.
    induction btr; crush.
  Qed.

End Q7.

Module Q8.

  Inductive nat_btree : Set :=
  | Lf : nat_btree
  | Br : nat_btree -> nat -> nat_btree -> nat_btree.
  
  Definition toProp (b : nat_btree) :=
    match b with
    | Lf => False
    | Br _ _ _ => True
    end.
  
  Theorem leaf_not_node : forall (n : nat) (t1 t2 : nat_btree), Lf <> Br t1 n t2.

    red.
    intros.
    change (toProp Lf).
    rewrite H.
    simpl.
    trivial.

  Qed.

  (* Originally I wrote this without a default parameter (returned O for Lf) *)
  Definition node_val (def : nat) (tr : nat_btree) : nat :=
    match tr with
    | Lf => def
    | Br _ n _ => n
    end.
  
  Theorem eq_nodes_nums : forall (def nl nr : nat) (tll tlr trl trr : nat_btree),
      Br tll nl tlr = Br trl nr trr -> nl = nr.

    intros.
    change (node_val def (Br tll nl tlr) = node_val def (Br trl nr trr)).
    rewrite H.
    reflexivity.

  Qed.

End Q8.