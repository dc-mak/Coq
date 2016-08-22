(* Third set of exercises from CPDT *)
(* Dhruv Makwana *)
(* PS. I miss Vim *)

Require Import Basics Bool Arith List Cpdt.CpdtTactics.

Set Implicit Arguments.

(* a: infinite trees *)
CoInductive inf_tree (A : Type) : Type :=
| Br : inf_tree A -> A -> inf_tree A -> inf_tree A.

Arguments Br {A} _ _ _.

(* b: initialisation for infinite trees *)
CoFixpoint everywhere {A : Type} (x : A) : inf_tree A :=
  Br (everywhere x) x (everywhere x).

(* c: combinator for infinite trees *)
CoFixpoint map {A B C : Type}  (f : A -> B -> C) (left : inf_tree A) (right : inf_tree B) :=
  match left,right with
  | Br ll l lr, Br rl r rr => Br (map f ll rl) (f l r) (map f lr rr)
  end.

(* d: false at all nodes *)
Definition falses := everywhere false.

(* e : alternates between true and false - this alternation makes the proof a lot
 *     more of a pain than the ones presented in the book. *)
CoFixpoint true_false :=
  let rest := Br true_false false true_false in
  Br rest true rest.

(* e: alternative definition
  CoFixpoint alternate (b : bool) : inf_tree bool :=
    let rest := alternate (negb b) in
    Br rest b rest.

  Definition true_false := alternate true. *)

(* Infinite proof of equality.
 * An alternative, (this might be a bit too general, or not operational enough)
 * would have been forall v1 v2 ..., v1 = v2 -> ... so on and would save some effort 
 * in the final proof. *)

CoInductive inf_tree_eq {A : Type} : inf_tree A -> inf_tree A -> Prop :=
| Inf_tree_eq :
    forall v left1 left2 right1 right2,
      inf_tree_eq left1 left2 ->
      inf_tree_eq right1 right2 ->
      inf_tree_eq (Br left1 v right1) (Br left2 v right2).

(* Helper functions *)
Definition hd {A : Type } (tree : inf_tree A) : A :=
  match tree with
  | Br _ v _ => v
  end.

Definition left_tree {A : Type} (tree : inf_tree A) : inf_tree A :=
  match tree with
  | Br left_tree _ _ => left_tree
  end.

Definition right_tree {A : Type} (tree : inf_tree A) : inf_tree A :=
  match tree with
  | Br _ _ right_tree => right_tree
  end.

(* This models the stream_eq_coind given in the book.
   Very general but is it still pragmantically useful for a complex R? *)
Section inf_tree_eq_coind.
  Variable A : Type.
  Variable R : inf_tree A -> inf_tree A -> Prop.
  Hypothesis Br_case_hd : forall t1 t2, R t1 t2 -> hd t1 = hd t2.
  Hypothesis Br_case_rest : forall t1 t2,
      R t1 t2 -> R (left_tree t1) (left_tree t2)
                 /\ R (right_tree t1) (right_tree t2).

  Theorem inf_tree_eq_coind : forall t1 t2, R t1 t2 -> inf_tree_eq t1 t2.

    cofix; destruct t1; destruct t2; intro.
    generalize (Br_case_hd H); intro Heq; simpl in Heq; rewrite Heq.
    constructor; trivial.

    apply inf_tree_eq_coind.
    apply (Br_case_rest H).

    apply inf_tree_eq_coind.
    apply (Br_case_rest H).

  Qed.

End inf_tree_eq_coind.

(* The "trick" is to turn normal "Definition" predicates in to guarded
   CoInductive defintions*)
CoInductive trans_eq (t1 t2 : inf_tree bool) : Prop :=
| Trans_eq : t1 = true_false ->
             t2 = map orb true_false falses ->
             trans_eq t1 t2.


(* Because R must apply directly to a parent *AND* both it's children, we need
   two cases/constructors for each case :-) *)
CoInductive alternate_eq  (t1 t2 : inf_tree bool) : Prop :=
| Gen_eq_true : trans_eq t1 t2 -> alternate_eq t1 t2
| Gen_eq_false : hd t1 = false -> hd t2 = false ->
                 trans_eq (left_tree t1) (left_tree t2) ->
                 trans_eq (right_tree t1) (right_tree t2) ->
                 alternate_eq t1 t2.

(* Since both cases follow in the exact same way - at this stage, I really don't
   know any Ltac so this is probably not the best way to do it. *)
Ltac child_alternate_trans H e1 e2:=
  cofix;
  intros;
  destruct H;
  rewrite e1, e2;
  constructor 2; crush;
  constructor; crush.

Lemma left_alternate_trans : forall t1 t2,
    trans_eq t1 t2 -> alternate_eq (left_tree t1) (left_tree t2).

  child_alternate_trans H H H0.

Qed.

Lemma right_alternate_trans : forall t1 t2,
    trans_eq t1 t2 -> alternate_eq (right_tree t1) (right_tree t2).

  child_alternate_trans H H H0.
  
Qed.

(* Now for the subcases of R *)
Theorem left_alternate : forall t1 t2,
    alternate_eq t1 t2 -> alternate_eq (left_tree t1) (left_tree t2).

  cofix;  intros;  destruct H.
  - apply left_alternate_trans; crush.
  - apply (Gen_eq_true H1).

Qed.

Theorem right_alternate : forall t1 t2,
    alternate_eq t1 t2 -> alternate_eq (right_tree t1) (right_tree t2).

  cofix; intros; destruct H.
  - apply right_alternate_trans; crush.
  - apply (Gen_eq_true H2).
    
Qed.

Theorem true_false_eq_map_orb : inf_tree_eq true_false (map orb true_false falses).
  
  Hint Resolve orb_false_r.
  cofix.
  apply (inf_tree_eq_coind alternate_eq); crush.
  (* What I get for not including head equality in the definition of inf_tree_eq *)
  - case H.
    + intros; case H0.
      intros; rewrite H1, H2.
      simpl; crush.
    + intros; rewrite H0, H1; crush.

  (* The rest follows *)
  - apply left_alternate; crush.
  - apply right_alternate; crush.
  - constructor; constructor; crush.

Qed.

(* Alternative approach, like the frob hack in the book. I got this from the
   other solutions repository, but it makes sense.  *)
Definition inf_tree_id {A : Type} (t : inf_tree A) : inf_tree A :=
  match t with
  | Br l v r => Br l v r
  end.

Lemma id_dummy : forall (A : Type) (t : inf_tree A), t = inf_tree_id t.
  intros.
  destruct t.
  trivial.
Qed.

(* "Dually, co-ﬁxpoints only reduce when enough is known about how their results
    will be used. In particular, a cofix is only expanded when it is the
    discriminee of a match. Rewriting with our superﬁcially silly lemma wrapped
    new matches around the two cofixes, triggering reduction." *)
Theorem is_eq : inf_tree_eq true_false (map orb true_false falses).
  cofix.
  
  Ltac rewrites x y := 
    rewrite (id_dummy x);
    rewrite (id_dummy y);
    simpl;
    constructor; crush.

  rewrites (map orb true_false falses) true_false;
  rewrites (map orb (Br true_false false true_false) (everywhere false))
           (Br true_false false true_false).

  (* Step-by-step for understanding 
  rewrite (id_dummy (map orb (Br true_false false true_false) (everywhere false))).
  rewrite (id_dummy (Br true_false false true_false)).
  simpl.
  constructor.
  unfold falses in is_eq.
  assumption.
  unfold falses in is_eq.
  assumption.
   *)

Qed.
