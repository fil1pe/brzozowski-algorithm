Require Import Lia.
Require Export DFA.

(* The pigeonhole principle *)
Lemma pigeonhole {X} (l1 l2 : list X) :
  (forall x1 x2 : X, {x1 = x2} + {x1 <> x2}) ->
  (forall x, In x l2 -> In x l1) -> length l2 > length l1 ->
  exists l2a l2b l2c y, l2 = l2a ++ [y] ++ l2b ++ [y] ++ l2c.
Proof.
  intro eq_dec; revert l1; induction l2 as [|y l2 IH]; intros l1 H H0.
  - simpl in H0; nia.
  - destruct l1 as [|x l1].
    destruct (H y); left; auto.
    destruct (in_dec eq_dec y l2) as [H1|H1].
    + apply in_split in H1; destruct H1 as [l2a [l2b H1]]; subst;
      exists nil, l2a, l2b, y; auto.
    + assert (H2: In y (x::l1)). apply H; left; auto.
      apply in_split in H2; destruct H2 as [l1a [l1b H2]];
      destruct IH with (l1a ++ l1b) as [l2a [l2b [l2c [z H4]]]].
      * intros z H3; apply in_or_app; rewrite H2 in H; specialize (H z);
        assert (H4: In z (l1a ++ y :: l1b)). apply H; right; auto.
        apply in_app_or in H4; destruct H4 as [H4|H4].
        left; auto.
        destruct H4 as [H4|H4].
        subst; contradiction.
        right; auto.
      * assert (H3: length l1 = length (l1a ++ l1b)). {
          rewrite app_length; assert (H3: length ([x] ++ l1) = length (l1a ++ [y] ++ l1b)).
            simpl ([x] ++ l1); rewrite H2; auto.
          rewrite app_length, app_length, app_length in H3; simpl in H3; nia.
        }
        simpl in H0; rewrite app_length; rewrite app_length in H3; nia.
      * exists (y::l2a), l2b, l2c, z; subst; auto.
Qed.

Section Pumping.

Context {State Symbol : Type}.
Definition Word := @Word Symbol.
Hypothesis State_eq_dec : forall (x1 x2:State), { x1 = x2 } + { x1 <> x2 }.
Hypothesis Symbol_eq_dec : forall (x1 x2:Symbol), { x1 = x2 } + { x1 <> x2 }.
Definition NFA := @NFA State Symbol.
Definition transitionf := transitionf State_eq_dec Symbol_eq_dec.
Definition nfa_accepts := nfa_accepts State_eq_dec Symbol_eq_dec.
Definition reachable_state := reachable_state State_eq_dec Symbol_eq_dec.

(* We need a definition of path with history *)
Inductive path' (g:NFA) : list State->list Symbol->Prop :=
  | path'_nil q : path' g [q] nil
  | path'_trans p q1 q2 w a : In (transition q1 a q2) g -> path' g (q2::p) w ->
    path' g (q1::q2::p) (a::w).

(* It is equivalent to the former *)
Lemma path'_correct g q1 q2 w :
  w <> nil ->
  path g q1 q2 w <-> exists l, path' g (q1::l ++ [q2]) w.
Proof.
  intro H; split; intro H0.
  - induction H0.
    intuition.
    destruct w as [|b w].
    + inversion H1; subst.
      exists nil; simpl.
      apply path'_trans.
      intuition.
      constructor.
    + assert (H2: b::w <> nil).
      intro H2; discriminate.
      apply IHpath in H2; clear IHpath.
      destruct H2 as [l H2].
      exists (q2::l); simpl.
      apply path'_trans; intuition.
  - destruct H0 as [l H0];
    generalize dependent q1;
    generalize dependent l;
    induction w as [|a w IH];
    intros l q1 H0.
    intuition.
    destruct w as [|b w].
    + inversion H0; subst.
      inversion H6; subst.
      destruct l.
      2: destruct l; discriminate.
      simpl in H2; injection H2; intros; subst.
      apply path_trans with q2.
      intuition.
      constructor.
    + inversion H0; subst.
      destruct l; simpl in *.
      * destruct p.
        2: discriminate.
        inversion H0;
        inversion H10.
      * injection H2; intros; subst.
        apply IH in H6.
        2: intro conta; discriminate.
        apply path_trans with s; intuition.
Qed.

(* The history length is equal to the word length plus one *)
Lemma path'_length g l w :
  path' g l w -> length l = S (length w).
Proof.
  intro H; induction H.
  intuition.
  simpl in *; nia.
Qed.

(* All terms in the history are states *)
Lemma path'_in_states g l w :
  w <> nil -> path' g l w -> (forall q, In q l -> In q (states g)).
Proof.
  intros H H0.
  induction H0.
  intuition.
  destruct w as [|b w].
  - inversion H1; subst.
    apply transition_states_alphabet in H0.
    intros q [H2|H2].
    2: apply in_singleton in H2.
    1,2: subst; intuition.
  - intros q [H3|H3].
    subst; apply transition_states_alphabet in H0; intuition.
    apply IHpath' in H3.
    intuition.
    intro contra; discriminate.
Qed.

(* We can decompose the path' *)
Lemma app_path' g l1 q l2 w :
  path' g (l1 ++ [q] ++ l2) w -> exists w1 w2, w = w1 ++ w2 /\ path' g (l1 ++ [q]) w1 /\
  path' g (q::l2) w2.
Proof.
  generalize dependent w;
  induction l1 as [|q1 l1 IH];
  intros w H.
  exists nil, w; split.
  intuition.
  split.
  constructor.
  intuition.
  inversion H; subst.
  destruct l1; discriminate.
  rewrite H1 in H4.
  apply IH in H4; destruct H4 as [w1 [w2 [H4 [H5 H6]]]].
  exists (a::w1), w2; split.
  simpl; rewrite H4; intuition.
  split.
  destruct l1 as [|q0 l1]; injection H1; intros; subst.
  apply path'_trans; intuition.
  simpl; apply path'_trans; intuition.
  intuition.
Qed.

(* And compose *)
Lemma path'_app g l1 q l2 w1 w2 :
  path' g (l1 ++ [q]) w1 ->
  path' g (q::l2) w2 ->
  path' g (l1 ++ [q] ++ l2) (w1 ++ w2).
Proof.
  intros H H0;
  generalize dependent w1;
  induction l1 as [|q1 l1 IH];
  intros w1 H.
  inversion H; subst; intuition.
  inversion H; subst.
  destruct l1; discriminate.
  rewrite H2 in H5; apply IH in H5.
  destruct l1 as [|q0 l1];
  injection H2; intros; subst;
  simpl; apply path'_trans; intuition.
Qed.


(** Pumping lemma: **)

(*
  For every path, there's another path from and to the same states through a word
  whose length is less or qual to the number of states
*)
Lemma pumping' g q1 l q2 w :
  q1 <> q2 ->
  path' g (q1::l ++ [q2]) w ->
  exists l' w', path' g (q1::l' ++ [q2]) w' /\
  length w' <= length (states g).
Proof.
  generalize dependent q1;
  generalize dependent l;
  induction w as [|a w IH];
  intros l q1 H H0. {
    apply path'_length in H0;
    simpl in H0; rewrite app_length in H0;
    simpl in H0; nia.
  }
  inversion H0; subst.
  destruct l as [|q3' l].
  - simpl in H2; injection H2; intros; subst.
    exists nil, [a].
    simpl; split.
    apply path'_trans.
    intuition.
    constructor.
    apply transition_states_alphabet in H4; destruct H4 as [H4 _];
    apply in_split in H4; destruct H4 as [l1 [l2 H4]]; rewrite H4;
    destruct l1; simpl; nia.
  - injection H2; intros; subst; clear H2.
    destruct (State_eq_dec q3' q2) as [H2|H2].
    subst; exists nil, [a]; split.
    simpl; apply path'_trans.
    intuition.
    constructor.
    apply transition_states_alphabet in H4; destruct H4 as [H4 _];
    apply in_split in H4; destruct H4 as [l1 [l2 H4]]; rewrite H4;
    destruct l1; simpl; nia.
    apply IH in H6.
    2: intuition.
    destruct H6 as [l' [w' [H6 H7]]].
    destruct (Compare_dec.le_gt_dec (length (a::w')) (length (states g))).
    exists (q3'::l'), (a::w'); split.
    simpl; apply path'_trans.
    1-3: intuition.
    clear IH; assert (path' g (q1 :: q3' :: l' ++ [q2]) (a::w')).
    apply path'_trans; intuition.
    assert (exists l2a l2b l2c y, q1 :: q3' :: l' ++ [q2] = l2a ++ [y] ++ l2b ++ [y] ++ l2c).
    apply pigeonhole with (states g).
    intuition.
    apply path'_in_states with (a :: w').
    intro contra; discriminate.
    intuition.
    apply path'_length in H1.
    simpl in *; nia.
    destruct H3 as [l1 [l2 [l3 [q H3]]]]; rewrite H3 in H1.
    apply app_path' in H1; destruct H1 as [w1 [w2 [H1 [H8 H9]]]].
    replace (q :: l2 ++ [q] ++ l3) with ((q :: l2) ++ [q] ++ l3) in H9.
    2: intuition.
    apply app_path' in H9; destruct H9 as [w2' [w3 [H9 [H10 H11]]]].
    assert (path' g (l1 ++ [q] ++ l3) (w1 ++ w3)).
    apply path'_app; intuition.
    destruct l1 as [|q'' l1]; destruct l3 as [|q' l3 _] using rev_ind;
    subst; simpl in *; injection H3; intros; subst.
    + replace (q3' :: l' ++ [q2]) with ((q3' :: l') ++ [q2]) in H9.
      2: intuition.
      apply app_inj_tail in H9; destruct H9; subst.
      destruct H; intuition.
    + replace (q3' :: l' ++ [q2]) with ((q3' :: l') ++ [q2]) in H9.
      replace (l2 ++ q :: l3 ++ [q']) with ((l2 ++ q :: l3) ++ [q']) in H9.
      2,3: repeat rewrite <- app_assoc; intuition.
      apply app_inj_tail in H9; destruct H9; subst.
      exists l3, (w1 ++ w3); split.
      intuition.
      rewrite app_length.
      assert (length (w1 ++ w2' ++ w3) <= S (length (states g))).
      rewrite <- H1; simpl; nia.
      repeat rewrite app_length in H12.
      apply path'_length in H10.
      simpl in H10; rewrite app_length in H10.
      simpl in *; nia.
    + replace (q3' :: l' ++ [q2]) with ((q3' :: l') ++ [q2]) in H9.
      replace (l1 ++ q :: l2 ++ [q]) with ((l1 ++ q :: l2) ++ [q]) in H9.
      2,3: repeat rewrite <- app_assoc; intuition.
      apply app_inj_tail in H9; destruct H9; subst.
      exists l1, (w1 ++ w3); split.
      intuition.
      rewrite app_length.
      assert (length (w1 ++ w2' ++ w3) <= S (length (states g))).
      rewrite <- H1; simpl; nia.
      repeat rewrite app_length in H12.
      apply path'_length in H10.
      simpl in H10; rewrite app_length in H10.
      simpl in *; nia.
    + replace (q3' :: l' ++ [q2]) with ((q3' :: l') ++ [q2]) in H9.
      replace (l1 ++ q :: l2 ++ q :: l3 ++ [q']) with ((l1 ++ q :: l2 ++ q :: l3) ++ [q']) in H9.
      apply app_inj_tail in H9; destruct H9; subst.
      exists (l1 ++ q :: l3), (w1 ++ w3); split.
      rewrite <- app_assoc; intuition.
      2,3: repeat (rewrite <- app_assoc; simpl); intuition.
      rewrite app_length.
      assert (length (w1 ++ w2' ++ w3) <= S (length (states g))).
      rewrite <- H1; simpl; nia.
      repeat rewrite app_length in H12.
      apply path'_length in H10.
      simpl in H10; rewrite app_length in H10.
      simpl in *; nia.
Qed.

Lemma pumping (g:NFA) q1 q2 w :
  path g q1 q2 w ->
  exists w', path g q1 q2 w' /\
  length w' <= length (states g).
Proof.
  intro H; destruct w as [|a w].
  - inversion H; subst.
    exists nil; split.
    intuition.
    simpl; nia.
  - apply path'_correct in H.
    2: intro contra; discriminate.
    destruct H as [l H].
    destruct (State_eq_dec q1 q2) as [H0|H0].
    subst; exists nil; split; try constructor; simpl; nia.
    apply pumping' in H.
    2: intuition.
    destruct H as [l' [w' [H H1]]].
    exists w'; split.
    2: intuition.
    inversion H; subst.
    destruct l'; discriminate.
    apply path'_correct.
    intro contra; discriminate.
    exists l'; intuition.
Qed.


Definition remove_state := @NFA.remove_state State Symbol State_eq_dec.
Definition alphabet_nodup := @alphabet_nodup State Symbol Symbol_eq_dec.

(* Decides whether there's a path from q1 to q2 with length n *)
Fixpoint is_reachableb g q1 q2 n :=
  if State_eq_dec q1 q2 then true
  else
    match n with
    | 0 => false
    | S n => existsb (fun q3 => is_reachableb (remove_state g q1) q3 q2 n) (flat_map (fun a => transitionf g [q1] a) (alphabet_nodup g))
    end.

(* The path taken by is_reachableb *)
Inductive path'' (g:NFA) : list State->list Symbol->Prop :=
  | path''_nil q : path'' g [q] nil
  | path''_trans p q1 q2 w a : In (transition q1 a q2) g -> path'' (remove_state g q1) (q2::p) w ->
    path'' g (q1::q2::p) (a::w).

(* A path'' in a NFA without a state exists in the NFA with it *)
Lemma path''_with_state g q l w :
  path'' (remove_state g q) l w -> path'' g l w.
Proof.
  intro H;
  remember (remove_state g q) as g' eqn:H0;
  generalize dependent q;
  generalize dependent g;
  induction H; intros; subst.
  apply path''_nil.
  apply path''_trans.
  {
    clear H0 IHpath'' w p.
    induction g0.
    contradiction.
    simpl; simpl in H.
    destruct a0.
    2: intuition.
    1-4: apply in_app_or in H; destruct H as [H|H].
    2,4,6,8: intuition.
    1-3: destruct (State_eq_dec q0 q); try destruct H; try contradiction; discriminate.
    destruct (State_eq_dec q0 q), (State_eq_dec q3 q); subst; try destruct H; try contradiction.
    inversion H; left; auto.
  }
  apply IHpath'' with (q:=q).
  apply remove_state_comm.
Qed.

(* If a state is not in a given path, it can be removed from the NFA without breaking the path *)
Lemma path''_without_state g q l w :
  ~ In q l -> path'' g l w ->
  path'' (remove_state g q) l w.
Proof.
  intros H H0.
  induction H0.
  apply path''_nil.
  apply path''_trans.
  2: unfold remove_state; rewrite remove_state_comm; apply IHpath''; intros [contra|contra];
  subst; intuition.
  clear IHpath'' H1.
  induction g.
  contradiction.
  simpl in H0; destruct H0 as [H0|H0].
  2: {
    destruct a0; simpl.
    1,3-5: apply in_or_app; right.
    1-5: intuition.
  }
  subst; simpl.
  destruct (State_eq_dec q1 q); destruct (State_eq_dec q2 q); subst.
  1-3: apply in_or_app; left; apply H; intuition.
  left; auto.
Qed.

(* path' is equivalent to path'' *)
Lemma path''_correct1 g l w :
  path'' g l w -> path' g l w.
Proof.
  intro H.
  induction H.
  apply path'_nil.
  apply path'_trans.
  auto.
  remember (q2::p) as l eqn:H1;
  pose proof IHpath'' as H2;
  clear IHpath'' H1 H0 H a q2.
  induction H2.
  apply path'_nil.
  apply path'_trans.
  2: auto.
  remember (transition q0 a q2) as x eqn:H3;
  clear H3 H2 IHpath' a q0 q2 p0 w p.
  induction g.
  contradiction.
  destruct a; simpl in H.
  2: intuition.
  1-3: destruct (State_eq_dec q q1) as [H0|H0].
  1,3,5: intuition.
  1-3: destruct H as [H|H]; subst; intuition.
  destruct (State_eq_dec q0 q1) as [H0|H0].
  intuition.
  destruct (State_eq_dec q2 q1) as [H1|H1].
  intuition.
  destruct H as [H|H]; subst; intuition.
Qed.

Lemma path''_correct2 g q1 q2 l1 w1 :
  q1 <> q2 ->
  path' g (q1::l1 ++ [q2]) w1 -> exists l2 w2, length w2 <= length w1 /\ path'' g (q1::l2 ++ [q2]) w2.
Proof.
  intros H H0;
  remember (q1::l1 ++ [q2]) as L1 eqn:H1;
  generalize dependent q1;
  generalize dependent l1;
  induction H0; intros.
  inversion H1; destruct l1 as [|q3 l1]; discriminate.
  inversion H2; subst; clear H2.
  destruct l1 as [|q1 l1].
  {
    inversion H5; inversion H0; subst;
    clear H7 H5 IHpath'.
    2: discriminate.
    exists nil, [a]; split.
    intuition.
    apply path''_trans.
    auto.
    apply path''_nil.
  }
  inversion H5; subst.
  specialize (IHpath' l1 q1).
  destruct (State_eq_dec q1 q2) as [H6|H6].
  {
    subst; exists nil, [a]; split.
    simpl; intuition.
    apply path''_trans.
    auto.
    apply path''_nil.
  }
  pose H6 as H7;
  apply IHpath' in H7.
  2: auto.
  destruct H7 as [l2 [w2 [H7 H8]]].
  destruct (in_dec State_eq_dec q3 (q1::l2)) as [H9|H9].
  2: {
    exists (q1::l2), (a::w2); simpl; split.
    intuition.
    apply path''_trans.
    auto.
    apply path''_without_state.
    2: auto.
    intro contra; destruct contra as [contra|contra]; subst.
    2: apply in_app_or in contra; repeat destruct contra as [contra|contra]; subst.
    1-4: intuition.
  }
  destruct H9 as [H9|H9].
  subst; exists l2, w2; simpl; split; intuition.
  apply in_split in H9; destruct H9 as [l21 [l22 H9]]; subst.
  assert (H9: exists w3, length w3 <= length w2 /\ path'' g (q3::l22 ++ [q2]) w3).
  2: {
    destruct H9 as [w3 [H9 H10]].
    exists l22, w3; simpl; split.
    lia.
    auto.
  }
  clear H7 H6 H5 H1 H IHpath' H0 l1 a w.
  remember (q1 :: l21) as l1 eqn:H9.
  remember (q3::l22 ++ [q2]) as l2 eqn:H10.
  replace (q1 :: (l21 ++ q3 :: l22) ++ [q2]) with (l1 ++ l2) in H8.
  2: rewrite <- app_assoc; rewrite H9, H10; auto.
  remember (l1 ++ l2) as l eqn:H.
  assert (H0: l2 <> nil).
  intro contra; subst; discriminate.
  clear H9 H10 l21 l22.
  generalize dependent l2;
  generalize dependent l1;
  induction H8; intros.
  {
    exists nil; split.
    auto.
    destruct l1, l2.
    discriminate.
    2: contradiction.
    2: destruct l1; discriminate.
    destruct l2.
    2: discriminate.
    apply path''_nil.
  }
  destruct l1.
  2: {
    inversion H0; clear H0; subst.
    apply IHpath'' in H4.
    2: auto.
    destruct H4 as [w3 [H4 H5]].
    exists w3; split.
    simpl; intuition.
    apply path''_with_state with (q:=s); auto.
  }
  destruct l2.
  contradiction.
  simpl in H0; inversion H0; subst.
  specialize (IHpath'' nil (q4 :: p)).
  assert (H2: q4 :: p = [] ++ q4 :: p).
  simpl; auto.
  apply IHpath'' in H2.
  2: intro contra; discriminate.
  destruct H2 as [w3 [H2 H3]].
  exists (a::w3); split.
  simpl; intuition.
  apply path''_trans; auto.
Qed.

(* is_reachableb and path'' are equivalent *)
Lemma is_reachableb_path'' g q1 q2 n :
  is_reachableb g q1 q2 n = true -> q1 = q2 \/ exists w p, length w <= n /\ path'' g (q1::p ++ [q2]) w.
Proof.
  generalize dependent q1;
  generalize dependent g;
  induction n as [|n IH];
  intros g q1 H; simpl in H.
  {
    destruct (State_eq_dec q1 q2) as [H0|H0].
    auto.
    discriminate.
  }
  destruct (State_eq_dec q1 q2) as [H0|H0].
  auto.
  right.
  apply existsb_exists in H; destruct H as [q3 [H1 H2]].
  apply IH in H2.
  apply in_flat_map in H1; destruct H1 as [a [H1 H4]].
  destruct H2 as [H2|[w [p [H2 H3]]]].
  + subst.
    exists [a], nil; split.
    intuition.
    simpl; apply path''_trans.
    2: apply path''_nil.
    apply transition_transitionf in H4; auto.
  + exists (a::w), (q3::p); split.
    simpl; intuition.
    destruct w as [|b w].
    inversion H3; destruct p; discriminate.
    simpl; apply path''_trans.
    apply transition_transitionf in H4; auto.
    auto.
Qed.

(* The reciprocal *)
Lemma path''_is_reachableb g q1 q2 n w p :
  length w <= n /\ path'' g (q1::p ++ [q2]) w -> is_reachableb g q1 q2 n = true.
Proof.
  intros [H0 H]; generalize dependent n;
  remember (q1 :: p ++ [q2]) as p' eqn:H0;
  generalize dependent q1;
  generalize dependent p;
  induction H; intros.
  {
    inversion H0.
    destruct p; discriminate.
  }
  destruct n as [|n].
  inversion H2.
  simpl; destruct (State_eq_dec q3 q2) as [H3|H3].
  auto.
  destruct p0 as [|p0]; simpl; inversion H1; subst.
  - apply existsb_exists; exists q2; split.
    2: {
      destruct n; simpl; destruct (State_eq_dec q2 q2) as [H4|H4].
      1,3: auto.
      1,2: contradiction.
    }
    apply in_flat_map; exists a; split.
    apply nodup_In; apply transition_states_alphabet in H; intuition.
    apply transition_transitionf; auto.
  - specialize (IHpath'' p1 p0).
    assert (H4: p0 :: p1 ++ [q2] = p0 :: p1 ++ [q2]).
    auto.
    apply IHpath'' with (n:=n) in H4.
    2: intuition.
    apply existsb_exists; exists p0; split.
    2: auto.
    apply in_flat_map; exists a; split.
    apply nodup_In; apply transition_states_alphabet in H; intuition.
    apply transition_transitionf; auto.
Qed.

(* is_reachableb is correct *)
Lemma is_reachableb_correct g q1 q2 n :
  is_reachableb g q1 q2 n = true <-> exists w, length w <= n /\ path g q1 q2 w.
Proof.
  split; intro H.
  - apply is_reachableb_path'' in H; destruct H as [H|H]; subst.
    + exists nil; split.
      simpl; lia.
      apply path_nil.
    + destruct H as [w [p [H H0]]].
      apply path''_correct1 in H0.
      pose proof (path'_correct g q1 q2 w) as H1.
      assert (H2: w <> nil). {
        destruct w.
        inversion H0; destruct p; discriminate.
        intro contra; discriminate.
      }
      exists w; split.
      2: apply H1.
      3: exists p.
      1-3: auto.
  - destruct H as [w [H H0]].
    pose proof (path'_correct g q1 q2 w) as H1.
    destruct w as [|a w].
    {
      inversion H0; subst.
      destruct n as [|n].
      1,2: simpl; destruct (State_eq_dec q2 q2) as [H2|H2];
      try contradiction; auto.
    }
    assert (a :: w <> []).
    intro contra; discriminate.
    apply H1 in H2; apply H2 in H0; clear H2 H1.
    destruct H0 as [p H0].
    pose proof (path''_correct2 g q1 q2 p (a::w)).
    destruct (State_eq_dec q1 q2) as [H2|H2].
    {
      subst; destruct n as [|n].
      1,2: simpl; destruct (State_eq_dec q2 q2) as [H2|H2];
      try contradiction; auto.
    }
    apply H1 in H2.
    2: auto.
    destruct H2 as [l' [w' [H2 H3]]].
    apply path''_is_reachableb with (w:=w') (p:=l'); split.
    simpl in H, H2; lia.
    auto.
Qed.

(* Reachable state decider *)
Lemma reachable_state_dec (g:NFA) :
  forall q, {reachable_state g q} + {~reachable_state g q}.
Proof.
  intro q.
  assert ({ exists q0, In q0 (start_states g) /\ is_reachableb g q0 q (length (states g)) = true } +
  { ~ exists q0, In q0 (start_states g) /\ is_reachableb g q0 q (length (states g)) = true }).
  2: {
    destruct H as [H|H].
    - left; destruct H as [q0 [H H0]].
      apply is_reachableb_correct in H0.
      destruct H0 as [w [H0 H1]].
      exists w; apply ext_transitionf_generalize with q0.
      2: apply path_ext_transitionf.
      1,2: intuition.
    - right; intros [w H0]; apply H; clear H.
      apply ext_transitionf_singleton in H0.
      destruct H0 as [q0 [H0 H1]]; exists q0; split.
      intuition.
      apply path_ext_transitionf, pumping in H1.
      clear w; destruct H1 as [w [H1 H2]].
      apply is_reachableb_correct; exists w; intuition.
  }
  generalize dependent (length (states g)); intro n;
  induction (start_states g) as [|q0 s IH].
  simpl; right; intros [q0 [[] _]].
  destruct IH as [H|H].
  left; destruct H as [q1 [H H0]]; exists q1; intuition.
  destruct (is_reachableb g q0 q n) eqn:H0.
  left; exists q0; intuition.
  right; intros [q1 [H1 H2]].
  apply H; clear H.
  destruct H1.
  subst; rewrite H0 in H2; discriminate.
  exists q1; intuition.
Defined.

(* Remove the unreachable states of a NFA *)
Fixpoint remove_unreachable_states' (g cp:NFA) :=
  match g with
  | state q::g => (
    if reachable_state_dec cp q then [state q] else []
  ) ++ remove_unreachable_states' g cp
  | start q::g => (
    if reachable_state_dec cp q then [start q] else []
  ) ++ remove_unreachable_states' g cp
  | accept q::g => (
    if reachable_state_dec cp q then [accept q] else []
  ) ++ remove_unreachable_states' g cp
  | transition q1 a q2::g => (
    if reachable_state_dec cp q1 then [transition q1 a q2] else []
  ) ++ remove_unreachable_states' g cp
  | x::g => x::remove_unreachable_states' g cp
  | nil => nil
  end.

Definition remove_unreachable_states g := remove_unreachable_states' g g.

(* The resulting states are in the original NFA *)
Lemma remove_unreachable_states'_states g cp q :
  In q (states (remove_unreachable_states' g cp)) ->
  In q (states g).
Proof.
  intro H.
  induction g as [|c g IH].
  contradiction.
  destruct c.
  2: intuition.
  - simpl in H; apply in_states_app in H.
    destruct H.
    destruct (reachable_state_dec cp q0).
    destruct H.
    2,3: contradiction.
    simpl; left; intuition.
    right; apply IH, H.
  (* same code from above: *)
  - simpl in H; apply in_states_app in H.
    destruct H.
    destruct (reachable_state_dec cp q0).
    destruct H.
    2,3: contradiction.
    simpl; left; intuition.
    right; apply IH, H.
  (* same code from above: *)
  - simpl in H; apply in_states_app in H.
    destruct H.
    destruct (reachable_state_dec cp q0).
    destruct H.
    2,3: contradiction.
    simpl; left; intuition.
    right; apply IH, H.
  - simpl in H; apply in_states_app in H.
    destruct H.
    destruct (reachable_state_dec cp q1).
    simpl in H; destruct H.
    2: destruct H.
    left; intuition.
    right; left; intuition.
    1,2: contradiction.
    right; right; intuition.
Qed.

Lemma remove_unreachable_states_states g q :
  In q (states (remove_unreachable_states g)) ->
  In q (states g).
Proof.
  apply remove_unreachable_states'_states.
Qed.

(*
  All states in remove_unreachable_states' g cp are reachable
  in the original NFA if g is subset of cp
*)
Lemma remove_unreachable_states'_reachable_state g cp q :
  (subset NFA_comp g cp) ->
  In q (states (remove_unreachable_states' g cp)) ->
  reachable_state cp q.
Proof.
  intros H H0.
  induction g as [|c g IH].
  contradiction.
  destruct c.
  5: {
    simpl in H, H0; apply in_states_app in H0.
    destruct H0. {
      destruct (reachable_state_dec cp q1) as [H1|H1].
      2: contradiction.
      simpl in H0; destruct H0.
      subst; intuition.
      destruct H0; subst.
      2: contradiction.
      destruct H1 as [w H1].
      exists (w ++ [a]); rewrite ext_transitionf_app.
      assert (In q (transitionf cp [q1] a)).
      2: apply ext_transitionf_generalize with q1; intuition.
      apply transition_transitionf, H; intuition.
    }
    apply IH.
    2: intuition.
    intros c H1.
    apply H; intuition.
  }
  2: apply IH; try (intros c H2; apply H); intuition.
  - simpl in H0; destruct (reachable_state_dec cp q0).
    destruct H0.
    subst; intuition.
    1,2: apply IH; try (intros c H2; apply H); intuition.
  (* same code from above: *)
  - simpl in H0; destruct (reachable_state_dec cp q0).
    destruct H0.
    subst; intuition.
    1,2: apply IH; try (intros c H2; apply H); intuition.
  (* same code from above: *)
  - simpl in H0; destruct (reachable_state_dec cp q0).
    destruct H0.
    subst; intuition.
    1,2: apply IH; try (intros c H2; apply H); intuition.
Qed.

(* The resulting start states are the same *)
Lemma remove_unreachable_states'_start_states g cp :
  (subset NFA_comp g cp) ->
  start_states (remove_unreachable_states' g cp) = start_states g.
Proof.
  intro H.
  induction g as [|c g IH].
  intuition.
  destruct c.
  1,4: simpl; destruct (reachable_state_dec cp q);
  simpl; apply IH; intros c H2; apply H; intuition.
  simpl; apply IH; intros c H2; apply H; intuition.
  2: simpl; destruct (reachable_state_dec cp q1);
  simpl; apply IH; intros c H2; apply H; intuition.
  simpl.
  assert (reachable_state cp q).
  2: {
    destruct (reachable_state_dec cp q).
    simpl; rewrite IH.
    intuition.
    intros c H2; apply H; intuition.
    contradiction.
  }
  exists nil; simpl; apply in_start_states.
  apply H; intuition.
Qed.

Lemma remove_unreachable_states_start_states g :
  start_states (remove_unreachable_states g) = start_states g.
Proof.
  apply remove_unreachable_states'_start_states, subset_self.
Qed.

(* The resulting accept states are in the original NFA *)
Lemma remove_unreachable_states'_accept_states g cp q :
  In q (accept_states (remove_unreachable_states' g cp)) ->
  In q (accept_states g).
Proof.
  intro H.
  induction g as [|c g IH].
  contradiction.
  destruct c.
  1-3: apply IH, in_accept_states; intuition;
  simpl in H; apply in_accept_states in H; intuition;
  destruct (reachable_state_dec cp q0); intuition;
  destruct H; try discriminate; intuition.
  2: apply IH, in_accept_states; intuition;
  simpl in H; apply in_accept_states in H; intuition;
  destruct (reachable_state_dec cp q1); intuition;
  destruct H; try discriminate; intuition.
  simpl in H; destruct (reachable_state_dec cp q0).
  destruct H.
  subst; left.
  2,3: right.
  1-3: intuition.
Qed.

Lemma remove_unreachable_states_accept_states g q :
  In q (accept_states (remove_unreachable_states g)) ->
  In q (accept_states g).
Proof.
  apply remove_unreachable_states'_accept_states.
Qed.

(*
  If an original accept state is in the resulting NFA,
  then it is a resulting accept state.
*)
Lemma remove_unreachable_states'_has_accept_state g cp q :
  (subset NFA_comp g cp) ->
  In q (states (remove_unreachable_states' g cp)) ->
  In q (accept_states g) ->
  In q (accept_states (remove_unreachable_states' g cp)).
Proof.
  intros H10 H H0.
  apply remove_unreachable_states'_reachable_state in H.
  2: intuition.
  clear H10.
  induction g as [|c g IH].
  contradiction.
  destruct c.
  2: destruct H; try discriminate; intuition.
  1-2,4: destruct H; try discriminate; simpl;
  destruct (reachable_state_dec cp q);
  apply in_accept_states_app; intuition.
  simpl; simpl in H0; destruct H0.
  subst; destruct (reachable_state_dec cp q).
  left; intuition.
  contradiction.
  apply in_accept_states_app; intuition.
Qed.

Lemma remove_unreachable_states_has_accept_state g q :
  In q (states (remove_unreachable_states g)) ->
  In q (accept_states g) ->
  In q (accept_states (remove_unreachable_states g)).
Proof.
  apply remove_unreachable_states'_has_accept_state, subset_self.
Qed.

(* The resulting transitions are in the original NFA *)
Lemma remove_unreachable_states'_transitions1 g cp q1 a q2 :
  In (transition q1 a q2) (remove_unreachable_states' g cp) ->
  In (transition q1 a q2) g.
Proof.
  intro H.
  induction g as [|c g IH].
  contradiction.
  destruct c.
  1,3,4: simpl in H; destruct (reachable_state_dec cp q); intuition;
  destruct H; try discriminate; intuition.
  right; destruct H; try discriminate; intuition.
  simpl in H; destruct (reachable_state_dec cp q0).
  destruct H.
  2,3: right; intuition.
  injection H; intros; subst;
  left; intuition.
Qed.

Lemma remove_unreachable_states_transitions1 g q1 a q2 :
  In (transition q1 a q2) (remove_unreachable_states g) ->
  In (transition q1 a q2) g.
Proof.
  apply remove_unreachable_states'_transitions1.
Qed.

(*
  If a transition from a resulting state exists in the original NFA,
  then the transition is maintained.
*)
Lemma remove_unreachable_states'_transitions2 g cp q1 a q2 :
  (subset NFA_comp g cp) ->
  In q1 (states (remove_unreachable_states' g cp)) ->
  In (transition q1 a q2) g ->
  In (transition q1 a q2) (remove_unreachable_states' g cp).
Proof.
  intros H10 H H0.
  assert (reachable_state cp q1).
  2: {
    clear H H10.
    induction g as [|c g IH].
    contradiction.
    destruct c.
    2: destruct H0; try discriminate; right; intuition.
    1-3: destruct H0; try discriminate; simpl;
    destruct (reachable_state_dec cp q); try right;
    intuition.
    simpl in H0; simpl; destruct H0;
    destruct (reachable_state_dec cp q0).
    1,2: injection H; intros; subst.
    2: contradiction.
    left; intuition.
    apply in_or_app; right.
    1,2: intuition.
  }
  apply remove_unreachable_states'_reachable_state with g;
  intuition.
Qed.

Lemma remove_unreachable_states_transitions2 g q1 a q2 :
  In q1 (states (remove_unreachable_states g)) ->
  In (transition q1 a q2) g ->
  In (transition q1 a q2) (remove_unreachable_states g).
Proof.
  apply remove_unreachable_states'_transitions2, subset_self.
Qed.

(* Algorithm is correct: all resulting states are reachable *)
Lemma remove_unreachable_correct g q :
  In q (states (remove_unreachable_states g)) ->
  reachable_state (remove_unreachable_states g) q.
Proof.
  intros H.
  apply remove_unreachable_states'_reachable_state in H.
  2: apply subset_self.
  destruct H as [w H].
  apply ext_transitionf_singleton in H.
  destruct H as [q0 [H H0]].
  apply path_ext_transitionf in H0.
  assert (path (remove_unreachable_states g) q0 q w).
  2: {
    exists w; apply ext_transitionf_generalize with q0.
    rewrite remove_unreachable_states_start_states; intuition.
    apply path_ext_transitionf; intuition.
  }
  generalize dependent q;
  induction w as [|a w IH] using rev_ind;
  intros q H0.
  inversion H0; subst; constructor.
  apply path_trans_inv2 in H0.
  destruct H0 as [q' [H0 H1]].
  pose proof H0 as H10.
  apply IH in H0; clear IH.
  apply path_trans_inv1 with q'.
  intuition.
  apply remove_unreachable_states'_transitions2.
  apply subset_self.
  2: intuition.
  assert (reachable_state g q'). {
    exists w; apply ext_transitionf_generalize with q0.
    2: apply path_ext_transitionf.
    1,2: intuition.
  }
  clear H10 H0 H w q0.
  assert (forall cp, reachable_state cp q' -> In q' (states (remove_unreachable_states' g cp))). {
    clear H2.
    intros cp H.
    induction g as [|c g IH].
    contradiction.
    destruct c.
    - destruct H1.
      discriminate.
      simpl; apply in_states_app.
      right; intuition.
    - destruct H1.
      discriminate.
      intuition.
    - destruct H1.
      discriminate.
      simpl; apply in_states_app.
      right; intuition.
    - destruct H1.
      discriminate.
      simpl; apply in_states_app.
      right; intuition.
    - destruct H1.
      2: {
        simpl; apply in_states_app.
        right; intuition.
      }
      injection H0; intros; subst; simpl.
      destruct (reachable_state_dec cp q').
      left; intuition.
      contradiction.
  }
  apply H; intuition.
Qed.

End Pumping.