Require Export ListSets.

Section NFA.

Context {State Symbol : Type}.
Definition Word := ListSet Symbol.

Hypothesis State_eq_dec : forall (x1 x2:State), { x1 = x2 } + { x1 <> x2 }.
Hypothesis Symbol_eq_dec : forall (x1 x2:Symbol), { x1 = x2 } + { x1 <> x2 }.

Inductive NFA_comp :=
  | state (q:State)
  | symbol (a:Symbol)
  | start (q:State)
  | accept (q:State)
  | transition (q1:State) (a:Symbol) (q2:State).

Definition NFA := ListSet NFA_comp.

Fixpoint states (g:NFA) :=
  match g with
  | state q::g => q::states g
  | start q::g => q::states g
  | accept q::g => q::states g
  | transition q1 a q2::g => q1::q2::states g
  | _::g => states g
  | nil => nil
  end.

Fixpoint alphabet (g:NFA) :=
  match g with
  | symbol a::g => a::alphabet g
  | transition q1 a q2::g => a::alphabet g
  | _::g => alphabet g
  | nil => nil
  end.

Fixpoint start_states (g:NFA) :=
  match g with
  | start q::g => q::start_states g
  | _::g => start_states g
  | nil => nil
  end.

Fixpoint accept_states (g:NFA) :=
  match g with
  | accept q::g => q::accept_states g
  | _::g => accept_states g
  | nil => nil
  end.

(* Transition function *)
Fixpoint transitionf (g:NFA) s a :=
  match g with
  | transition q1 b q2::g =>
    (if In_dec State_eq_dec q1 s then
      (if Symbol_eq_dec b a then [q2] else nil)
    else nil) ++ transitionf g s a
  | _::g => transitionf g s a
  | nil => nil
  end.

(* Extended transition function *)
Fixpoint ext_transitionf (g:NFA) s w :=
  match w with
  | a::w => ext_transitionf g (transitionf g s a) w
  | nil => s
  end.

(* In states decomposition *)
Lemma in_states q g :
  In q (states g) <->
  In (state q) g \/
  In (start q) g \/
  In (accept q) g \/
  (exists a q', In (transition q a q') g) \/
  (exists a q', In (transition q' a q) g).
Proof.
  induction g as [|c g IH]. {
    split; intro.
    contradiction.
    destruct H.
    2: destruct H.
    3: destruct H.
    4: destruct H.
    4,5: destruct H as [a [q' H]].
    1-5: contradiction.
  }
  destruct c; simpl.
  2: {
    split; intro H.
    - apply IH in H.
      destruct H.
      2: destruct H.
      3: destruct H.
      1-3: intuition.
      destruct H as [[b [q' H]]|[b [q' H]]].
      right; right; right; left; exists b, q'; intuition.
      repeat right; exists b, q'; intuition.
    - apply IH.
      destruct H as [[H|H]|H]; try discriminate.
      intuition.
      destruct H as [[H|H]|H]; try discriminate.
      intuition.
      destruct H as [[H|H]|H]; try discriminate.
      intuition.
      destruct H as [[b [q' [H|H]]]|H]; try discriminate.
      right; right; right; left; exists b, q'; intuition.
      destruct H as [b [q' [H|H]]]; try discriminate.
      repeat right; exists b, q'; intuition.
  }
  - split; intro H.
    + destruct H.
      subst; intuition.
      apply IH in H.
      destruct H.
      2: destruct H.
      3: destruct H.
      1-3: intuition.
      destruct H as [[b [q' H]]|[b [q' H]]].
      right; right; right; left; exists b, q'; intuition.
      right; right; right; right; exists b, q'; intuition.
    + destruct H.
      destruct H.
      injection H; intros; subst; intuition.
      right; apply IH; intuition.
      destruct H.
      destruct H; try discriminate.
      right; apply IH; intuition.
      destruct H.
      destruct H; try discriminate.
      right; apply IH; intuition.
      destruct H as [[b [q' [H|H]]]|[b [q' [H|H]]]]; try discriminate.
      1,2: right; apply IH.
      right; right; right; left; exists b, q'; intuition.
      repeat right; exists b, q'; intuition.
  - split; intro H.
    + destruct H.
      subst; intuition.
      apply IH in H.
      destruct H.
      2: destruct H.
      3: destruct H.
      1-3: intuition.
      destruct H as [[a [q' H]]|[a [q' H]]].
      right; right; right; left; exists a, q'; intuition.
      right; right; right; right; exists a, q'; intuition.
    + destruct H.
      destruct H; try discriminate.
      right; apply IH; intuition.
      destruct H.
      destruct H.
      injection H; intros; subst; intuition.
      right; apply IH; intuition.
      destruct H.
      destruct H; try discriminate.
      right; apply IH; intuition.
      destruct H as [[a [q' [H|H]]]|[a [q' [H|H]]]]; try discriminate.
      1,2: right; apply IH.
      right; right; right; left; exists a, q'; intuition.
      repeat right; exists a, q'; intuition.
  - split; intro H.
    + destruct H.
      subst; intuition.
      apply IH in H.
      destruct H.
      2: destruct H.
      3: destruct H.
      1-3: intuition.
      destruct H as [[a [q' H]]|[a [q' H]]].
      right; right; right; left; exists a, q'; intuition.
      right; right; right; right; exists a, q'; intuition.
    + destruct H.
      destruct H; try discriminate.
      right; apply IH; intuition.
      destruct H.
      destruct H; try discriminate.
      right; apply IH; intuition.
      destruct H.
      destruct H.
      injection H; intros; subst; intuition.
      right; apply IH; intuition.
      destruct H as [[a [q' [H|H]]]|[a [q' [H|H]]]]; try discriminate.
      1,2: right; apply IH.
      right; right; right; left; exists a, q'; intuition.
      repeat right; exists a, q'; intuition.
  - split; intro H.
    + destruct H.
      subst; right; right; right; left; exists a, q2; intuition.
      destruct H.
      subst; repeat right; exists a, q1; intuition.
      apply IH in H.
      destruct H.
      2: destruct H.
      3: destruct H.
      1-3: intuition.
      destruct H as [[b [q' H]]|[b [q' H]]].
      right; right; right; left; exists b, q'; intuition.
      right; right; right; right; exists b, q'; intuition.
    + destruct H.
      destruct H; try discriminate.
      repeat right; apply IH; intuition.
      destruct H.
      destruct H; try discriminate.
      repeat right; apply IH; intuition.
      destruct H.
      destruct H; try discriminate.
      repeat right; apply IH; intuition.
      destruct H as [[b [q' [H|H]]]|[b [q' [H|H]]]].
      injection H; intros; subst; intuition.
      2: injection H; intros; subst; intuition.
      1,2: repeat right; apply IH.
      right; right; right; left; exists b, q'; intuition.
      repeat right; exists b, q'; intuition.
Qed.

(* In start_states decomposition *)
Lemma in_start_states q g :
  In q (start_states g) <-> In (start q) g.
Proof.
  induction g as [|c g IH].
  intuition.
  simpl; destruct c.
  3: {
    split; intro H.
    destruct H; subst; intuition.
    destruct H.
    injection H; intros; subst.
    1,2: intuition.
  }
  - split; intro H.
    right.
    2: destruct H; try discriminate.
    1,2: intuition.
  (* same code from above: *)
  - split; intro H.
    right.
    2: destruct H; try discriminate.
    1,2: intuition.
  (* same code from above: *)
  - split; intro H.
    right.
    2: destruct H; try discriminate.
    1,2: intuition.
  (* same code from above: *)
  - split; intro H.
    right.
    2: destruct H; try discriminate.
    1,2: intuition.
Qed.

(* In accept_states decomposition *)
Lemma in_accept_states q g :
  In q (accept_states g) <-> In (accept q) g.
Proof.
  (* same proof from in_start_states: *)
  induction g as [|c g IH].
  intuition.
  simpl; destruct c.
  4: {
    split; intro H.
    destruct H; subst; intuition.
    destruct H.
    injection H; intros; subst.
    1,2: intuition.
  }
  - split; intro H.
    right.
    2: destruct H; try discriminate.
    1,2: intuition.
  (* same code from above: *)
  - split; intro H.
    right.
    2: destruct H; try discriminate.
    1,2: intuition.
  (* same code from above: *)
  - split; intro H.
    right.
    2: destruct H; try discriminate.
    1,2: intuition.
  (* same code from above: *)
  - split; intro H.
    right.
    2: destruct H; try discriminate.
    1,2: intuition.
Qed.

(* A state in the concatenation of two NFAs is in at least one of them *)
Lemma in_states_app g1 g2 q :
  In q (states (g1 ++ g2)) <->
  In q (states g1) \/ In q (states g2).
Proof.
  induction g1 as [|c g1 IH].
  simpl; intuition.
  destruct c; simpl.
  2: trivial.
  - split; intro H.
    destruct H; subst; intuition.
    apply or_assoc in H; destruct H; subst; intuition.
  (* same code from above: *)
  - split; intro H.
    destruct H; subst; intuition.
    apply or_assoc in H; destruct H; subst; intuition.
  (* same code from above: *)
  - split; intro H.
    destruct H; subst; intuition.
    apply or_assoc in H; destruct H; subst; intuition.
  - split; intro H.
    destruct H.
    2: destruct H.
    1-3: subst; intuition.
    apply or_assoc in H; destruct H.
    2: apply or_assoc in H; destruct H.
    1,2: subst; intuition.
    intuition.
Qed.

(* An accept state in the concatenation of two NFAs is in at least one of them *)
Lemma in_accept_states_app g1 g2 q :
  In q (accept_states (g1 ++ g2)) <->
  In q (accept_states g1) \/ In q (accept_states g2).
Proof.
  induction g1 as [|c g1 IH].
  simpl; intuition.
  destruct c; simpl.
  1-3,5: trivial.
  split; intro H.
  destruct H; subst; intuition.
  apply or_assoc in H; destruct H; subst; intuition.
Qed.

(* A start state is a state *)
Lemma start_state g q :
  In q (start_states g) -> In q (states g).
Proof.
  intro H.
  induction g as [|c g IH].
  contradiction.
  destruct c.
  1,2,4,5: apply IH in H; try right; intuition.
  destruct H.
  - subst.
    simpl; intuition.
  - right; intuition.
Qed.

(* The start states of the concatenation of two NFAs is the their start states concatenated *)
Lemma start_states_app g1 g2 :
  start_states (g1 ++ g2) = start_states g1 ++ start_states g2.
Proof.
  induction g1 as [|c g1 IH].
  intuition.
  simpl; destruct c;
  simpl; rewrite IH; intuition.
Qed.

(* Transition function decomposition *)
Lemma transition_transitionf g q1 a q2 :
  In (transition q1 a q2) g <-> In q2 (transitionf g [q1] a).
Proof.
  induction g as [|c g IH].
  intuition.
  destruct c; simpl.
  1-4: split; intro H; try destruct H as [H|H]; try discriminate; intuition.
  destruct (State_eq_dec q1 q0) as [H|H].
  - subst; destruct (Symbol_eq_dec a0 a) as [H|H].
    + subst; split; intro H.
      * destruct H.
        inversion H; subst.
        1,2: intuition.
      * destruct H; subst; intuition.
    + split; intro H0.
      * destruct H0.
        inversion H0; subst.
        1,2: intuition.
      * intuition.
  - split; intro H0.
    + destruct H0.
      inversion H0; subst.
      1,2: intuition.
    + intuition.
Qed.

(*
  The transition function applied to two sets concatenated returns a state returned
  by the transition function applied to one of the sets
*)
Lemma in_transitionf_app g q s1 s2 a :
  In q (transitionf g (s1 ++ s2) a) -> In q (transitionf g s1 a) \/ In q (transitionf g s2 a).
Proof.
  intro H.
  induction g as [|c g IH].
  contradiction.
  destruct c.
  1-4: apply IH in H; destruct H; intuition.
  simpl; simpl in H;
  destruct (in_dec State_eq_dec q1 (s1 ++ s2)) as [H0|H0]; destruct (Symbol_eq_dec a0 a) as [H1|H1];
  subst.
  apply in_app_or in H; destruct H. {
    apply in_singleton in H; subst.
    apply in_app_or in H0; destruct H0.
    - destruct (in_dec State_eq_dec q1 s1).
      intuition.
      contradiction.
    - destruct (in_dec State_eq_dec q1 s2).
      intuition.
      contradiction.
  }
  1-4: apply IH in H; destruct H.
  1,3,5,7: left; apply in_or_app; intuition.
  1-4: right; apply in_or_app; intuition.
Qed.

(*
  The transition function applied to a set returns a state returned
  by the transition function applied to a single state in the set
*)
Lemma transitionf_singleton g s q2 a :
  In q2 (transitionf g s a) -> exists q1,
  In q1 s /\ In q2 (transitionf g [q1] a).
Proof.
  intro H.
  induction g as [|c g IH].
  contradiction.
  destruct c.
  1-4: apply IH in H; destruct H as [q1 H]; exists q1; intuition.
  simpl in H; destruct (in_dec State_eq_dec q1 s).
  destruct (Symbol_eq_dec a0 a).
  destruct H.
  2-4: apply IH in H; destruct H as [q3 H]; exists q3; split; simpl; try (apply in_or_app); intuition.
  subst.
  exists q1; split.
  2: simpl; destruct (State_eq_dec q1 q1).
  2: destruct (Symbol_eq_dec a a).
  1-4: intuition.
Qed.

(* The reciprocal *)
Lemma transitionf_generalize g s q1 q2 a :
  In q1 s -> In q2 (transitionf g [q1] a) ->
  In q2 (transitionf g s a).
Proof.
  intros H H0.
  induction g as [|c g IH].
  contradiction.
  destruct c.
  1-4: intuition.
  simpl; simpl in H0.
  destruct (State_eq_dec q1 q0).
  destruct (Symbol_eq_dec a0 a).
  destruct H0.
  2-4: apply in_or_app; intuition.
  subst.
  destruct (in_dec State_eq_dec q0 s).
  intuition.
  contradiction.
Qed.

(*
  Given two equivalent states, the transition function applied to them
  returns equivalent sets
*)
Lemma transitionf_equiv g s1 s2 a :
  equiv_sets State s1 s2 ->
  equiv_sets State (transitionf g s1 a) (transitionf g s2 a).
Proof.
  intro H; induction g as [|c g IH].
  apply equiv_sets_self.
  destruct c.
  1-4: intuition.
  simpl.
  destruct (in_dec State_eq_dec q1 s1) as [H0|H0];
  destruct (in_dec State_eq_dec q1 s2) as [H1|H1].
  4: intuition.
  2: apply H in H0.
  3: apply H in H1.
  2,3: contradiction.
  destruct (Symbol_eq_dec a0 a) as [H2|H2].
  2: intuition.
  simpl; split; intros q [H3|H3]; subst.
  1,3: intuition.
  1,2: right; apply IH; intuition.
Qed.

(* A set cannot be nil if the transition function applied to it returns something *)
Lemma ext_transitionf_not_nil g s w q :
  In q (ext_transitionf g s w) ->
  exists q', In q' s.
Proof.
  revert s.
  induction w as [|a w IH];
  intros s H.
  exists q; intuition.
  simpl in H; apply IH in H.
  destruct H as [q0 H].
  clear IH.
  induction g as [|c g IH].
  contradiction.
  destruct c.
  5: simpl in H; apply in_app_or in H; destruct H.
  1-4,6: intuition.
  destruct (in_dec State_eq_dec q1 s).
  destruct (Symbol_eq_dec a0 a).
  2,3: contradiction.
  exists q1; intuition.
Qed.

(* Rewrite rule on the extended transition function for concatenation of words *)
Lemma ext_transitionf_app g s w1 w2 :
  ext_transitionf g s (w1 ++ w2) = ext_transitionf g (ext_transitionf g s w1) w2.
Proof.
  revert s;
  induction w1 as [|a1 w1 IH];
  intro s.
  intuition.
  apply IH.
Qed.

(*
  The extended transition function applied to two sets concatenated returns a state returned
  by the transition function applied to one of the sets
*)
Lemma in_ext_transitionf_app g q s1 s2 w :
  In q (ext_transitionf g (s1 ++ s2) w) <-> In q (ext_transitionf g s1 w) \/ In q (ext_transitionf g s2 w).
Proof.
  generalize dependent q;
  induction w as [|a w IH] using rev_ind;
  intro q.
  simpl; split; intro H.
  apply in_app_or.
  2: apply in_or_app.
  1,2: intuition.
  split; intro H.
  - repeat rewrite ext_transitionf_app; rewrite ext_transitionf_app in H; simpl; simpl in H.
    apply transitionf_singleton in H.
    destruct H as [q1 [H H0]].
    apply IH in H.
    destruct H.
    left.
    2: right.
    1,2: apply transitionf_generalize with q1; intuition.
  - rewrite ext_transitionf_app; repeat rewrite ext_transitionf_app in H; simpl; simpl in H.
    destruct H.
    + apply transitionf_singleton in H.
      destruct H as [q1 [H H0]].
      assert (In q1 (ext_transitionf g s1 w) \/ In q1 (ext_transitionf g s2 w)).
      2: apply IH in H1.
      2: apply transitionf_generalize with q1.
      1-3: intuition.
    (* same code from above: *)
    + apply transitionf_singleton in H.
      destruct H as [q1 [H H0]].
      assert (In q1 (ext_transitionf g s1 w) \/ In q1 (ext_transitionf g s2 w)).
      2: apply IH in H1.
      2: apply transitionf_generalize with q1.
      1-3: intuition.
Qed.

(*
  The extended transition function applied to a single state can be generalized
  for a set of states
*)
Lemma ext_transitionf_generalize g s q1 q2 w :
  In q1 s -> In q2 (ext_transitionf g [q1] w) ->
  In q2 (ext_transitionf g s w).
Proof.
  intros H H0.
  apply in_split in H.
  destruct H as [s1 [s2 H]]; subst.
  apply in_ext_transitionf_app; right.
  replace (q1 :: s2) with ([q1] ++ s2).
  apply in_ext_transitionf_app.
  1,2: intuition.
Qed.

(* The reciprocal *)
Lemma ext_transitionf_singleton g s q2 w :
  In q2 (ext_transitionf g s w) -> exists q1,
  In q1 s /\ In q2 (ext_transitionf g [q1] w).
Proof.
  generalize dependent s;
  induction w as [|a w IH];
  intros s H; simpl in H.
  exists q2; simpl; intuition.
  apply IH in H; destruct H as [q1 [H H0]]; clear IH.
  assert (exists q0, In q0 s /\ In q1 (transitionf g [q0] a)). {
    apply transitionf_singleton; intuition.
  }
  destruct H1 as [q0 [H1 H2]].
  exists q0; split.
  intuition.
  simpl; apply ext_transitionf_generalize with q1; intuition.
Qed.

(* Transition decomposition into states and alphabet *)
Lemma transition_states_alphabet g q1 a q2 :
  In (transition q1 a q2) g ->
  In q1 (states g) /\ In a (alphabet g) /\ In q2 (states g).
Proof.
  intro H.
  induction g as [|c g IH].
  contradiction.
  destruct c.
  1-4: destruct H; try discriminate; apply IH in H; repeat split; try right; intuition.
  destruct H.
  - injection H; intros; subst; repeat split.
    1,2: left.
    3: right; left.
    1-3: intuition.
  - apply IH in H; repeat split; try right; intuition.
Qed.

(* The transition function returns states *)
Lemma transitionf_all_states g s a q :
  In q (transitionf g s a) ->
  In q (states g).
Proof.
  intro H.
  induction g as [|c g IH].
  contradiction.
  destruct c.
  1-4: try right; intuition.
  simpl in H.
  apply in_app_or in H; destruct H.
  destruct (in_dec State_eq_dec q1 s).
  destruct (Symbol_eq_dec a0 a).
  2,3: contradiction.
  apply in_singleton in H.
  subst; right; left.
  2: right; right.
  1,2: intuition.
Qed.

(* The extended transition function returns states *)
Lemma ext_transitionf_all_states g s w q :
  subset State s (states g) ->
  In q (ext_transitionf g s w) ->
  In q (states g).
Proof.
  revert s; induction w as [|a w IH]; intros s H0 H1.
  apply H0; intuition.
  simpl in H1.
  apply IH with (transitionf g s a).
  2: intuition.
  clear IH H1 w.
  induction s as [|q1 s IH]; intros q2 H. {
    clear H0; induction g as [|c g IH].
    contradiction.
    destruct c;
    try right; try right; intuition.
  }
  replace (q1::s) with ([q1] ++ s) in H.
  apply in_transitionf_app in H.
  destruct H; apply transitionf_all_states in H.
  1-3: intuition.
Qed.

Lemma ext_transitionf_singleton_all_states g q1 w q2 :
  In q1 (states g) -> In q2 (ext_transitionf g [q1] w) ->
  In q2 (states g).
Proof.
  intros H H0; apply (ext_transitionf_all_states g [q1] w q2).
  intros q [H1|H1].
  1,3: subst; intuition.
  contradiction.
Qed.

Definition has_state (s1 s2:ListSet State) := has_el State s1 s2.

Definition has_accept_state (g:NFA) s := has_state s (accept_states g).

(* hast_accept_state decider *)
Lemma has_accept_state_dec (g:NFA) :
  forall s, {has_accept_state g s} + {~ has_accept_state g s}.
Proof.
  intro s; induction s as [|q s IH].
  right; intros [q [H _]]; contradiction.
  destruct IH as [H|H].
  left; destruct H as [qf H]; exists qf; intuition.
  destruct (in_dec State_eq_dec q (accept_states g)) as [H0|H0].
  left; exists q; intuition.
  right; intros [qf [[H1|H1] H2]].
  subst; contradiction.
  apply H; exists qf; intuition.
Defined.

(* Equivalent states *)
Definition equiv_states (g:NFA) (q1 q2:State) :=
  forall w, has_accept_state g (ext_transitionf g [q1] w) <-> has_accept_state g (ext_transitionf g [q2] w).

(* Word acceptance *)
Definition nfa_accepts (g:NFA) w :=
  has_accept_state g (ext_transitionf g (start_states g) w).

Definition reachable_state (g:NFA) q :=
  exists w, In q (ext_transitionf g (start_states g) w).

Inductive path (g:NFA) : State -> State -> Word -> Prop :=
  | path_nil q : path g q q nil
  | path_trans q1 q2 q3 a w : In (transition q1 a q2) g -> path g q2 q3 w ->
    path g q1 q3 (a::w).

(* Every transition is a path *)
Lemma path_ext_transitionf g q1 q2 w :
  path g q1 q2 w <-> In q2 (ext_transitionf g [q1] w).
Proof.
  split; intro H.
  - induction H; simpl.
    intuition.
    apply transition_transitionf in H.
    apply ext_transitionf_generalize with (s:=transitionf g [q1] a) in IHpath.
    1,2: intuition.
  - generalize dependent q1; induction w as [|a w IH]; intros q1 H.
    destruct H.
    subst; constructor.
    contradiction.
    simpl in H; apply ext_transitionf_singleton in H; destruct H as [q3 [H H0]].
    apply IH in H0.
    apply transition_transitionf in H.
    apply path_trans with q3; intuition.
Qed.

(* A inverted transitive property *)
Lemma path_trans_inv1 g q1 q2 q3 w a :
  path g q1 q2 w -> In (transition q2 a q3) g ->
  path g q1 q3 (w ++ [a]).
Proof.
  intros H H0.
  induction H.
  apply path_trans with (q2:=q3).
  2: constructor.
  2: simpl; apply path_trans with q2.
  1-3: intuition.
Qed.

(* The reciprocal *)
Lemma path_trans_inv2 g q1 q3 w a :
  path g q1 q3 (w ++ [a]) -> exists q2,
  path g q1 q2 w /\ In (transition q2 a q3) g.
Proof.
  intro H.
  generalize dependent q1;
  induction w as [|b w IH];
  intros q1 H.
  inversion H; subst.
  inversion H5; subst.
  exists q1; split.
  constructor.
  intuition.
  simpl in H; inversion H; subst.
  apply IH in H5; destruct H5 as [q4 [H5 H6]].
  exists q4; split.
  apply path_trans with q2.
  1-3: intuition.
Qed.

(* Remove duplicate states *)
Definition states_nodup g := nodup State_eq_dec (states g).

(* Remove duplicate symbols in the alphabet *)
Definition alphabet_nodup g := nodup Symbol_eq_dec (alphabet g).

Fixpoint remove_state (g:NFA) s :=
  match g with
  | state q::g => (
      if State_eq_dec q s then [] else [state q]
    ) ++ remove_state g s
  | start q::g => (
      if State_eq_dec q s then [] else [start q]
    ) ++ remove_state g s
  | accept q::g => (
      if State_eq_dec q s then [] else [accept q]
    ) ++ remove_state g s
  | transition q1 a q2::g => (
      if State_eq_dec q1 s then [] else (
        if State_eq_dec q2 s then [] else [transition q1 a q2]
      )
    ) ++ remove_state g s
  | _::g => remove_state g s
  | nil => nil
  end.

(* remove_state is commutative *)
Lemma remove_state_comm g q1 q2 :
  remove_state (remove_state g q1) q2 = remove_state (remove_state g q2) q1.
Proof.
  revert q1 q2 g; intros q q1 g0.
  induction g0.
  auto.
  destruct a; simpl.
  2: auto.
  1-3: destruct (State_eq_dec q0 q); destruct (State_eq_dec q0 q1); simpl;
  destruct (State_eq_dec q0 q); destruct (State_eq_dec q0 q1); simpl;
  try contradiction; rewrite IHg0; intuition.
  destruct (State_eq_dec q0 q); destruct (State_eq_dec q0 q1); destruct (State_eq_dec q0 q2); simpl;
  destruct (State_eq_dec q0 q); destruct (State_eq_dec q0 q1); destruct (State_eq_dec q0 q2); simpl;
  try contradiction.
  1,2: auto.
  1,2: destruct (State_eq_dec q2 q1); simpl; destruct (State_eq_dec q0 q); simpl; try contradiction; rewrite IHg0; intuition.
  1,2: destruct (State_eq_dec q2 q); simpl; destruct (State_eq_dec q0 q); simpl;
  destruct (State_eq_dec q0 q); simpl; destruct (State_eq_dec q0 q1); simpl;
  destruct (State_eq_dec q2 q1); simpl;
  try contradiction; rewrite IHg0; intuition.
  1,2: destruct (State_eq_dec q2 q); destruct (State_eq_dec q2 q1); simpl;
  destruct (State_eq_dec q0 q1); destruct (State_eq_dec q0 q); simpl;
  destruct (State_eq_dec q2 q1); destruct (State_eq_dec q2 q); simpl;
  try contradiction; rewrite IHg0; intuition.
Qed.

End NFA.