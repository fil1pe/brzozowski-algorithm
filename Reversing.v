Require Export NFA.

Section Reversing.

Context {State Symbol : Type}.
Definition Word := @Word Symbol.
Hypothesis State_eq_dec : forall (x1 x2:State), { x1 = x2 } + { x1 <> x2 }.
Hypothesis Symbol_eq_dec : forall (x1 x2:Symbol), { x1 = x2 } + { x1 <> x2 }.
Definition NFA := @NFA State Symbol.
Definition ext_transitionf := ext_transitionf State_eq_dec Symbol_eq_dec.
Definition nfa_accepts := nfa_accepts State_eq_dec Symbol_eq_dec.

(* Reverses word *)
Fixpoint rev (w:Word) :=
  match w with
  | a::w => rev w ++ [a]
  | nil => nil
  end.

(* Reverses NFA *)
Fixpoint rev_nfa (g:NFA) :=
  match g with
  | start q::g => accept q::rev_nfa g
  | accept q::g => start q::rev_nfa g
  | transition q1 a q2::g => transition q2 a q1::rev_nfa g
  | x::g => x::rev_nfa g
  | nil => nil
  end.

(* Distribution of word reversion *)
Lemma rev_distr w1 w2 :
  rev (w1 ++ w2) = rev w2 ++ rev w1.
Proof.
  induction w1 as [|a w1 IH].
  symmetry; apply app_nil_r.
  simpl.
  rewrite IH, app_assoc.
  intuition.
Qed.

(* A word reversed twice is equal to itself *)
Lemma rev_twice w :
  rev (rev w) = w.
Proof.
  induction w as [|a w IH].
  intuition.
  simpl.
  rewrite rev_distr, IH.
  intuition.
Qed.

(* The resulting states are the same *)
Lemma rev_states g q :
  In q (states (rev_nfa g)) -> In q (states g).
Proof.
  intro H.
  induction g as [|c g IH].
  contradiction.
  destruct c.
  1-4: try destruct H; subst.
  1,4,6: left; intuition.
  1-4: try right; intuition.
  destruct H as [H|[H|H]].
  1,3: right.
  1,3: subst; left; intuition.
  right; intuition.
Qed.

(* The resulting accept states are the original start states *)
Lemma rev_start_states g :
  accept_states (rev_nfa g) = start_states g.
Proof.
  induction g as [|c g IH].
  intuition.
  destruct c;
  simpl; rewrite IH; intuition.
Qed.

(* The resulting start states are the original accept states *)
Lemma rev_accept_states g :
  start_states (rev_nfa g) = accept_states g.
Proof.
  induction g as [|c g IH].
  intuition.
  destruct c;
  simpl; rewrite IH; intuition.
Qed.

(* The transitions go reversed *)
Lemma rev_transition g q1 a q2 :
  In (transition q1 a q2) g <->
  In (transition q2 a q1) (rev_nfa g).
Proof.
  induction g as [|c g IH].
  intuition.
  destruct c; simpl.
  1-4: split; intros [H|H]; try discriminate; intuition.
  split; intros [H|H].
  1,3: inversion H; subst; intuition.
  1,2: intuition.
Qed.

(* Same for paths *)
Lemma rev_path g q1 q2 w :
  path g q1 q2 w <-> path (rev_nfa g) q2 q1 (rev w).
Proof.
  split; intro H.
  - induction H.
    constructor.
    simpl.
    pose proof (path_trans_inv1 (rev_nfa g) q3 q2 q1 (rev w) a).
    apply H1.
    2: apply rev_transition in H.
    1,2: intuition.
  - rewrite <- rev_twice;
    remember (rev w) as w'; clear Heqw' w.
    induction H.
    constructor.
    simpl.
    pose proof (path_trans_inv1 g q3 q2 q1 (rev w) a).
    apply H1.
    2: apply rev_transition.
    1,2: intuition.
Qed.

(* And for the extended transition function *)
Lemma rev_ext_transitionf g q1 q2 w :
  In q1 (ext_transitionf g [q2] w) <->
  In q2 (ext_transitionf (rev_nfa g) [q1] (rev w)).
Proof.
  split; intro H.
  - apply path_ext_transitionf;
    apply path_ext_transitionf, rev_path in H;
    intuition.
  - apply path_ext_transitionf;
    apply path_ext_transitionf, rev_path in H;
    intuition.
Qed.

(* The reversed language *)
Lemma rev_language g w :
  nfa_accepts g w <-> nfa_accepts (rev_nfa g) (rev w).
Proof.
  unfold nfa_accepts, NFA.nfa_accepts, has_accept_state; split; intros [q [H H0]].
  - apply ext_transitionf_singleton in H; destruct H as [q0 [H H1]].
    apply path_ext_transitionf in H1.
    apply rev_path in H1.
    pose proof (path_ext_transitionf State_eq_dec Symbol_eq_dec (rev_nfa g) q q0 (rev w)) as H2.
    apply H2 in H1.
    exists q0; split.
    2: rewrite rev_start_states.
    apply ext_transitionf_generalize with q.
    rewrite rev_accept_states.
    1-3: intuition.
  - apply ext_transitionf_singleton in H; destruct H as [q0 [H H1]].
    apply path_ext_transitionf in H1.
    apply rev_path in H1.
    pose proof (path_ext_transitionf State_eq_dec Symbol_eq_dec g q q0 w) as H2.
    apply H2 in H1.
    exists q0; split.
    2: rewrite <- rev_accept_states.
    apply ext_transitionf_generalize with q.
    rewrite <- rev_start_states.
    1-3: intuition.
Qed.

End Reversing.