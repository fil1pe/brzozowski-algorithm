Require Export NFA.

Section DFA.

Context {State Symbol : Type}.
Hypothesis State_eq_dec : forall (x1 x2:State), { x1 = x2 } + { x1 <> x2 }.
Hypothesis Symbol_eq_dec : forall (x1 x2:Symbol), { x1 = x2 } + { x1 <> x2 }.
Variable nfa : @NFA State Symbol.
Definition transitionf := transitionf State_eq_dec Symbol_eq_dec nfa.
Definition ext_transitionf := ext_transitionf State_eq_dec Symbol_eq_dec nfa.

Definition start_singleton :=
  (exists q, In q (start_states nfa)) /\
  forall q1 q2, In q1 (start_states nfa) -> In q2 (start_states nfa) -> q1 = q2.

Definition transitionf_det :=
  forall q a q1 q2,
  let s := transitionf [q] a in
  In q1 s -> In q2 s -> q1 = q2.

Definition is_dfa := start_singleton /\ transitionf_det.

(* The extended transitions are deterministic *)
Lemma ext_transitionf_det q w q1 q2 :
  transitionf_det ->
  let s := ext_transitionf [q] w in
  In q1 s -> In q2 s -> q1 = q2.
Proof.
  unfold ext_transitionf, transitionf_det.
  intros H H0 H1; 
  generalize dependent q2;
  generalize dependent q1;
  generalize dependent q;
  induction w as [|a w IH];
  intros q q1 H0 q2 H1.
  destruct H0, H1; subst; try contradiction; intuition.
  simpl in H0, H1.
  apply ext_transitionf_singleton in H0, H1.
  destruct H0 as [q0 [H0 H2]]; destruct H1 as [q0' [H1 H3]].
  assert (q0' = q0).
  apply H with q a.
  1,2: intuition.
  subst.
  apply IH with q0; intuition.
Qed.

(* All start states are equal *)
Lemma ext_transitionf_start_singleton q1 w q2 :
  start_singleton -> In q1 (start_states nfa) ->
  In q2 (ext_transitionf (start_states nfa) w) ->
  In q2 (ext_transitionf [q1] w).
Proof.
  intros [_ H] H0 H1.
  induction (start_states nfa) as [|q l IH].
  contradiction.
  assert (q1 = q).
  apply H; intuition.
  destruct H0; subst. {
    replace (q1 :: l) with ([q1] ++ l) in H1.
    apply in_ext_transitionf_app in H1; destruct H1.
    1,3: intuition.
    apply IH.
    intros qA qB H3 H4.
    apply H.
    1-2,4: intuition.
    apply ext_transitionf_not_nil in H0.
    destruct H0 as [q' H0].
    assert (q1 = q').
    2: subst.
    apply H.
    1-3: intuition.
  }
  replace (q :: l) with ([q] ++ l) in H1.
  apply in_ext_transitionf_app in H1; destruct H1.
  1,3: intuition.
  apply IH.
  intros qA qB H3 H4.
  apply H.
  1-4: intuition.
Qed.

End DFA.