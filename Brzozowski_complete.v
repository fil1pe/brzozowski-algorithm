Require Export Brzozowski.

Section Brzozowski_complete.

Context {State Symbol : Type}.
Hypothesis State_eq_dec : forall (x1 x2:State), { x1 = x2 } + { x1 <> x2 }.
Definition Det_state_eq_dec := Det_state_eq_dec State_eq_dec.
Hypothesis Symbol_eq_dec : forall (x1 x2:Symbol), { x1 = x2 } + { x1 <> x2 }.
Variable nfa : @NFA State Symbol. (* No need for DFA *)

(* Minimizes NFA *)
Definition brzozowski := mini_rev_dfa Det_state_eq_dec Symbol_eq_dec (mini_rev_dfa State_eq_dec Symbol_eq_dec nfa).

(* All resulting states are distinguishable *)
Theorem all_distinguishable : forall q1 q2,
  In q1 (states brzozowski) -> In q2 (states brzozowski) ->
  equiv_states (Brzozowski.Det_state_eq_dec Det_state_eq_dec) Symbol_eq_dec brzozowski q1 q2 ->
  q1 = q2.
Proof.
  apply (
    all_distinguishable Det_state_eq_dec Symbol_eq_dec
      (mini_rev_dfa State_eq_dec Symbol_eq_dec nfa)
      (det_is_dfa State_eq_dec Symbol_eq_dec (rev_nfa nfa))
  ).
  apply (det_all_reachable State_eq_dec Symbol_eq_dec (rev_nfa nfa)).
Qed.

(* All resulting states are reachable *)
Theorem all_reachable : forall q,
  In q (states brzozowski) ->
  reachable_state (Brzozowski.Det_state_eq_dec Det_state_eq_dec) Symbol_eq_dec brzozowski q.
Proof.
  apply det_all_reachable.
Qed.

(* The resulting NFA is DFA *)
Theorem brzozowski_is_dfa :
  is_dfa (Brzozowski.Det_state_eq_dec Det_state_eq_dec) Symbol_eq_dec brzozowski.
Proof.
  apply det_is_dfa.
Qed.

(* The resulting NFA has the same language *)
Theorem same_language : forall w,
  nfa_accepts State_eq_dec Symbol_eq_dec nfa w <->
  nfa_accepts (Brzozowski.Det_state_eq_dec Det_state_eq_dec) Symbol_eq_dec brzozowski w.
Proof.
  unfold brzozowski;
  split; intros.
  - apply mini_rev_language in H.
    remember (mini_rev_dfa State_eq_dec Symbol_eq_dec nfa) as g'.
    apply mini_rev_language in H.
    replace (rev (rev w)) with w in H.
    subst; intuition.
    symmetry; apply rev_twice.
  - apply mini_rev_language.
    remember (mini_rev_dfa State_eq_dec Symbol_eq_dec nfa) as g'.
    apply mini_rev_language.
    replace (rev (rev w)) with w.
    subst; intuition.
    symmetry; apply rev_twice.
Qed.

End Brzozowski_complete.