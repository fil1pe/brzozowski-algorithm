Require Export Brzozowski.

Definition nfa1 := [start 0; transition 0 0 0; accept 0].
Definition nfa2 := [start 0; transition 0 1 1; transition 0 0 2; transition 1 1 1; transition 1 0 2; accept 0; accept 1].

Compute det_nfa PeanoNat.Nat.eq_dec PeanoNat.Nat.eq_dec nfa1.
Compute det_nfa PeanoNat.Nat.eq_dec PeanoNat.Nat.eq_dec nfa2.