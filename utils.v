Require Import List Bool.
Include ListNotations.


(** Lists and sets **)

(* Checks if x in l *)
Fixpoint inb {A} (eq:A->A->bool) x l :=
  match l with
  | nil => false
  | x'::l => eq x x' || inb eq x l
  end.

Lemma inb_correct {A} (eq:A->A->bool) x l :
  (forall x x', x=x' <-> eq x x'=true) ->
  inb eq x l = true <-> In x l.
Proof.
  intros.
  induction l.
  - split; intros; inversion H0.
  - simpl; destruct (eq x a) eqn:H0.
    + split; intros.
      * left; symmetry; apply H; auto.
      * auto.
    + split; intros.
      * right; apply IHl; auto.
      * destruct H1.
        -- symmetry in H1; apply H in H1; rewrite H1 in H0; discriminate H0.
        -- apply IHl; auto.
Qed.

Definition subset {A} (s1 s2:list A) :=
  forall x, In x s1 -> In x s2.

(* Checks if s1 is subset of s2 *)
Fixpoint subsetb {A} (eq:A->A->bool) s1 s2 :=
  match s1 with
  | nil => true
  | x::s1 => inb eq x s2 && subsetb eq s1 s2
  end.

Lemma subsetb_correct {A} (eq:A->A->bool) s1 s2 :
  (forall x x', x=x' <-> eq x x'=true) ->
  subsetb eq s1 s2 = true <-> subset s1 s2.
Proof.
  unfold subset; intros.
  induction s1.
  - split; intros.
    + inversion H1.
    + auto.
  - simpl; split; intros.
    + destruct H1.
      * subst; apply (inb_correct eq).
        -- apply H.
        -- apply andb_prop in H0; destruct H0; auto.
      * apply andb_prop in H0; destruct H0;
        destruct IHs1; apply H3 with (x:=x) in H2; auto.
    + apply andb_true_intro; split.
      * apply inb_correct.
        -- auto.
        -- apply H0; left; auto.
      * apply IHs1; intros; apply H0; right; auto.
Qed.

(* Sets equivalence means that the sets have the same elements *)
Definition eq_sets {A} (s1 s2:list A) :=
  forall x, In x s1 <-> In x s2.

(* A set is equivalent to itself *)
Lemma eq_sets_self {A} (s:list A) :
  eq_sets s s.
Proof.
  split; intuition.
Qed.

(* Commutative property of sets equivalence *)
Lemma eq_sets_comm {A} (s1 s2:list A) :
  eq_sets s1 s2 -> eq_sets s2 s1.
Proof.
  unfold eq_sets; intros; split; intros;
  apply H; auto.
Qed.

(* Transitive property of sets equivalence *)
Lemma eq_sets_transitive {A} (s1 s2 s3:list A) :
  eq_sets s1 s2 -> eq_sets s1 s3 -> eq_sets s2 s3.
Proof.
  unfold eq_sets; intros; split; intros.
  - apply H0, H; auto.
  - apply H, H0; auto.
Qed.

(* Equivalent sets rewrite rule for subset *)
Lemma subset_eq {A} (s1 s2 s3:list A) :
  eq_sets s1 s3 -> (subset s1 s2 <-> subset s3 s2).
Proof.
  unfold subset, eq_sets; split; intros;
  apply H0, H, H1.
Qed.

(* Checks if s1 is equivalent to s2 *)
Definition eq_setsb {A} (eq:A->A->bool) s1 s2 :=
  subsetb eq s1 s2 && subsetb eq s2 s1.

Lemma eq_setsb_correct {A} (eq:A->A->bool) s1 s2 :
  (forall x x', x=x' <-> eq x x'=true) ->
  eq_setsb eq s1 s2 = true <-> eq_sets s1 s2.
Proof.
  unfold eq_setsb; split; intros.
  - apply andb_true_iff in H0; destruct H0.
    pose proof subsetb_correct eq.
    split; intros.
    + apply (H2 s1 s2) in H; destruct H as [H _].
      apply H in H0; intuition.
    + apply (H2 s2 s1) in H; destruct H as [H _].
      apply H in H1; intuition.
  - apply andb_true_iff; split;
      apply subsetb_correct;
        try (unfold subset; intros; destruct H0 with x); auto.
Qed.

(* Commutative property for the decider *)
Lemma eq_setsb_comm {A} (eq:A->A->bool) s1 s2 :
  (forall x x', x=x' <-> eq x x'=true) ->
  eq_setsb eq s1 s2 = eq_setsb eq s2 s1.
Proof.
  intros.
  destruct (eq_setsb eq s1 s2) eqn:H0;
  destruct (eq_setsb eq s2 s1) eqn:H1.
  1,4: auto.
  - assert (eq_setsb eq s2 s1 = true).
    2: rewrite H2 in H1; discriminate.
    apply eq_setsb_correct;
    apply eq_setsb_correct, eq_sets_comm in H0; auto.
  - assert (eq_setsb eq s1 s2 = true).
    2: rewrite H2 in H0; discriminate.
    apply eq_setsb_correct;
    apply eq_setsb_correct, eq_sets_comm in H1; auto.
Qed.

(* The decider result is equal for equivalent states *)
Lemma eq_setsb_equals {A} eq (s1 s2 s:list A) :
  (forall x1 x2, x1=x2 <-> eq x1 x2=true) ->
  eq_sets s1 s2 ->
  eq_setsb eq s1 s = eq_setsb eq s2 s.
Proof.
  intros; destruct (eq_setsb eq s1 s) eqn:H1, (eq_setsb eq s2 s) eqn:H2.
  1,4: auto.
  - apply eq_setsb_correct in H1.
    2: auto.
    assert (eq_setsb eq s2 s = true).
    2: rewrite H3 in H2; discriminate.
    apply eq_setsb_correct;
    try apply eq_sets_transitive with s1; auto.
  - apply eq_setsb_correct in H2.
    assert (eq_setsb eq s1 s = true).
    2: rewrite H3 in H1; discriminate.
    apply eq_setsb_correct.
    2: apply eq_sets_transitive with s2.
    2: apply eq_sets_comm.
    1-4: auto.
Qed.

(* Checks whether a possibly undefined value x is in a possibly undefined list *)
Definition in_opt {A} (x:option A) l :=
  match x with
  | None => False
  | Some x => match l with
              | None => False
              | Some l => In x l
              end
  end.

(* Returns a set equivalent to s in l or itself if none is found *)
Fixpoint get_set {A} (eq:A->A->bool) s l :=
  match l with
  | nil => s
  | s'::l => if (eq_setsb eq s s') then s'
             else get_set eq s l
  end.

(* The returned set is indeed equivalent *)
Lemma get_set_eq {A} (eq:A->A->bool) s l :
  (forall a b, a=b <-> eq a b = true) ->
  eq_sets s (get_set eq s l).
Proof.
  intros; induction l.
  split; auto.
  simpl; destruct (eq_setsb eq s a) eqn:H0.
  2: auto.
  apply eq_setsb_correct in H0; auto.
Qed.

(* Decider for lists equality *)
Fixpoint lists_eq {A} (eq:A->A->bool) l1 l2 :=
  match l1, l2 with
  | nil, nil => true
  | x1::l1, x2::l2 => eq x1 x2 && lists_eq eq l1 l2
  | _, _ => false
  end.

Lemma lists_eq_correct {A} {eq:A->A->bool} (H:forall q1 q2, q1=q2 <-> eq q1 q2=true) :
  forall q1 q2, q1=q2 <-> lists_eq eq q1 q2=true.
Proof.
  split; intros.
  - symmetry in H0; subst.
    induction q1.
    2: simpl; apply andb_true_intro; split.
    2: apply H; auto.
    1-2: auto.
  - generalize dependent q2; induction q1; intros.
    + destruct q2.
      auto.
      discriminate.
    + destruct q2.
      discriminate.
      simpl in H0; apply andb_prop in H0; destruct H0;
      apply H in H0; symmetry in H0;
      apply IHq1 in H1; subst; auto.
Qed.


(** Excluded middle **)

Definition eq_dec {A} (eq:A->A->bool) (H: forall a b, a=b <-> eq a b = true) :
  forall (a b:A), {a = b} + {a <> b}.
Proof.
  intros.
  destruct (eq a b) eqn:H0.
  left; apply H; auto.
  right; intros H1; apply H in H1; rewrite H0 in H1; discriminate.
Qed.








