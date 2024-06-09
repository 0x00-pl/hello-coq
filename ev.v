Inductive ev: nat->Prop :=
| EVO: ev 0
| EV2: ev 2         
| EVSum: forall n1 n2, ev n1 -> ev n2 -> ev (n1 + n2).

Hint Constructors ev.

Require Import Omega.

Print Ltac intuition.

Lemma not_ev_1: ~ ev 1.
Proof.
  intro.
  remember 1.
  induction H; try omega.
  destruct n1; destruct n2; intuition; try omega.
Qed.

Hint Resolve not_ev_1.

Ltac tt :=
  match goal with
    | [H: _ = _ + 0 |- _ ] => intuition
    | [H: S ?n1 + S ?n2 = 3 |- _ ] => 
      idtac n1; idtac n2; destruct n1; destruct n2; intuition; try omega
           | [H: ?n1 + ?n2 = 3 |- _ ] => 
             idtac n1; idtac n2; destruct n1; destruct n2; intuition; try omega
  end.

Fixpoint mod2 (n:nat) :bool :=
  match n with
    | 0 => true
    | 1 => false
    | S (S n') => mod2 n'
  end. 
Fixpoint div2 (n:nat) :nat :=
  match n with
    | 0 => 0
    | 1 => 0
    | S (S n') => S (div2 n')
  end.
Definition dm2 (d2:nat) (m2:bool) :nat :=
  if m2 then d2+d2 else S(d2+d2).

Lemma mod2_S: forall n, mod2 n = negb (mod2 (S n)).
Proof.
  intros.
  induction n; auto.
  destruct (mod2 n) eqn:E;
    destruct (mod2 (S n)) eqn:Ei; inversion IHn;
    simpl; rewrite E; auto.
Qed.


Lemma dm2_eq: forall n, n=dm2 (div2 n) (mod2 n).
Proof.
  induction n; auto.
  destruct (mod2 n) eqn:E; rewrite mod2_S in E;
  [apply Bool.negb_true_iff in E|apply Bool.negb_false_iff in E];
  rewrite E.
  unfold dm2 in *.
  apply eq_S.
  rewrite IHn.
  rewrite mod2_S in E.
  apply Bool.negb_false_iff in E.
  simpl in E.
  assert(forall m, div2 (S (m+m)) = m).
  induction m; auto.
  simpl. apply eq_S.
  replace (m+S m) with (S(m+m)) by auto.
  auto.
  rewrite H. auto.

  unfold dm2 in *.
  rewrite IHn. simpl.
  apply eq_S.
  assert(forall m, div2 (m+m) = m).
  induction m; auto.
  replace(S m + S m)with(S (S (m+m)))by omega.
  simpl. auto. 
  rewrite H.
  omega.
Qed.

Lemma mod2_nn: forall n, mod2 n = true -> div2 n + div2 n = n.
Proof.
  induction n; eauto; intros.

  destruct n; auto. inversion H.

  unfold mod2 in *.
  
  destruct(mod2 n) eqn:E; auto.
  rewrite mod2_S in E.
  rewrite Bool.negb_true_iff in E.
Abort.

Lemma ind2: forall P, P 0 -> P 1 -> (forall m, P m -> P (S (S m))) -> (forall n, P n).
Proof.
  intros.
  rewrite (dm2_eq n).
  remember (div2 n) as a.
  remember (mod2 n) as b.
  generalize dependent n.
  induction a. destruct b; auto.
  intros.
  destruct n. rewrite Heqa. rewrite Heqb.
  rewrite <- dm2_eq. auto.
  destruct n. rewrite Heqa. rewrite Heqb.
  rewrite <- dm2_eq. auto.
  rewrite Heqa. rewrite Heqb.
  rewrite <- dm2_eq.
  inversion Heqa. simpl in *; subst.
  rewrite <- dm2_eq in IHa.
  apply X1. apply (IHa n); auto.
Qed.


Lemma not_ev_3: ~ ev 3.
Proof.
  intro.
  remember 3.
  induction H. inversion Heqn. inversion Heqn.
  destruct n1; auto.
  destruct n1; auto.
  destruct n1; auto. inversion Heqn; subst; auto.
  destruct n1; auto. inversion Heqn.
Qed.

Hint Resolve not_ev_3.

Lemma ev_SS: forall n, ev n -> ev (S (S n)).
Proof.
  apply (ind2 (fun n => ev n -> ev (S (S n)))).
  auto. intro. apply not_ev_1 in H. inversion H.

  intros.
  replace(S (S (S (S m))))with(2+(2+m))by omega.
  apply EVSum; auto.
Qed.

Lemma ev_SS': forall n, ev (S (S n)) -> ev n.
Proof.
  intros.
  remember (S (S n)).
  induction H.
  inversion Heqn0.
  inversion Heqn0; auto.

  remember (S (S n)).
  destruct n1; auto.
  destruct n1. apply not_ev_1 in H. inversion H.
  
  
  generalize dependent n2.
  generalize dependent n1.
Abort.

Hint Resolve ev_SS.

Theorem not_ev_S: forall n, ev n <-> ~(ev (S n)).
  apply ind2; split; auto; intro.
  + specialize(H EV2). inversion H.
  + intuition.
    
    auto.
  intros. intro.
  inversion H0; subst.
  apply
  inversion H1; subst.
  destruct n1; simpl in *; subst.
  simpl in H0.
  simpl.
  
  intro. inversion H1.
  destruct n1; simpl in H3; subst; auto.
  destruct n1. simpl in *; inversion H3; subst; auto.
  inversion H3.
  inversion H2.
  

  
  tt.
  destruct n1; destruct n2; intuition; try omega.  
  intro. inversion H.
  destruct n1; SIMPL IN H0; SUBST.
  induction n; intros; auto.
  + intro.
    inversion H0.