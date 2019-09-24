Inductive natvec : nat -> Type :=
  | nil : natvec O
  | cons : forall (n: nat), nat -> natvec n -> natvec (S n).
Infix "::" := (cons _).                                    

(*Notation "x :: l" := (cons _ x l)
                     (at level 60, right associativity).*)
Notation "[ ]" := nil.
Notation "[ x ]" := (cons x nil).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Require Import Coq.Program.Tactics.
Require Import Coq.Logic.JMeq.

Program Fixpoint add' {n} (a b : natvec n) : natvec n :=
  match a with
  | nil => nil
  | ha :: ta =>
    match b with
    | nil => nil
    | hb :: tb => (ha + hb) :: add' ta tb
    end
  end.

Notation "a ⊕ b" := (add' a b)
                      (at level 50, left associativity).

Theorem plus_n_O : forall n:nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  -  simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem add_com: forall a b: nat, a + b = b + a.
Proof.
  intros a b. induction a as [| a' IHa'].
  - simpl. rewrite <- plus_n_O. reflexivity.
  - simpl. rewrite IHa', <- plus_n_Sm. reflexivity.
Qed.

Theorem add_assoc: forall a b c: nat, a + (b + c) = (a + b) + c.
Proof.
  intros a b c. induction a as [| a' IHa'].
  - reflexivity.
  - simpl. rewrite IHa'. reflexivity.
Qed.

Fixpoint zerovec (n : nat) : natvec n :=
  match n with
  | 0 => []
  | S n => 0 :: zerovec n
  end.

Theorem plusvec_u_O : forall n: nat, forall u : natvec n,
      u = u ⊕ zerovec n.
Proof.
  intros n u. induction u as [| nu u' IHu'].
  - reflexivity.
  - simpl.
    rewrite <- IHIHu'.
    rewrite <- plus_n_O.
    reflexivity.
Qed.

Definition natvec_elim_0 (P : natvec 0 -> Type) (n : P nil) : forall v, P v := fun v =>
  match v in natvec k return match k, v with
                             | S _, _ => True
                             | 0, v => P v
                             end with
  | nil => n
  | cons _ _ _ => I
  end.

Theorem add_empty: forall u : natvec 0,
    u ⊕ [] = [].
Proof.
  intros.
  destruct u using natvec_elim_0.
  reflexivity.
Qed.

Require Import Coq.Program.Equality.

Theorem addvec_commutative: forall n : nat, forall u v: natvec n,
    u ⊕ v = v ⊕ u.
Proof.
  intros u v. induction u as [| n IHu'].
  - dependent inversion v.
    intros v0. simpl.
    rewrite add_empty. reflexivity.
  - intros v0.
    dependent destruction v.
    dependent destruction v0.
    simpl. rewrite IHu', add_com. reflexivity.
Qed.
                                        
Theorem addvec_assoc : forall n, forall u v w: natvec n,
    u ⊕ (v ⊕ w) = (u ⊕ v) ⊕ w.
Proof.
  intros u v w. induction u as [| n IHu'].
  - apply natvec_elim_0, natvec_elim_0.
    rewrite add_empty, add_empty.
    reflexivity.
  - intros w0.
    dependent destruction v.
    dependent destruction w.
    dependent destruction w0.
    simpl. rewrite add_assoc, IHu'.
    reflexivity.
Qed.
    
