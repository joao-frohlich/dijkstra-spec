From Coq Require Import Strings.String.
From Coq Require Export Bool.Bool.
From Coq Require Export Arith.Arith.
From Coq Require Export Arith.PeanoNat.
From Coq Require Export Unicode.Utf8.
From Coq Require Export Lia.
From Coq Require Export Lists.List.
Export ListNotations.

Fixpoint in_nat_list (l : list nat) (x : nat) :=
    match l with
    | [] => false
    | y :: l' => if x =? y then true else in_nat_list l' x
    end.

(* Equivalência entre in_nat_list e a definição indutiva In *)
Lemma in_nat_list_iff_In : forall (l : list nat) (x : nat),
    In x l <-> in_nat_list l x = true.
Proof.
    split.
    - intros.
      induction l; auto.
      simpl.
      destruct (x =? a) eqn:E; auto.
      apply IHl.
      simpl in H.
      destruct H.
      rewrite H in E.
      assert (x =? x = true).
      { apply Nat.eqb_eq; auto. }
      rewrite E in H0.
      discriminate H0.
      apply H.
    - intros.
      induction l.
      + inversion H.
      + simpl.
        inversion H.
        destruct (x =? a) eqn:E.
        * left.
          rewrite Nat.eqb_eq in E.
          auto.
        * apply IHl in H1.
          right.
          apply H1.
Qed.

(* Remover uma ocorrência de um dado número da lista*)
Fixpoint remove_nat_one (l : list nat) (x : nat) :=
    match l with
    | [] => []
    | h :: t => if h =? x then t else h :: (remove_nat_one t x)
    end.

(* Prova que se x está em l, então o tamanho de l é igual a
1 + tamanho da lista resultante da aplicação de remove_nat_one l x*)
Lemma remove_nat_one_length : forall (l : list nat) (x : nat),
    In x l -> length l = 1 + length (remove_nat_one l x).
Proof.
    intros.
    induction l.
    - inversion H.
    - simpl.
      destruct (a =? x) eqn:E; auto.
      simpl in H.
      destruct H; auto.
      rewrite H in E.
      assert (x =? x = true).
      { apply Nat.eqb_eq. auto. }
      rewrite E in H0.
      discriminate H0.
Qed.

(* Move um elemento x para a cabeça de uma lista l *)
Definition set_nat_head (l : list nat) (x : nat) :=
    if in_nat_list l x then x :: (remove_nat_one l x) else l.

(* Prova que a aplicação de set_nat_head mantem o tamanho da lista
inalterado *)
Lemma set_nat_head_same_length : forall (l : list nat) (x : nat),
    length l = length (set_nat_head l x).
Proof.
    intros.
    induction l; auto.
    simpl.
    unfold set_nat_head.
    destruct (in_nat_list (a :: l) x) eqn:E.
    - apply in_nat_list_iff_In in E.
      simpl in E.
      simpl.
      destruct E as [H | H].
      + destruct (a =? x) eqn:E; auto.
        rewrite H in E.
        apply Nat.eqb_neq in E.
        destruct E.
        auto.
      + destruct (a =? x) eqn:E; auto.
        simpl.
        rewrite <- remove_nat_one_length; auto.
    - auto.
Qed.

Definition append_nat_lists (l1 l2 : list (list nat)) := l1 ++ l2.