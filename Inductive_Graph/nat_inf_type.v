From Coq Require Import Strings.String.
From Coq Require Export Bool.Bool.
From Coq Require Export Arith.Arith.
From Coq Require Export Arith.PeanoNat.

Module NatInf.
    Inductive NatInf :=
        | Nat : nat -> NatInf
        | Infty : NatInf.

    Definition sum_inf (a b : NatInf) : NatInf :=
        match a,b with
        | Infty, _ => Infty
        | _, Infty => Infty
        | Nat x, Nat y => Nat (x + y)
        end.

    Definition Lt_inf (a b : NatInf) : Prop :=
        match a,b with
        | Infty, Infty => True
        | _, Infty => True
        | Infty, _ => False
        | Nat x, Nat y => x < y
        end.

    Definition Eq_inf (a b : NatInf) : Prop :=
        match a,b with
        | Infty, Infty => True
        | Nat x, Nat y => (x = y)
        | _, _ => False
        end.

    Definition Le_inf (a b : NatInf) : Prop :=
        Lt_inf a b \/ Eq_inf a b.

    Definition ltb_inf (a b : NatInf) : bool :=
        match a,b with
        | Infty, Infty => true
        | Infty, _ => false
        | _, Infty => true
        | Nat x, Nat y => (x <? y)
        end.

    Definition eqb_inf (a b : NatInf) : bool :=
        match a,b with
        | Infty, Infty => true
        | Nat x, Nat y => (x =? y)
        | _, _ => false
        end.

    Definition min_inf (a b : NatInf) : NatInf :=
        match a, b with
        | Infty, Infty => Infty
        | Nat x, Infty => Nat x
        | Infty, Nat y => Nat y
        | Nat x, Nat y => Nat (min x y)
        end.

    Declare Scope natinf.
    Notation "| n |" := (Nat n) (at level 60) : natinf.
    Notation "a +i b" := (sum_inf a b) (at level 60) : natinf.
    Notation "a <i b" := (Lt_inf a b) (at level 60) : natinf.
    Notation "a =i b" := (Eq_inf a b) (at level 60) : natinf.
    Notation "a <=i b" := (Le_inf a b) (at level 60) : natinf.
    Notation "a <?i b" := (ltb_inf a b) (at level 60) : natinf.
    Notation "a =?i b" := (eqb_inf a b) (at level 60) : natinf.
    Open Scope natinf.
End NatInf.