From Coq Require Import Strings.String.  (* for manual grading *)
From Coq Require Export Bool.Bool.
From Coq Require Export Arith.Arith.
From Coq Require Export Arith.PeanoNat.
From Coq Require Export Arith.EqNat.
From Coq Require Export Lia.
From Coq Require Export Lists.List.
Export ListNotations.
From Coq Require Export Permutation.
From Coq Require Import Logic.FunctionalExtensionality.

(* Definition total_map (A : Type) : Type := nat -> A.

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A : Type}
  (m : total_map A) (x : nat) (v : A) : total_map A :=
fun x' => if x =? x' then v else m x'.

Definition partial_map (A : Type) := total_map (option A).
Definition empty {A : Type} : partial_map A :=
  t_empty None.
Definition update {A : Type}
           (m : partial_map A) (x : nat) (v : A) : partial_map A :=
  t_update m x (Some v). *)

Definition total_map : Type := (nat*nat) -> nat.

Definition t_empty : total_map :=
  (fun _ => 0).

Definition pair_eq (a b : nat*nat) :=
  match a,b with
  (x, y), (x', y') => (x =? x') && (y =? y')
  end.

Definition t_update
  (m : total_map) (k : nat*nat) (v : nat) : total_map :=
  fun k' => if (pair_eq k k') then v else m k'.

Definition graph := total_map.

Definition empty_graph := t_empty.

Definition insert_edge
  (g : graph) (edge: nat*nat) (weight : nat) : graph :=
  match edge with
    (x,y) => if x =? y then g else
              fun e => if (pair_eq edge e) then weight else g e
  end.

Definition example_graph_1 :=
  insert_edge (insert_edge (empty_graph) (1,2) 1) (1,2) 2.

Definition example_graph_2 :=
  insert_edge (empty_graph) (1,1) 10.

Compute example_graph_1 (1,2).

Example example_graph_1_weight :
  example_graph_1 (1,2) = 2.
Proof.
  reflexivity.
Qed.

Example example_graph_2_empty :
  example_graph_2 = empty_graph.
Proof.
  reflexivity.
Qed.

(* Fixpoint in_list (x : nat) (l : list nat) : bool :=
  match l with
  | [] => false
  | x' :: l' => if x =? x' then true else in_list x l'
  end.

Fixpoint is_connected (g : graph) (x d : nat) (vis : list nat) : bool :=
  if x =? d then true else
    match (in_list x vis) with
    | true => false
    | false =>
      fun e => match e with
      | (u, v) => if u =? x then is_connected g v d (x::vis) else false
      end 
    end. *)