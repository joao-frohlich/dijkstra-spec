From DijkstraSpec Require Import nat_lists_extras graph graph_functions impl graph_specs.
Require Import Coq.Program.Wf.
Import Graph.

Program Fixpoint generate_everything' (sz : nat) (to_use : list nat) (nxt : nat) {measure (length to_use)} : list (list nat) :=
    match sz with
    | 0 => [[]]
    | S n =>
        let to_use' :=
            set_nat_head to_use nxt
        in
        let aux (x : nat) :=
            match to_use' with
            | [] => []
            | h :: t => map (cons h) (generate_everything' n t x)
            end
        in
        fold_left append_nat_lists (map aux to_use') []
    end.
Next Obligation.
Proof.
  rename Heq_to_use' into H.
  unfold set_nat_head in H.
  destruct (in_nat_list to_use nxt) eqn:E in H.
  - injection H.
    apply in_nat_list_iff_In in E.
    intros H1 H2.
    rewrite H1.
    unfold lt.
    rewrite <- remove_nat_one_length; auto.
  - rewrite <- H. auto.
Qed.

Fixpoint eq_lists (l1 l2 : list nat) : bool :=
    match l1,l2 with
    | [], [] => true
    | x :: l1', y :: l2' => (x =? y) && eq_lists l1' l2'
    | _, _ => false
    end.

Fixpoint list_in_lists (l : list nat) (ls : list (list nat)) : bool :=
    match ls with
    | [] => false
    | l' :: ls' => (eq_lists l l') || list_in_lists l ls'
    end.

Fixpoint eliminate_duplicates (ls : list (list nat)) : list (list nat) :=
    match ls with
    | [] => []
    | l :: ls' => if list_in_lists l ls' then eliminate_duplicates ls' else l :: eliminate_duplicates ls'
    end.

Definition generate_perms (sz : nat) (l : list nat) : list (list nat) :=
    eliminate_duplicates (fold_left (append_nat_lists) (map (generate_everything' sz l) l) [[]]).

Fixpoint generate_paths' (sz : nat) (l : list nat) : list (list nat) :=
    match sz with
    | 0 => [[]]
    | S n => fold_left append_nat_lists [(generate_perms sz l)] (generate_paths' n l)
    end.

Fixpoint eliminate_empty_perms (ls : list (list nat)) : list (list nat) :=
    match ls with
    | [] => []
    | l :: ls' => match l with
        | [] => eliminate_empty_perms ls'
        | _ => l :: eliminate_empty_perms ls'
        end
    end.

Definition generate_perms_of_all_sizes (l : list nat) :=
    eliminate_duplicates (generate_paths' (length l) l).

Definition generate_all_graph_paths (g : Graph) :=
    generate_perms_of_all_sizes (get_nodes g).

Fixpoint eliminate_invalid_paths (g : Graph) (paths : list Path) :=
    match paths with
    | [] => [[]]
    | path :: paths' => if valid_pathb g path then path :: eliminate_invalid_paths g paths'
        else eliminate_invalid_paths g paths'
    end.

Definition generate_all_valid_graph_paths (g : Graph) :=
    eliminate_empty_perms (eliminate_invalid_paths g (generate_all_graph_paths g)).

Fixpoint paths_with_o_head (paths : list Path) (o : Node) :=
    match paths with
    | [] => [[]]
    | path :: paths' => match path with
        | [] => paths_with_o_head paths' o
        | x :: path' => if o =? x then
                            path :: paths_with_o_head paths' o
                        else
                            paths_with_o_head paths' o
        end
    end.

Fixpoint paths_with_d_last (paths : list Path) (d : Node) :=
    match paths with
    | [] => [[]]
    | path :: paths' => if (last path (d+1)) =? d then
                            path :: paths_with_d_last paths' d
                        else
                            paths_with_d_last paths' d
    end.

Definition generate_all_valid_graph_paths_from_o_to_d (g : Graph) (o d : Node) :=
    eliminate_empty_perms (paths_with_d_last (paths_with_o_head (generate_all_valid_graph_paths g) o) d).