From DijkstraSpec Require Import nat_lists_extras graph graph_functions.
Import Graph.

Definition Empty_Graph g :=
    match g with
    | Empty => True
    | _ => False
    end.

Fixpoint Adj_In_Nodes (a : Adj) (nodes : list Node) :=
    match a with
    | [] => True
    | (n, _) :: a' => In n nodes /\ Adj_In_Nodes a' nodes
    end.

Fixpoint Valid_Graph' g nodes :=
    match g with
    | Empty => True
    | {_, s} & g' => Adj_In_Nodes s nodes /\ Valid_Graph' g' nodes
    end.

Definition Valid_Graph g := Valid_Graph' g (get_nodes g).

Fixpoint Valid_Path' (g : Graph) (path : Path) (nodes : list Node) :=
    match path with
    | [] => True
    | x :: path' => match (head path') with
                    | None => In x nodes
                    | Some y => match (get_node_context g x) with
                                | None => False
                                | Some ({_, s}) => In y (get_node_sucessors s) /\ Valid_Path' g path' nodes
                                end
                    end
    end.

Definition Valid_Path (g : Graph) (path : Path) :=
    Valid_Graph g /\ Valid_Path' g path (get_nodes g).