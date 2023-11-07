From DijkstraSpec Require Import nat_lists_extras graph graph_functions impl.
Import Graph.

Definition Empty_Graph (g : Graph) : Prop :=
    match g with
    | Empty => True
    | _ => False
    end.

Fixpoint Adj_In_Nodes (a : Adj) (nodes : list Node) : Prop :=
    match a with
    | [] => True
    | (n, _) :: a' => In n nodes /\ Adj_In_Nodes a' nodes
    end.

Fixpoint Valid_Graph' (g : Graph) (nodes : list Node) : Prop :=
    match g with
    | Empty => True
    | {_, s} & g' => Adj_In_Nodes s nodes /\ Valid_Graph' g' nodes
    end.

Definition Valid_Graph (g : Graph) : Prop := Valid_Graph' g (get_nodes g).

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

Fixpoint Valid_Paths (g : Graph) (paths : list Path) :=
    match paths with
    | [] => True
    | path :: paths' => Valid_Path g path /\ Valid_Paths g paths'
    end.

Definition Get_Paths_Valid (g : Graph) (o d : Node) :=
    Valid_Paths g (get_paths g o d).

Fixpoint Min_Weight (g: Graph) (inf : Weight) (w : Weight) (paths : list Path) :=
    match paths with
    | [] => True
    | path :: paths' => w <= (get_path_weight g inf path) /\ Min_Weight g inf w paths'
    end.

Definition Dijkstra_Min_Weight (g : Graph) (o d : Node) :=
    Min_Weight g (sum_weights g) (dijkstra g o d) (get_paths g o d).