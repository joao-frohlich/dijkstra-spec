From DijkstraSpec Require Import graph nat_lists_extras nat_inf_type.
Import Graph.
Import NatInf.

Fixpoint get_node_context (g : Graph) (u : Node) : option Context :=
    match g with
    | Empty => None
    | {n, s} & g' =>
        if n =? u then
            Some ({n, s})
        else
            get_node_context g' u
    end.
    
Fixpoint get_node_sucessors (a : Adj) : list Node :=
    match a with
    | [] => []
    | (n, _) :: a' => n :: get_node_sucessors a'
    end.

Fixpoint get_nodes (g : Graph) : list Node :=
    match g with
    | Empty => []
    | ({n, _}) & g' => n :: (get_nodes g')
    end.

Definition add_node (g : Graph) (x : Node) :=
    match get_node_context g x with
    | None => (mkcontext x []) & g
    | Some _ => g
    end.

Fixpoint add_edge' (g : Graph) (o d : Node) (p : Weight) :=
    match g with
    | Empty => Empty
    | (mkcontext n s) & g' =>
        if o =? n then
            (mkcontext n ((d,p) :: s)) & g'
        else
            (mkcontext n s) & add_edge' g' o d p
    end.
    
Definition add_edge (g : Graph) (o d : Node) (p : Weight) :=
    add_edge' (add_node (add_node g o) d) o d p.

Fixpoint add_edges (g : Graph) (l : list (Node*Node*Weight)) :=
    match l with
    | [] => g
    | (o,d,p) :: l' => add_edges (add_edge g o d p) l'
    end.

Fixpoint get_elem_in_list (a : Adj) (b : list nat) :=
    match a with
    | [] => []
    | (h, _) :: t => if in_nat_list b h then
        h :: get_elem_in_list t b
    else
        get_elem_in_list t b
    end.

Fixpoint get_node_dist (dist : list (Node*Weight)) (u : Node) : Weight :=
    match dist with
    | [] => Infty
    | (u',w) :: dist' => if u =? u' then w else get_node_dist dist' u
    end.

Fixpoint update_node_dist (dist : list(Node*Weight)) (u : Node) (w : Weight) : list(Node*Weight) :=
    match dist with
    | [] => []
    | (u', w') :: dist' => if u =? u' then (u,w) :: dist' else (u',w') :: update_node_dist dist' u w
    end.

Fixpoint get_edges_in_list (a : Adj) (b : list Node) :=
    match a with
    | [] => []
    | (v,w) :: t => if in_nat_list b v then (v, w) :: get_edges_in_list t b else get_edges_in_list t b
    end.

Fixpoint min_weight_in_list (dist : list(Node*Weight)) (l : list Node) : Weight :=
    match dist with
    | [] => Infty
    | (u,w) :: t => let md := min_weight_in_list t l in
        if in_nat_list l u then
            if w <?i md then w else md
        else md
    end.

Fixpoint node_with_min_weight_in_list (dist : list(Node*Weight)) (l : list Node) (w : Weight) :=
    match dist with
    | [] => None
    | (u,w') :: t =>  if in_nat_list l u then
        if w =?i w' then
            Some u
        else
            node_with_min_weight_in_list t l w
    else
        node_with_min_weight_in_list t l w
    end.

Definition next_node (dist : list(Node*Weight)) (to_vis : list Node) :=
    node_with_min_weight_in_list dist to_vis (min_weight_in_list dist to_vis).

Fixpoint get_edge_weight (a : Adj) (x : Node) : option Weight :=
    match a with
    | [] => None
    | (y,w) :: a' => if x =? y then Some w else get_edge_weight a' x
    end.

Fixpoint get_path_weight (g : Graph) (path : Path) :=
    match path with
    | [] => Infty
    | [x] => |0|
    | x :: path' => match head path' with
        | None => Infty
        | Some y => match (get_node_context g x) with
            | None => Infty
            | Some ({_, s}) => match (get_edge_weight s y) with
                | None => Infty
                | Some w => w +i get_path_weight g path'
                end
            end
        end
    end.