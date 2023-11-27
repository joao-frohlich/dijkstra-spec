From DijkstraSpec Require Import nat_lists_extras nat_inf_type.
Import NatInf.

Module Graph.
    Definition Node := nat.
    Definition Weight := NatInf.
    Definition Adj := list (Node*Weight).
    Definition Path := list Node.
    Inductive Context := 
        | mkcontext : Node -> Adj -> Context.

    Inductive Graph :=
        | Empty : Graph
        | CGraph : Context -> Graph -> Graph.

    Declare Scope graph_scope.
    Notation "{ n , s }" := (mkcontext n s) (at level 60) : graph_scope.
    Infix "&" := CGraph (at level 60, right associativity) : graph_scope.
    Open Scope graph_scope.
End Graph.

