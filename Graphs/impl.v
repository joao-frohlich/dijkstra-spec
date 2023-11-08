From DijkstraSpec Require Import nat_lists_extras graph graph_functions nat_inf_type.
Require Import Coq.Program.Wf.
Import Graph.
Import NatInf.

(* Funciona semelhante a uma função de DFS, porém retorna todos os caminhos sem loops entre u e d no
grafo g. Dá para provar propriedades como a garantia que todos os caminhos válidos são gerados. Uma ideia para pegar
todos os caminhos seria gerar todas as combinações de nós sem repetição de tamanhos variados, e selecionar os caminhos
válidos que tenham o como cabeça e d como final *)
Program Fixpoint get_paths' (g : Graph) (u d : Node) (to_vis : list Node) {measure (length to_vis)} : list Path :=
  (* Verifica se o nó atual é o mesmo nó que está sendo procurado pela busca *)
  if u =? d then [[u]]
  else
    (* Move o nó atual da busca para a frente de nós a serem visitados *)
    let (* 1 *) to_vis' := 
      set_nat_head to_vis u
    in
    (* Salva a lista de nós a serem visitados a partir do nó atual. Só são considerados nós que ainda
    não foram visitados *)
    let (* 2 *) suc := match (get_node_context g u) with
    | None => []
    | Some (mkcontext _ s) => get_elem_in_list s to_vis
    end in
    (* Função auxiliar para chamar a função get_paths' recursivamente, pois a necessidade de especificar um
    nó x impede que isso seja feito na função fold_left *)
    let (* 3 *) aux (x : Node) :=
      match (* 1' *) to_vis' with
      | [] => []
      | h :: t => map (cons h) (get_paths' g x d t)
      end
    in
    (* Aplicação da função get_path' sobre todos os sucessores do nó atual *)
    fold_left append_nat_lists (map (* 3' *) aux (* 2' *) suc) [].
Next Obligation.
Proof.
  rename Heq_to_vis' into H.
  unfold set_nat_head in H.
  destruct (in_nat_list to_vis u) eqn:E in H.
  - injection H.
    apply in_nat_list_iff_In in E.
    intros H1 H2.
    rewrite H1.
    unfold lt.
    rewrite <- remove_nat_one_length; auto.
  - rewrite <- H. auto.
Qed.

Definition get_paths (g : Graph) (o d : Node) :=
  get_paths' g o d (get_nodes g).

Definition get_paths_from_o_to_d (g : Graph) (o d : Node) : list Weight :=
  map (get_path_weight g) (get_paths g o d).

Definition get_min_weight_from_o_to_d (g : Graph) (o d : Node) : Weight :=
  fold_left min_inf (get_paths_from_o_to_d g o d) Infty.

Program Fixpoint dijkstra' (g : Graph) (u d : Node)
  (to_vis : list Node) (dist : list (Node*Weight)) {measure (length to_vis)} : Weight :=
  if u =? d then (get_node_dist dist d)
  else
    let to_vis' :=
      set_nat_head to_vis u
    in
    let suc := match (get_node_context g u) with
      | None => []
      | Some ({_, s}) => get_edges_in_list s to_vis
    end in
    let relax (dist : list (Node*Weight)) (n : (Node*Weight)) : list (Node*Weight) :=
      let v := (fst n) in
      let w := (snd n) in
      let new_dist := 
        (get_node_dist dist u) +i w
      in
      if (new_dist) <?i (get_node_dist dist v) then
        update_node_dist dist v new_dist
      else
        dist
    in
    let new_dist_list : list (Node*Weight) :=
      fold_left (relax) suc dist
    in
    match to_vis' with
      | [] => (get_node_dist dist d)
      | h :: t => match (next_node new_dist_list t) with
        | None => (get_node_dist dist d)
        | Some v => dijkstra' g v d t new_dist_list
      end
    end.
Next Obligation.
Proof.
  rename Heq_to_vis' into H.
  unfold set_nat_head in H.
  destruct (in_nat_list to_vis u) eqn:E in H.
  - injection H.
    apply in_nat_list_iff_In in E.
    intros H1 H2.
    rewrite H1.
    unfold lt.
    rewrite <- remove_nat_one_length; auto.
  - rewrite <- H. auto.
Qed.

Definition dijkstra (g : Graph) (o d : Node) : Weight :=
  let dist :=
    (combine (get_nodes g) (repeat Infty (length (get_nodes g))))
  in
  dijkstra' g o d (get_nodes g) (update_node_dist dist o (|0|)).