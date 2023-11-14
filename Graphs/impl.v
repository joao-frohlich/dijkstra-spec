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



(* 
Dijkstra(G, s)
    b0:
    for all u ∈ V,
        b1:
        d(u) <- ∞
    b2:
    d(s) <- 0
    R <- {}
    b3:
    while R != V
        b4:
        u <- vertex not in R with smallest d(u)
        R <- insert u R
        b5:
        for all vertices v adjacent to u
            b6:
            alt <- d(u) + l(u, v)
            if d(v) > alt
                b7:
                d(v) <- alt
    b8:
    return d
  *)

  Definition distances := list (Node * Weight).

  Fixpoint set (dist : distances) (u : Node) (w : Weight) :=
    match dist with
    | [] => []
    | (u', w') :: dist' =>
      if u =? u' then
        (u, w) :: dist'
      else
        (u', w') :: set dist' u w
    end.

  Fixpoint get (dist : distances) (u : Node) :=
    match dist with
    | [] => Infty
    | (u', w') :: dist' =>
      if u =? u' then
        w'
      else
        get dist' u
    end.

  Fixpoint edge_weight (G : Graph) (u v : Node) :=
    match G with
    | Empty => Infty
    | {n, s} & G' =>
      if n =? u then
        get s v
      else
        edge_weight G' u v
    end.

  Fixpoint set_diff (V R : list Node) :=
    match V with
    | [] => []
    | v :: V' =>
      if in_nat_list R v then
        set_diff V' (remove_nat_one R v)
      else
        v :: set_diff V' R
    end.

  Fixpoint get_sucessors (G : Graph) (u : Node) :=
    match G with
    | Empty => []
    | {n, s} & G' =>
      if n =? u then
        get_node_sucessors s
      else
        get_sucessors G' u
    end.

  Fixpoint b5 (G : Graph) (s : Node) (u : Node) (dist : distances) (adj : list Node) :=
    match adj with
    | [] => dist
    | v :: adj' =>
      (* b6 *)
      let alt := (get dist u) +i (edge_weight G u v) in
      if alt <?i (get dist v) then
        (* b7 *)
        let dist' := set dist v alt in
        b5 G s u dist' adj'
      else
        b5 G s u dist adj'
    end.

  Program Fixpoint b3 (G : Graph) (s : Node) (dist : distances) (V R : list Node) { measure (length V - length R) } :=
    let R_Comp := (set_diff V R) in
    match R_Comp with
    | [] => dist
    | _ =>
      let u := next_node dist R_Comp in
      match u with
      | None => dist
      | Some u' =>
        let R' := (u' :: R) in
        let dist' := b5 G s u' dist (get_sucessors G u') in
        b3 G s dist' V R'
      end
    end.

  Next Obligation.
  Proof.
    admit.
  Admitted.


  Fixpoint b1 (V : list Node) : distances :=
    match V with
    | [] => []
    | v :: V' => (v, Infty) :: b1 V'
    end.

  Definition b0 (G : Graph) (s : Node) :=
    let V := get_nodes G in
    let dist := b1 V in
    (* b2 *)
    let dist' := set dist s (|0|) in
    let R := [] in
    b3 G s dist' V R.