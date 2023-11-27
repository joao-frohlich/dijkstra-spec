# Formalização e Prova do algoritmo de Dijkstra em Coq

Este repositório apresenta uma modelagem de grafos e uma formalização e prova do algoritmo de Dijkstra usando o assistente de provas Coq. Duas implementações foram definidas, uma tendo como base a modelagem apresentada por Martin Erwig no artigo [Inductive Graphs and Functional Graph Algorithms](https://web.engr.oregonstate.edu/~erwig/papers/InductiveGraphs_JFP01.pdf) e outra modelando o algoritmo de Dijkstra como um grafo de fluxo de controle.

A implementação foi feita utilizando a versão 8.16.1 do Coq.

- Instalação do opam: https://opam.ocaml.org/doc/Install.html
- Instalação do Coq usando opam: https://coq.inria.fr/opam-using.html
  - Para instalação da versão 8.16.1 do Coq: `opam pin add coq 8.16.1`

Para gerar o Makefile deste projeto, basta executar o comando:

`coq_makefile -f _CoqProject Inductive_Graph/*.v -o Makefile`

## Implementação de Grafos Indutivos

O código está estruturado da seguinte forma, na pasta [Inductive_Graph](./Inductive_Graph):

- [nat_inf_type](./Inductive_Graph/nat_inf_type.v): Define indutivamente um tipo que representa números naturais e infinitos (NatInf), bem como algumas operações e notações sobre esse tipo
- [nat_lists_extras](./Inductive_Graph/nat_lists_extras.v): Implementa algumas funções específicas para listas de números naturais que são utilizadas no trabalho;
- [graph](./Inductive_Graph/graph.v): Modela um grafo ponderado usando uma definição indutiva e define algumas notações para a utilização dos construtores;
- [graph_functions](./Inductive_Graph/graph_functions.v): Implementa funções gerais sobre nós, arestas e o peso das arestas, baseadas na modelagem de grafos;
- [impl](./Inductive_Graph/impl.v): Contém a implementação dos algoritmos de buscar todos os caminhos e de Dijkstra.
- [graph_specs](./Inductive_Graph/graph_specs.v): Contém uma especificação de corretude em cima da modelagem de grafos, caminhos e da equivalência entre a função de Dijkstra e a função de buscar todos os caminhos.
- [perm_paths](./Inductive_Graph/perm_paths.v): Implementa uma função equivalente à função de buscar todos os caminhos de um grafo, bem como define uma proposição para mostrar a equivalência entre as definições
- [example_graph_1](./Inductive_Graph/example_graph_1.v) e [example_graph_2](./Inductive_Graph/example_graph_2.v): Mostram exemplos do uso desta definição.

## Implementação por Grafo de Fluxo de Controle

Todo o código está no arquivo [dijkstra.v](./CFG/dijkstra.v) da pasta [CFG](./CFG). Também foi
realizada a extração da implementação para a linguagem _Haskell_, que pode ser visualizada no
arquivo [dijkstra.hs](./CFG/dijkstra.hs).

## Histórico de implementações

Na pasta [Tentativas/](./Tentativas/) estão contidos os arquivos de teste de modelagem de grafos e implementação dos algoritmos, e a existência da pasta está mais para um registro histórico (eu sei que existe o registro de commits para isso, mas achei melhor manter a pasta). Também dentro desta pasta está o código apresentado na primeira fase do TCC, que mostrava apenas uma formalização de caminhos ponderados, sem nenhum envolvimento de grafos. Para compilar esse arquivo em específico, sugiro usar a versão 8.17 do Coq e também a versão 1.17.0 da [Mathematical Components](https://math-comp.github.io/installation.html)