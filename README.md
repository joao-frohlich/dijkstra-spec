# Formalização e Prova do algoritmo de Dijkstra em Coq

Este repositório apresenta uma modelagem de grafos e uma formalização e prova do algoritmo de Dijkstra usando o assistente de provas Coq. Para a modelagem e implementação, foi usado como base as definições apresentadas por Martin Erwig no artigo [Inductive Graphs and Functional Graph Algorithms](https://web.engr.oregonstate.edu/~erwig/papers/InductiveGraphs_JFP01.pdf).

A implementação foi feita utilizando a versão 8.16.1 do Coq.

- Instalação do opam: https://opam.ocaml.org/doc/Install.html
- Instalação do Coq usando opam: https://coq.inria.fr/opam-using.html
  - Para instalação da versão 8.16.1 do Coq: `opam pin add coq 8.16.1`

Para gerar o Makefile deste projeto, basta executar o comando:

`coq_makefile -f _CoqProject Graphs/*.v -o Makefile`

Na pasta [Tentativas/](./Tentativas/) estão contidos os arquivos de teste de modelagem de grafos e implementação dos algoritmos, e a existência da pasta está mais para um registro histórico (eu sei que existe o registro de commits para isso, mas achei melhor manter a pasta). Também dentro desta pasta está o código apresentado na primeira fase do TCC, que mostrava apenas uma formalização de caminhos ponderados, sem nenhum envolvimento de grafos. Para compilar esse arquivo em específico, sugiro usar a versão 8.17 do Coq e também a versão 1.17.0 da [Mathematical Components](https://math-comp.github.io/installation.html)

O código está estruturado da seguinte forma, na pasta [Graphs](./Graphs):

- [nat_lists_extras](./Graphs/nat_lists_extras.v): Implementa algumas funções específicas para listas de números naturais que são utilizadas no trabalho;
- [graph](./Graphs/graph.v): Modela um grafo ponderado usando uma definição indutiva e define algumas notações para a utilização dos construtores;
- [graph_functions](./Graphs/graph_functions.v): Implementa funções gerais sobre nós, arestas e o peso das arestas, baseadas na modelagem de grafos;
- [graph_specs](./Graphs/graph_specs.v): Contém uma especificação de corretude em cima da modelagem de grafos e alguns teoremas (WIP) que serão provados em cima disso.
- [impl](./Graphs/impl.v): Contém a implementação dos algoritmos de DFS (que não é bem uma DFS) e Dijkstra, bem como uma função que retorna todos os caminhos de um nó A para um nó B e funções auxiliares desta última.
