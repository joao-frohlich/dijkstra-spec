# Formalização e Prova do algoritmo de Dijkstra em Coq

A implementação foi feita utilizando a versão 8.17.0 do Coq e 1.17.0 da Mathematical Components, que são mantidas com o gerenciador de pacotes do OCaml, opam.

- Instalação do opam: https://opam.ocaml.org/doc/Install.html
- Instalação do Coq usando opam: https://coq.inria.fr/opam-using.html
  - Para instalação da versão 8.17.0: `opam pin add coq 8.17.0`
- Instalação da Mathematical components: https://math-comp.github.io/installation.html
  - Para instalação da versão 1.17.0: `opam pin add coq-mathcomp-ssreflect 1.17.0`

O código está estruturado da seguinte forma:

- CaminhoPonderado.v: implementa e formaliza o conceito de caminho ponderado em grafos
