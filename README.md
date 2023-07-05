<a name="readme-top"></a>

<br />
<div align="center">

  <h3 align="center">Featherweight Solidity</h3>

  <p align="center">
    A new formalization of <a href="https://soliditylang.org/">Solidity</a> in OCaml!
  </p>
</div>



<!-- TABLE OF CONTENTS -->
<details>
  <summary>Table of Contents</summary>
  <ol>
    <li>
      <a href="#about-the-project">About The Project</a>
      <ul>
        <li><a href="#supported-features">Supported Features</a></li>
        <li><a href="#built-with">Built With</a></li>
      </ul>
    </li>
    <li>
      <a href="#getting-started">Getting Started</a>
      <ul>
        <li><a href="#prerequisites">Prerequisites</a></li>
        <li><a href="#installation">Installation</a></li>
      </ul>
    </li>
    <li><a href="#usage">Usage</a></li>
    <li><a href="#license">License</a></li>
  </ol>
</details>



<!-- ABOUT THE PROJECT -->
## About The Project

This is a proof of concept (POC) inspired on featherweight-solidity formalization by Matteo Di Pirro and Silvia Crafa.

You can read more about their formalization <a href="https://link.springer.com/chapter/10.1007/978-3-030-43725-1_11">here</a>

### Supported Features:

- [x] Multiple Inheritance
- [x] More safety type casting addresses to contracts
- [x] Operational Semantics 
- [x] Typechecker
- [x] Some tests using  <a href="https://medium.com/criteo-engineering/introduction-to-property-based-testing-f5236229d237">property based testing</a> 
<!-- - [ ] Add Additional Templates w/ Examples
- [ ] Add "components" document to easily copy & paste sections of the readme
- [ ] Multi-language Support -->

<p align="right">(<a href="#readme-top">back to top</a>)</p>



### Built With

This project was built using OCaml and Dune ecosystem!
It also relies on the following OCaml libraries:

* <a href="https://gitlab.inria.fr/fpottier/menhir">Menhir/MenhirSDK</a>
* <a href="https://github.com/xavierleroy/cryptokit">Cryptokit</a>
* <a href="https://github.com/c-cube/qcheck">QCheck</a>
  
<p align="right">(<a href="#readme-top">back to top</a>)</p>

<!-- GETTING STARTED -->
## Getting Started

### Prerequisites

* OCaml/Opam
  ```sh
  sudo apt install gcc build-essential curl bubblewrap unzip ; \
  bash -c "sh <(curl -fsSL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)" ; \
  opam init ; \
  opam switch create 4.14.0 ; \
  eval $(opam env)
  ```

* Dune 
  ```sh
   opam install dune
  ```
### Installation

_In this section you have the instructions needed to install this project depedencies on your machine_

1. Clone the repo
   ```sh
    git clone https://github.com/jcrreis/featherweight-solidity.git ; \
    cd featherweight-solidity
   ```
2. Install depedencies
   ```sh
    opam install ./ --deps-only --with-test ; \
    opam install menhir qcheck-alcotest ppx_deriving_qcheck qcheck ppxlib ; \ 
    eval $(opam env)
   ```

<p align="right">(<a href="#readme-top">back to top</a>)</p>


<!-- USAGE EXAMPLES -->
## Usage

* Running tests
  ```sh
    dune runtest
   ```

* Compiling
  ```sh
    dune build @all
   ```

<p align="right">(<a href="#readme-top">back to top</a>)</p>


<!-- LICENSE -->
## License

Distributed under the MIT License. See `LICENSE` for more information.

<p align="right">(<a href="#readme-top">back to top</a>)</p>



# featherweight-solidity

* dune build @install --profile release
* dune install

https://github.com/OpenZeppelin/openzeppelin-contracts/blob/master/contracts/token/ERC20/ERC20.sol

https://www.researchgate.net/publication/228386147_Testing_Formal_Semantics_with_QuickCheck 

https://www.fc.up.pt/dcc/Pubs/TReports/TR13/dcc-2013-06.pdf 

Pontos a ver:

- Parser agora incorpora novas features, anotação em funções, address< type >, imports, inicializacao de construtores 
com super contratos 

- main agora tem opção de correr com bank_example ou wallet_example e mostrar estes contratos a serem executados com semântica operacional 

- muitos exemplos adicinados na pasta contracts/simple_tests, script run.py facilita a validação que todos os testes passam !

TODO: PLANO ATUALIZADO

- JULHO -> escrever dissertação / artigo ? 
- Agosto -> continuar anterior
- Setembro -> acabar a escrita com revisão dos professores e submeter


notas:

- o nosso gamma agora é um quadruplo, introduzi um gamma para as state vars apenas (pois existe colisão com as vars) (a abordagem teorica usual seria considerar o conjunto dos identificadores todos disjuntos, mas para facilitar o programador na escrita do código optei por separar em ambientes de tipificacao disjuntos)
- falar dos exemplos em openzeppelin
- melhor maneira de testar a implementação da semântica operacional e da expressão CallTopSender do typechecker é através de RPC, fazendo um mock da ethereum e manipulando esta rede através de invocações de New e CallTopSender
- As regras do De Pirro de typechecking, são regras de inferencia de tipos e não typechecking?
- c++ uses virtual inheritance: https://stackoverflow.com/questions/110157/how-do-i-implement-a-lookup-table-in-c

- ver se argumentos passados no super constructor tem o tipo esperado
- https://github.com/MPRI/M2-4-2/blob/master/Types%20and%20Programming%20Languages.pdf (caps 15, 16)
- realçar que era interessante gastar tempo a arranjar/procurar vulnerabilidades que sejam detetadas pela nossa ferramenta