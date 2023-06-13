<!-- Improved compatibility of back to top link: See: https://github.com/jcrreis/featherweight-solidity/pull/73 -->
<a name="readme-top"></a>
<!--
*** Thanks for checking out the Best-README-Template. If you have a suggestion
*** that would make this better, please fork the repo and create a pull request
*** or simply open an issue with the tag "enhancement".
*** Don't forget to give the project a star!
*** Thanks again! Now go create something AMAZING! :D
-->



<!-- PROJECT SHIELDS -->
<!--
*** I'm using markdown "reference style" links for readability.
*** Reference links are enclosed in brackets [ ] instead of parentheses ( ).
*** See the bottom of this document for the declaration of the reference variables
*** for contributors-url, forks-url, etc. This is an optional, concise syntax you may use.
*** https://www.markdownguide.org/basic-syntax/#reference-style-links
-->
<!-- [![Contributors][contributors-shield]][contributors-url]
[![Forks][forks-shield]][forks-url]
[![Stargazers][stars-shield]][stars-url]
[![Issues][issues-shield]][issues-url]
[![MIT License][license-shield]][license-url] -->


<!-- PROJECT LOGO -->
<br />
<div align="center">

  <h3 align="center">Featherweight Solidity</h3>

  <p align="center">
    A new formalization of <a href="https://soliditylang.org/">Solidity</a> in OCaml!
    <!-- <br />
    <a href="https://github.com/jcrreis/featherweight-solidity"><strong>Explore the docs »</strong></a>
    <br />
    <br />
    <a href="https://github.com/jcrreis/featherweight-solidity">View Demo</a>
    ·
    <a href="https://github.com/jcrreis/featherweight-solidity/issues">Report Bug</a>
    ·
    <a href="https://github.com/jcrreis/featherweight-solidity/issues">Request Feature</a> -->
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

This project was built using ocaml and dune ecosystem!
It relies on the following OCaml libraries:

* <a href="https://gitlab.inria.fr/fpottier/menhir">Menhir/MenhirSDK</a>
* <a href="https://github.com/xavierleroy/cryptokit">Cryptokit</a>
* <a href="https://github.com/c-cube/qcheck">QCheck</a>
  
<p align="right">(<a href="#readme-top">back to top</a>)</p>

<!-- GETTING STARTED -->
## Getting Started

### Prerequisites

* OCaml/Opam
  ```sh
  $ bash -c "sh <(curl -fsSL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)"
  $ opam init
  $ opam switch create 4.14.0
  $ eval $(opam env)
  ```

* Dune 
  ```sh
  $ opam install dune
  ```
### Installation

_In this section you have the instructions needed to install this project depedencies on your machine_

1. Clone the repo
   ```sh
    git clone https://github.com/jcrreis/featherweight-solidity.git
    cd featherweight-solidity
   ```
2. Install depedencies
   ```sh
    opam install ./ --deps-only --with-test
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

Pontos a rever:


TODO: PLANO DISSERTAÇÃO ATÉ JULHO


- ultima semana de abril + maio -> escrever artiga // começar a escrever dissetação // ler artigos em detalhe relevantes // eventualmente encontrar novas ideias ? 
- junho/julho/agosto -> continuar escrita de dissertação...
- Setembro -> preparar entrega 



notas:

- c++ uses virtual inheritance: https://stackoverflow.com/questions/110157/how-do-i-implement-a-lookup-table-in-c

