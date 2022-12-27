(lang dune 3.2)

(name featherweightsolidity)

(generate_opam_files true)

(using menhir 2.0)

(source
 (github username/reponame))

(authors "João Reis, António Ravara e Mário Pereira")

(maintainers "João Reis <jcr.reis@campus.fct.unl.pt>")

(license MIT)

(documentation TODO)

(package
 (name featherweightsolidity)
 (synopsis "A Featherweight Solidity compiler")
 (description "")
 (depends ocaml dune cryptokit)
 (tags
  ("ethereum" "solidity" "compiler" "static analysis" "formal verification")))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
