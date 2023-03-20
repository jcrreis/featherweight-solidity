# featherweight-solidity

* dune build @install --profile release
* dune install


https://www.researchgate.net/publication/228386147_Testing_Formal_Semantics_with_QuickCheck 

https://www.fc.up.pt/dcc/Pubs/TReports/TR13/dcc-2013-06.pdf 

Pontos feitos:

- Construtores (New) Feito e validado com sucesso
- Contrato bank com dois subcontratos banks validados 
 - pontos importantes feitos/melhorados:
    - Executar fallback function quando se recebe ether > 0 em CallTopLevel e Call 
    - Nos mapas quando o valor é alterado para o default value remover da tabela
    - Por default todas as funções/ variáveis de estado são passíveis de ser overrided pelo contrato pai 
    - Funcionalidades testadas: NEW, SEQ, StateAssign, StateRead, CallTopLevel, Transfer, MsgSender, MsgValue
    - Por testar: Let, Assign, Call, Cons, this.f, Balance(a), Address(c), Revert and Return 


TODO: PLANO DISSERTAÇÃO ATÉ JULHO

- Até final do mês de março, acabar implementação de FS (typechecker e semantica), + 1 semana de abril para melhorias
    - acabar semantica operacional: - ver "this.f" "this.s" e testar operacoes como transfer call calltoplevel (exemplos)
    - acabar typechecker: como fazer avaliação de expressões que podem tomar muitos valores e não sabemos a partida (por exmeplo o Cast, que pode ser Donor(msg.sender), Donor(0x00000), Donor(this.donor) etc...
    - acabar parser/menhir: msg.sender/msg.value, erros a dar parser de maps "this.balances[msg.sender]", possivelmente outros
- 2 semanas de abril para voltar a testes, escrever dois ou três teste para typechecker e semantica
- ultima semana de abril + maio -> começar a escrever dissetação // ler artigos em detalhe relevantes // eventualmente encontrar novas ideias ? 
- junho/julho/agosto -> continuar escrita de dissertação...
- Setembro -> preparar entrega 