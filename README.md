# featherweight-solidity

* dune build @install --profile release
* dune install

https://github.com/OpenZeppelin/openzeppelin-contracts/blob/master/contracts/token/ERC20/ERC20.sol

https://www.researchgate.net/publication/228386147_Testing_Formal_Semantics_with_QuickCheck 

https://www.fc.up.pt/dcc/Pubs/TReports/TR13/dcc-2013-06.pdf 

Pontos feitos:

- Construtores (New) Feito e validado com sucesso
- Contrato bank com dois subcontratos banks validados
- Contrato Wallet testado e validado com sucesso 
 - pontos importantes feitos/melhorados:
    - Executar fallback function quando se recebe ether > 0 em CallTopLevel e Call 
    - Nos mapas quando o valor é alterado para o default value remover da tabela
    - Por default todas as funções/ variáveis de estado são passíveis de ser overrided pelo contrato pai 
    - Funcionalidades testadas: NEW, SEQ, StateAssign, StateRead, CallTopLevel, Transfer, MsgSender, MsgValue, Balance(a), Call, Const, this.f, Address(C), Revert, If
    - Por testar: Let, Assign  


TODO: PLANO DISSERTAÇÃO ATÉ JULHO

- Até final do mês de março, acabar implementação de FS (typechecker e semantica), + 1 semana de abril para melhorias
    - acabar semantica operacional: - ver "this.f" "this.s" e testar operacoes como transfer call calltoplevel (exemplos) - FEITO
    - acabar typechecker: como fazer avaliação de expressões que podem tomar muitos valores e não sabemos a partida (por exmeplo o Cast, que pode ser Donor(msg.sender), Donor(0x00000), Donor(this.donor) etc...
    - acabar parser/menhir: msg.sender/msg.value, erros a dar parser de maps "this.balances[msgvalue]", possivelmente outros
- 2 semanas de abril para voltar a testes, escrever dois ou três teste para typechecker e semantica
- ultima semana de abril + maio -> escrever artiga // começar a escrever dissetação // ler artigos em detalhe relevantes // eventualmente encontrar novas ideias ? 
- junho/julho/agosto -> continuar escrita de dissertação...
- Setembro -> preparar entrega 

Bidirectional typechecking -- ver até sexta


notas:

- c++ uses virtual inheritance: https://stackoverflow.com/questions/110157/how-do-i-implement-a-lookup-table-in-c

sendo trabalhador-estudante só tenho conseguido dedicar 25% do tempo quando na elaboração se espera que seja a 100%, contudo tenho avançado de forma positiva na elaboração,conseguido cumprir os objetivos que têm sido estabelecidos dentro dos prazos combinados e temos programado que seja concluido no final deste semestre.

1 - Seguir as regras, 
