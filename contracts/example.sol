contract Bank {

mapping(address => uint) balances;

    constructor() {
     

    }

    function fb() {

    }

    function deposit() {
       this.balances = (this.balances[msgsender] = this.balances[msgsender] + msgvalue);
    }
    
    
    
}