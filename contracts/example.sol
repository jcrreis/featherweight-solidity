contract Bank {

    mapping(address => uint) balances;

    constructor() {
     

    }

    function fb() {

    }

    function getBalance() returns (uint){
        return this.balances[true];
    }
    
    
    
}