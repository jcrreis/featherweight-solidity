contract Bank {

    mapping(address => uint) balances;

    constructor() {
     

    }

    function fb() {

    }

    function deposit() {
        this.balances = (this.balances[msgsender] = this.balances[msgsender] + msgvalue);
    }
    
    

    function transferTo(address to, uint amount) {
        if(this.balances[msgsender] >= amount) {
            this.balances = (this.balances[msgsender] = this.balances[msgsender] - amount);
            this.balances = (this.balances[to] = this.balances[msgsender] + amount);
        }
    }

    function withdraw(uint amount) {
        if(this.balances[msgsender] >= amount) {
            this.balances = (this.balances[msgsender] = this.balances[msgsender] - amount);
            msgsender.transfer(amount);

        }   
    }

    
    function getLiquidity() returns (uint){
        return address(this).balance;
    }

    function getBalance() returns (uint) {
        return this.balances[msgsender];
    }
    
    
}