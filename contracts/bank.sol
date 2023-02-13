contract Bank {

    mapping(address => uint) balances;

    constructor() {
        
    }

    function deposit(uint amount) {
        this.balances[msgsender] = amount;
    }

    function getBalance() {
        return this.balances[msgsender];
    }

    function transferTo(address to, uint amount) {
        if(this.balances[msgsender] >= amount) {
            this.balances[msgsender] = this.balances[msgsender] - amount;
            this.balances[to] = this.balances[msgsender] + amount;
        }
    }

    function withdraw(uint amount) {
        if(this.balances[msgsender] >= amount) {
            this.balances[msgsender] = this.balances[msgsender] - amount;
            msgsender.transfer(amount);
        }   
    }
}
