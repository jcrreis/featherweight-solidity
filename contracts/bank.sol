contract Bank {

    mapping(address => uint) balances;

    constructor() {
     

    }

<<<<<<< HEAD
    function deposit() {
        this.balances[msgsender];
=======
    function deposit(uint amount) {
        this.balances[msgsender] = amount;
>>>>>>> ee9b25c69b9fd8faeafb9988532af3a421b33acd
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
