contract Bank {

    uint balance;

    constructor() {

    }

    function deposit(uint amount) {
        this.balance = this.balance + amount
    }

    function getBalance() {
        return this.balance;
    }

    function transfer(address to, uint amount) {
        if(this.balance >= amount) {
            this.balance = this.balance - amount;
        }
    }

    function withdraw(uint amount) {
        if(this.balance >= amount) {
            this.balance = this.balance - amount;
            msg.sender.transfer(amount);
        }   
    }
}
