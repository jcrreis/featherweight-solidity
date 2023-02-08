contract Bank {

    uint balance;
    uint x;
    uint y; 

    constructor() {

    }

    function deposit(uint amount) {
        return this.balance;
    }

    function getBalance() {
        return this.balance;
    }

    function transferTo(address to, uint amount) {
        if(this.balance >= amount) {
            this.balance - amount;
        }
        else {
            
        };
    }

    function withdraw(uint amount) {
        if(this.balance >= amount) {
            this.balance - amount;
        } 
        else {
            
        };
    }
}
