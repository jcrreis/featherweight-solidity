contract Bank {

    mapping(address => uint) balances;

    constructor() {

    }

    function deposit() {
        
        return 1;
    }

    function getBalance() {
        return this.balances[msg.sender];
    }

    function transfer(address to, uint amount) {
        if(this.balances[msg.sender] >= amount) {
            this.balances[msg.sender] = this.balances[msg.sender] - amount;
            this.balances[to] = this.balances[msg.sender] + amount;
        }
    }

    function withdraw(uint amount) {
        if(this.balances[msg.sender] >= amount) {
            this.balances[msg.sender] = this.balances[msg.sender] - amount;
            msg.sender.transfer(amount);
        }   
    }
}
