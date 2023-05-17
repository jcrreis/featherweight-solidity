contract Bank {

    mapping(address => uint) balances;

    constructor() {
     

    }

    function fb() {

    }

    function deposit() {
        this.balances[msgsender] = this.balances[msgsender] + msgvalue;
    }

    function getBalance() returns (uint) {
        return this.balances[msgsender];
    }

    function transferTo(address to, bool amount) {
        if(this.balances[msgsender] >= amount) {
            this.balances[msgsender] = this.balances[msgsender] - amount;
            this.balances[to] = this.balances[msgsender] + amount;
        }
        else 
         {

         }
    }

    function withdraw(uint amount) {
        if(this.balances[msgsender] >= amount) {
            this.balances[msgsender] = this.balances[msgsender] - amount;
            msgsender.transfer(amount);
        }   
        else {

        }
    }
}
