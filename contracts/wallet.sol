contract Wallet {
    uint balance;
    address owner;

    constructor() {
        this.balance = msgvalue;
        this.owner = msgsender;
    }

    function onlyOwner() returns (bool){
        return msgsender == this.owner;
    }

    function deposit() {
        this.balance = this.balance + msgvalue;
    }

    function withdraw(uint amount) {
        if(this.onlyOwner()){
            msgsender.transfer(amount);
            this.balance = this.balance - amount;
        }
    }

    function getBalance() returns (uint){
        return this.balance;
    }

    function transferTo(address walletTo, uint amount) {
        if(this.onlyOwner()){
            Wallet(walletTo).deposit{value: amount}();
           this.balance = this.balance - amount;
        }
    }

}