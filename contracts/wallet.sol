contract Wallet {

    uint bal;
    address owner;

    constructor() {
        this.bal = msgvalue;
        this.owner = msgsender;
    }

    function fb() {

    }

    function onlyOwner() returns (bool){
        return msgsender == this.owner;
    }

    function deposit() {
        this.bal = this.bal + msgvalue;
    }

    function withdraw(uint amount) {
        if(this.onlyOwner()){
            msgsender.transfer(amount);
            this.bal = this.bal - amount;
        }
    }

    function getBalance() returns (uint){
        return this.bal;
    }

    function transferTo(address walletTo, uint amount) {
        if(this.onlyOwner()){
            Wallet(walletTo).deposit{value: amount}();
            this.bal = this.bal - amount;
        }
    }

}