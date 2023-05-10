contract Wallet {
    uint balance;
    address owner;

    constructor() payable {
        balance = msg.value;
        owner = msg.sender;
    }

    function onlyOwner() public view returns (bool) {
        return msg.sender == owner;
    }

    function deposit() public payable{
        balance += msg.value;
    }

    function withdraw(uint _amount) public payable {
        if(this.onlyOwner()){
            payable(msg.sender).transfer(_amount);
            balance -= _amount;
        }
    }

    function getBalance() public view returns (uint){
        return balance;
    }

    function transferTo(address _walletTo, uint _amount) public {
        if(this.onlyOwner()){
            Wallet(_walletTo).deposit{value: _amount}();
            balance -=  _amount;
        }
    }

}


