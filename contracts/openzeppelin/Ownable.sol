import "./Context.sol";

contract Ownable is Context {
    address owner;


    constructor(address initialOwner) Context() {
        this.owner = initialOwner;
    }

    function fb() {

    }
    
    function checkOwner() {
        if (this.owner != this.msgSender()) {
            revert;
        }
    }

    function onlyOwner() {
        this.checkOwner();
    }


    function renounceOwnership() {
        this.onlyOwner();
        this.transferOwnership(address(0));
    }


    function transferOwnership(address newOwner) {
        this.checkOwner();
        if (newOwner == address(0)) {
            revert;
        }
        else {
            this.transferOwnership(newOwner);

        }
    }

}