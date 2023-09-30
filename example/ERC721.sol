import "./Context.sol";

contract TinyERC721 is Context {

    mapping(uint => address) owners;

    mapping(address => uint) balances;


    constructor() Context(){

    }

    function fb() {

    }

    
    function ownerOf(uint tokenId) returns (address) {
        address ownr = this.owners[tokenId];
        if (ownr == address(0)) {
           return address(0);
        }
        else {
            return ownr;
        }
    }

    function balanceOf(address owner) returns (uint) {
        if (owner == address(0)) {
            revert;
        }
        else{
           return this.balances[owner];
        }
    }

    function exists(uint tokenId) returns (bool) {
        return (this.ownerOf(tokenId) != address(0));
    }

    function transferFrom(address from, address to, uint tokenId) {
        this.balances = (this.balances[from] = this.balances[from] - 1);
        this.balances = ( this.balances[to] =  this.balances[to] + 1);
        this.owners = (this.owners[tokenId] = to);     
    }


    function mint(address to, uint tokenId) {
        if ((to == address(0)) || this.exists(tokenId)) {
            revert;
        }
        else {
            this.balances = ( this.balances[to] =  this.balances[to] + 1);
            this.owners = (this.owners[tokenId] = to);
        }

    }

 
    function burn(address own, uint tokenId) {
        this.owners = (this.owners[tokenId] = address(0));
        uint currentBal = this.balances[own];
        this.balances = (this.balances[own] = currentBal - 1);
    }

}