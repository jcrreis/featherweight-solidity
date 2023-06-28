import "./Context.sol";

contract TinyERC721 is Context {

    mapping(uint => address) owners;

    mapping(address => uint) balances;


    constructor() Context(){

    }

    function fb() {

    }

    
    function ownerOf(uint tokenId) returns (address) {
        address owner = this.owners[tokenId];
        return owner;
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
        address owner = this.ownerOf(tokenId);
        if ((owner != from) || (to == address(0)) ) {
            revert ;
        }
        else {
        this.balances = (this.balances[from] = this.balances[from] - 1);

        this.balances = ( this.balances[to] =  this.balances[to] + 1);

        this.owners = (this.owners[tokenId] = to);
        }

       
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

 
    function burn(uint tokenId) {
        address owner = this.ownerOf(tokenId);
        this.balances = (this.balances[owner] = this.balances[owner] - 1);
    }


}