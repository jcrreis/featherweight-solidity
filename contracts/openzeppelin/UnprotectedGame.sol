import "./Ownable.sol";
import "./ERC721.sol";

contract MaliciousGame is Ownable, TinyERC721 {
    
    uint lastTokenId; 
    
    constructor() Ownable(msgsender) TinyERC721()  {

    }

    function fb() {

    }

    function createNFT() {
        if(this.onlyOwner()) {
            this.mint(address(0), this.lastTokenId);
            this.lastTokenId = this.lastTokenId + 1;
        }
        else {
            revert;
        }
    }

    function transferNFT(uint tokenId, address from, address to) {
        if(this.onlyOwner()) {
            this.transferFrom(from, to, tokenId);
        }
        else {
            revert;
        }
    }

    function destroyNFT(uint tokenId) {
        if(this.onlyOwner()) {
            this.burn(tokenId);
        }
        else {
            revert;
        }
    }

}