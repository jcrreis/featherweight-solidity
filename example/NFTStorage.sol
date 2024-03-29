import "./Ownable.sol";
import "./ERC721.sol";

contract NFTStorage is Ownable, TinyERC721 {
    
    uint lastUnsoldToken;
    uint lastTokenId; 
    uint price;
    
    constructor() Ownable(msgsender) TinyERC721()  {

    }

    function fb() {

    }

    function setNFTPrice(uint val) {
        this.onlyOwner();
        this.price = val;
    }

    function createNFT(address to) {
        this.onlyOwner();
        this.mint(to, this.lastTokenId);
        this.lastTokenId = this.lastTokenId + 1;
    }

    function buyNFT(address buyer) {
        if(msgvalue >= this.price) {
            this.transferFrom(address(0), buyer, this.lastUnsoldToken);
        }
        else {
            revert;
        }
    }

    function transferNFT(uint tokenId, address from, address to) {
        if(from == this.ownerOf(tokenId)) {
            this.transferFrom(from, to, tokenId);
        }
        else {
            revert;
        }
    }


    function destroyNFT(address owner, uint tokenId) {
        if(owner == this.ownerOf(tokenId)) {
            this.burn(owner, tokenId);
        }
        else {
            revert;
        }
    }

}