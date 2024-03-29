import "./Ownable.sol";
import "./ERC721.sol";

contract MaliciousNFTStorage is Ownable, TinyERC721 {
    uint lastUnsoldToken;
    uint lastTokenId;
    uint price;

    constructor() Ownable(msgsender) TinyERC721() {}

    function fb() {}

    function setNFTPrice(uint val) {
        this.onlyOwner();
        this.price = val;
    }

    function createNFT() {
        this.onlyOwner();
        this.mint(address(0), this.lastTokenId);
        this.lastTokenId = this.lastTokenId + 1;
    }

    function buyNFT(address from, address to, uint tokenId) {
        if (msgvalue >= this.price) {
            this.transferFrom(address(0), msgsender, this.lastUnsoldToken);
        } else {
            revert;
        }
    }

    function transferNFT(uint tokenId, address from, address to) {
        this.onlyOwner();
        this.transferFrom(from, to, tokenId);
    }

    function destroyNFT(uint tokenId) {
        this.onlyOwner();
        this.burn(tokenId);
    }
}
