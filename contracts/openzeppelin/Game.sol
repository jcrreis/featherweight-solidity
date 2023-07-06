import "./NFTStorage.sol";

contract Game is Context{

    mapping(address => NFTStorage) stores;


    constructor() Context(){

    }

    function fb() {

    }

    function createStore() returns (address) {
        NFTStorage store = new NFTStorage{value: 0}();
        this.stores = (this.stores[address(store)] = store);
        return address(store);
    }

    function addExternalStore(address<NFTStorage> store) {
        this.stores = (this.stores[store] = NFTStorage(store));
    }


    function setNFTPrice(address<NFTStorage> store, uint price) {
        NFTStorage storeInstance = this.stores[store];
        storeInstance.setNFTPrice{value: 0}(price);
    }

    function createNFT(address<NFTStorage> store, address to) {
        NFTStorage storeInstance = this.stores[store];
        storeInstance.createNFT{value: 0}(to);
    }

    function buyNFT(address<NFTStorage> store) {
        NFTStorage storeInstance = this.stores[store];
        storeInstance.buyNFT{value: msgvalue}();
    }

    function transferNFT(address<NFTStorage> store, uint tokenId, address from, address to) {
        address snder = this.msgSender();
        NFTStorage storeInstance = this.stores[store];
        storeInstance.transferNFT{value: 0}(tokenId, snder, to);
    }

    function destroyNFT(address<NFTStorage> store, uint tokenId) {
        address snder = this.msgSender();
        NFTStorage storeInstance = this.stores[store];
        storeInstance.destroyNFT{value: 0}(snder, tokenId);
    }

}