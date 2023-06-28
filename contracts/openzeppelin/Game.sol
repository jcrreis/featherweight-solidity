import "./NFTStorage.sol";

contract Game {

    mapping(address => NFTStorage) stores;


    constructor() {

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

    function createNFT(address<NFTStorage> store) {
        NFTStorage storeInstance = this.stores[store];
        storeInstance.createNFT{value: 0}();
    }

    function buyNFT(address<NFTStorage> store) {
        NFTStorage storeInstance = this.stores[store];
        storeInstance.buyNFT{value: msgvalue}();
    }

    function transferNFT(address<NFTStorage> store, uint tokenId, address from, address to) {
        NFTStorage storeInstance = this.stores[store];
        storeInstance.transferNFT{value: 0}(tokenId, from, to);
    }

    function destroyNFT(address<NFTStorage> store, uint tokenId) {
        NFTStorage storeInstance = this.stores[store];
        storeInstance.destroyNFT{value: 0}(tokenId);
    }
}