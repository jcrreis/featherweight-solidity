import "./NFTStorage.sol";

contract Game {

    mapping(address => NFTStorage) stores;


    constructor() {

    }

    function fb() {

    }

    function createStore() {
        NFTStorage store = new NFTStorage{value: 0}();
        this.stores = (this.stores[address(store)] = store);
    }

    function addExternalStore(address<NFTStorage> store) {
        this.stores = (this.stores[store] = NFTStorage(store));
    }
}