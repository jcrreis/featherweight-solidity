import "./NFTStorage.sol";

contract Game {

    mapping(address<NFTStorage> => NFTStorage) stores;


    constructor() {

    }

    function fb() {

    }

    function addStore() {
        NFTStorage store = new NFTStorage{value: 0}();
        this.stores = (this.stores[address(store)] = store);
    }
}