contract Arit {
    constructor () {

    }

    function fb() {

    }

    function arit() returns (uint) {
        return (2 ** 2 % 2) / 2 * 3 / 3 + 1 - 1 + true;
    }
    
    function getLiquidity() returns (uint){
        return address(this).balance;
    }
}