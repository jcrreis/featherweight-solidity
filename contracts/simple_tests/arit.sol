contract Arit {
    constructor () {

    }

    function fb() {

    }

    function arit() returns (uint) {
        return (1 ** 2 % 2) / 2 * 3 / 3 + 1 - 1;
    }
    
    function getLiquidity() returns (uint){
        return address(this).balance;
    }
}