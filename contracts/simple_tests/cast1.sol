contract A {
    constructor () {

    }

    function fb() {

    }

    function isValid() returns (bool) {
        return true;
    }

}

contract B {
    address"A" a;

    constructor (address"A" a) {
        this.a = a;
    }

    function fb() {

    }

    function donate(uint amount) returns (bool){
        return A(this.a).isValid{value: 0}();
    }

}