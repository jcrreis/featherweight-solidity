contract Bool {
    address owner;
    
    constructor () {

    }

    function fb() {
    }

    function bool1() returns (bool) {
        return msgsender == owner;
    }
    function bool2(uint amount) returns (uint) {
        return (2 == amount) || (3 == 5) && (5 > 4);
    }
    function bool3() returns (bool) {
        return this.bool2(2) || false;
    }
}