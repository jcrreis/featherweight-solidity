contract Bool {
    address owner;
    
    constructor () {

    }

    function fb() {
    }

    function bool1() returns (bool) {
        return msgsender == owner;
    }
    function bool2() returns (bool) {
        return (2 == 3) || (3 == 5) && (5 > 4);
    }
    function bool3() returns (bool) {
        return this.bool2() || false;
    }
}