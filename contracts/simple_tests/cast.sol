contract Aux {
    constructor () {

    }

    function fb() {
    }
}

contract Cast is Aux {
    
    constructor () {

    }

    function fb() {
    }
    
    
    

    function cast() returns (address) {
        Aux c = Aux(this);
        return address(c);
    }

    function cast1() returns (Aux) {
        Aux c = Aux(this);
        return c;
    }

    function cast2() returns (Cast) {
        Cast c = Cast(this);
        return c;
    }

    function cast3(address"Cast" a) returns (Aux) {
        Aux c = Aux(a);
        return c;
    }

    
}