contract Aux {
    constructor () {

    }

    function fb() {
    }
}

contract Cast {
    
    constructor () {

    }

    function fb() {
    }
    
    
    

    function cast() returns (address) {
        Aux c = Aux(this);
        return address(c);
    }

    
}