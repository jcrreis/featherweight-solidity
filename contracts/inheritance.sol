contract C {
    constructor(uint x)  {
    }

    function fb() {

    }

}
contract A {
    uint c;
    constructor(uint x)  {
        this.c = x;
    }

    function fb() {

    }

}

contract B is A,C{
    uint counter;
    uint b;
    constructor(uint x) A(msgsender) C(msgsender){
        this.counter = x;
        this.b = x;
    }


    function fb() {

    }
    
    function getCounter() returns (uint){
        return this.counter;
    }
}
