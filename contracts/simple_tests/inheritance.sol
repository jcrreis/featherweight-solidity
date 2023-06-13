
contract C {
    uint counter;

    constructor (uint init) {
        this.counter = init;
    }

    function fb() {
    }

}
contract A {
    address owner;
   constructor (address owner) {
    this.owner = owner;
    }

    function fb() {
    }

}
contract B is A,C{
    constructor () A(msgsender) C(10){

    }

    function fb() {
    }
}

contract EOAContract is B {
    constructor () B(){

    }

    function fb() {
    }


}