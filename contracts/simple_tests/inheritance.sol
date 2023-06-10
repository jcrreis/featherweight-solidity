
contract C {
    constructor () {

    }

    function fb() {
    }

}
contract A {
   constructor () {

    }

    function fb() {
    }

}
contract B is A,C{
    constructor () {

    }

    function fb() {
    }
}

contract EOAContract is B {
    constructor () {

    }

    function fb() {
    }


}