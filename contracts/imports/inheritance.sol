// SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;
contract C {
    constructor(address x) payable {
    }

}
contract A {
    address public c;
    constructor(address x) payable {
        c = x;
    }

    fallback() external {

    }

}
contract B is A,C{
    uint public counter;
    uint public b;
    constructor(uint x) payable C(0x5B38Da6a701c568545dCfcB03FcB875f56beddC4) A(0x5B38Da6a701c568545dCfcB03FcB875f56beddC4){
        counter = x;
        b = x;
    }
    

    function getCounter() public view returns (uint){
       // this.teste2 = address(this);
        return counter;
    }
}

contract EOAContract is B {
    uint public a;

    constructor(uint x) payable B(2) {
        counter = x;
        a = 5;
    }

    function getB() public view returns (uint){
       // this.teste2 = address(this);
        return b;
    }


}
