// SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;
contract S {
    address public c;
    constructor(address x) payable {
        c = x;
    }


}
contract B is S{
    uint public counter;
    uint public b;
    constructor(uint x) payable S(0x5B38Da6a701c568545dCfcB03FcB875f56beddC4){
        counter = x;
        b = x;
    }

    function getCounter() public view returns (uint){
       // this.teste2 = address(this);
        return counter;
    }
}

contract A is B {
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