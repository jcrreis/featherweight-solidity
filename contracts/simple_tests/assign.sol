contract Assign {
    
    constructor () {

    }

    function fb() {
    }

    function assign1() returns (bool) {
        bool x = 2 > 3;
        x = x || true;
        return x;
    }
    

    function assign2() returns (uint) {
        uint x = 3;
        x = x * 5;
        return x;
    }
    function assign3() {
        bool x = true;
    }
    
}