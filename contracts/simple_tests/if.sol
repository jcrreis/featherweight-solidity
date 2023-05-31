contract If {
    address owner;
    uint b;
    constructor () {

    }

    function fb() {
    }

    function if1() returns (bool) {
        if (msgsender == owner) {
            return true;
        }
        else {
            return false;
        }
    }

    function if2(uint amount) returns (uint){
        if ((msgsender == owner) && (amount > 0)){
            this.owner = msgsender;
            return amount;
        }
        else {
            return revert;
        }
    }
    
    
    function if3() {
        if(msgsender == owner) {
            this.b = this.b + 1;
        }
    }
    
    
}