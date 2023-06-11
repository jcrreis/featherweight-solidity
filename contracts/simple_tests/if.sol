contract If {
    address owner;
    uint b;
    constructor () {

    }

    function fb() {
    }

    function if1() returns (bool) {
        if (msgsender == this.owner) {
            return true;
        }
        else {
            return false;
        }
    }

    function if2(uint amount) returns (uint){
        if ((msgsender == this.owner) && (amount > 0)){
            this.owner = msgsender;
            return amount;
        }
        else {
            return revert;
        }
    }
    
    
    function if3() {
        if(msgsender == this.owner) {
            this.b = this.b + 1;
        }
    }
    
    
}