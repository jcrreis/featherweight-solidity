contract Donor {
    uint blood;
    address"BloodBank" bank;

    constructor (uint blood, address"BloodBank" bank) {
        this.blood = blood;
        this.bank = bank;
    }

    function fb() {

    }

    function donate(uint amount) {
        if(BloodBank(this.bank).donate{value: 0}(amount)){
            this.blood = this.blood - amount;
        }
        
    }

    function getBank() returns (address) {
        return this.bank;
    }

    function getBlood() returns (uint) {
        return this.blood;
    }
}