contract Donor {
    uint blood;
    address"BloodBank" bank;

    constructor (uint blood, address bank) {
        this.blood = blood;
        this.bank = bank;
    }

    function fb() {

    }

    function donate(uint amount) {
        bool cond = BloodBank(this.bank).donate(amount);
        if(cond){
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