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
        BloodBank b = BloodBank(this.bank);
        bool cond = b.donate(amount);
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