contract BloodBank{

    mapping(address => bool) healty;
    address doctor;
    uint blood;

    constructor (address doctor, uint blood) {
        this.doctor = doctor;
        this.blood = blood;
    }

    function fb() {

    }

    function setHealth(address donor, bool isHealty) {
        if (msgsender == this.doctor) {
            this.healty = (this.healty[donor] = isHealty);
        }
        else {
            return revert;
        }       
    }
    
    function isHealty(address donor) returns (bool) {
        if(msgsender == this.doctor) {
            return this.healty[donor];
        }
        else {
            return revert;
        }
    }

    function donate(uint amount) {
        uint donorBlood = Donor(msgsender).getBlood();
        if (this.healty[msgsender] && (donorBlood > 3000) && (donorBlood - amount > 0)){
            this.blood = this.blood + amount;
        }
        else {
            revert;
        }         
    }
    

    function getDoctor() returns (address) {
        return this.doctor;
    }
    function getBlood() returns (uint) {
        return this.blood;
    }

}   