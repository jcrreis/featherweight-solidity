contract Example {
        mapping(address => uint) balances;


    constructor () {
        
    }

    function fb () {

    }
    function teste (uint amount) returns (uint){
       if(balances[msgsender] && amount) {
           return amount;
       }
       else {
           return 0;
       }
      
    }
}