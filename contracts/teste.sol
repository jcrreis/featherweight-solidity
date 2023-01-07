uint xdoctor = new eoacontract.value(1000000)(); 
uint xhumandonor = new eoacontract.value(1000000)();
uint ybank = new bloodbank.value(0)(mapping, address(xdoctor),0);
uint zdonor = new donor.value(0)(5000, address(ybank));
zdonor.donate.value(0).sender(address(xhumandonor))(500)