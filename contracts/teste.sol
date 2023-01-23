bool xdoctor = new Eoacontract.value(1000000)(); 
bool xhumandonor = new Eoacontract.value(1000000)();
bool ybank = new BloodBank.value(0)(mapping, address(xdoctor),0);
bool zdonor = new Donor.value(0)(5000, address(ybank));
zdonor.donate.value(0).sender(address(xhumandonor))(500)