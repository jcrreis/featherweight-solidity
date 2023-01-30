bool xdoctor = new EOAContract.value(1000000)(); 
bool xhumandonor = new EOAContract.value(1000000)();
bool ybank = new BloodBank.value(0)(mapping, address(xdoctor), 1000);
bool zdonor = new Donor.value(0)(1000, address(ybank));
zdonor.donate.value(0).sender(address(xhumandonor))(500)


