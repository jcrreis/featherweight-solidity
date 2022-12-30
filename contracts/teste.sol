xdoctor = new eoacontract.value(1000000)(); 
xhumandonor = new eoacontract.value(1000000)();
ybank = new bloodbank.value(0)(mapping, address(xdoctor),0);
zdonor = new donor.value(0)(5000, address(ybank));
ybank.setHealth.value(0).sender(address(xdoctor))(address(zdonor), true);
zdonor.donate.value(0).sender(address(xhumandonor))(500)


