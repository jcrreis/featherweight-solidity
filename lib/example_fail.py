# A <- B <- C <- D <- E <- F <- G
#  ^__________________|________|

class A: pass 

class B1(A): pass 

class C(A,B1): pass

