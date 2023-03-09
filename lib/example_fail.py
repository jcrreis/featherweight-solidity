# A <- B <- C <- D <- E <- F <- G
#  ^__________________|________|

class A:
    pass

class B(A):
    pass

class C(A, B):
    pass
