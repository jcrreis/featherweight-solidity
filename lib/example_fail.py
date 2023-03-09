# A -> B -> C -> D -> E -> F -> G
#  ^__________________________|

class A:
    pass

class B(A):
    pass

class C(B):
    pass

class D(C):
    pass

class E(D, A):
    pass

class F(E):
    pass

class G(A, F):
    pass