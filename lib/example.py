class A:
        
    def a_method(self):
        return "CALLED FROM A"


class B(A):
    def a_method(self):
        return "CALLED FROM B" 
    

class C(A):
    def a_method(self):
        return "CALLED FROM C" 
    

class D(C,B):
    pass

# print(C.__mro__)
c = D()

v = c.a_method()

print(v)