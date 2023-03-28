# A <- B <- C <- D <- E <- F <- G
#  ^__________________|________|

class A: pass 

class B1(A): pass 

class C(A,B1): pass

#L(A) = [A]
# L(B1) = B1 + merge(L(A) + L(A)) = [B1] + [A] = [B1, A]
# L(C) = C + merge(L(A) + L(B1) + [A,B1]) = C + ([A] + [B1, A] + [A, B1]) = 
#[C,B1,A]
# merge is joining head of list that is not in TAIL
