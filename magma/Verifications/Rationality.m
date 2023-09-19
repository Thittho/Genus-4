// Checks that the first invariant I2 does not depend on the choice of the square root
R<a3000,a2100,a2010,a2001,a1200,a1110,a1101,a1020,a1011,a1002,a0300,a0210,a0201,a0120,a0111,a0102,a0030,a0021,a0012,a0003,A,B,D1,D2> := PolynomialRing(Rationals(), 24);
S<X,Y,Z,T> := PolynomialRing(FieldOfFractions(R), 4);
C := a3000*X^3+a2100*X^2*Y+a2010*X^2*Z+a2001*X^2*T+a1200*X*Y^2+a1110*X*Y*Z+a1101*X*Y*T+a1020*X*Z^2+a1011*X*Z*T+a1002*X*T^2+a0300*Y^3+a0210*Y^2*Z+a0201*Y^2*T+a0120*Y*Z^2+a0111*Y*Z*T+a0102*Y*T^2+a0030*Z^3+a0021*Z^2*T+a0012*Z*T^2+a0003*T^3;
Q := A*X^2-A*D1^2*T^2+B*Y^2-B*D2^2*Z^2;

F0 := Evaluate(C, [1/(2*A)*X+1/2*T, -1/(2*B)*Y+1/2*Z, -1/(2*B*D2)*Y-1/(2*D2)*Z, 1/(2*A*D1)*X-1/(2*D1)*T]);
F1 := Evaluate(C, [1/(2*A)*X+1/2*T, -1/(2*B)*Y+1/2*Z, 1/(2*B*D2)*Y+1/(2*D2)*Z, 1/(2*A*D1)*X-1/(2*D1)*T]); 
F2 := Evaluate(C, [1/(2*A)*X+1/2*T, -1/(2*B)*Y+1/2*Z, -1/(2*B*D2)*Y-1/(2*D2)*Z, -1/(2*A*D1)*X+1/(2*D1)*T]);
F3 := Evaluate(C, [1/(2*A)*X+1/2*T, -1/(2*B)*Y+1/2*Z, 1/(2*B*D2)*Y+1/(2*D2)*Z, -1/(2*A*D1)*X+1/(2*D1)*T]); 

_<x,y,u,v> := PolynomialRing(FieldOfFractions(R), 4);
f0 := Evaluate(F0, [x*u, x*v, y*u, y*v]);
f1 := Evaluate(F1, [x*u, x*v, y*u, y*v]);
f2 := Evaluate(F2, [x*u, x*v, y*u, y*v]);
f3 := Evaluate(F3, [x*u, x*v, y*u, y*v]);

s0 := Transvectant(f0, f0, 3, 3 : invariant := true);
s1 := Transvectant(f1, f1, 3, 3 : invariant := true);
s2 := Transvectant(f2, f2, 3, 3 : invariant := true);
s3 := Transvectant(f3, f3, 3, 3 : invariant := true);

s0 eq s1; s0 eq s2; s0 eq s3;