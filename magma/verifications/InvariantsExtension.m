// In the case of rank 4, we check that the first invariant I2 does not depend on the choice of the square root
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


// In the rank 3 case, the invariants of the isomorphic conjugated curves are the same, up to a -1 factor (when the weight is odd). This is the case for J431 and J432. Hence the transformation (1/D*x, y, w)
// with determinant D will make all invariants belong to Q. 
R<a,c,D,a300,a210,a201,a120,a111,a102,a030,a021,a012,a003,a200,a110,a101,a020,a011,a002> := PolynomialRing(Rationals(), 19);
_<X,Y,Z,T> := PolynomialRing(FieldOfFractions(R), 4);
Q := a*X^2 -Y^2 + c*Z^2; // after renormalization
C := a300*X^3 + a210*X^2*Z + a201*X^2*T + a120*X*Z^2 + a111*X*Z*T + a102*X*T^2 + a030*Z^3 + a021*Z^2*T + a012*Z*T^2 + a003*T^3 + Y*(a200*X^2 + a110*X*Z + a101*X*T + a020*Z^2 + a011*Z*T + a002*T^2);
P0 := Matrix([[1/(2*a),0,1/(2*a*D),0],[0,1,0,0],[1/2,0,-1/(2*D),0],[0,0,0,1]]);
P1 := Matrix([[1/(2*a),0,-1/(2*a*D),0],[0,1,0,0],[1/2,0,1/(2*D),0],[0,0,0,1]]);

function ChangeOfBasis(C, P)
	R := ChangeRing(Parent(C), Parent(P[1][1]));
	C := R!C;
	P := Transpose(Matrix([[R!P[i][j] : j in [1..NumberOfColumns(P)]] : i in [1..NumberOfRows(P)]]));
	Y := ElementToSequence(P*Matrix([[R.i] : i in [1..Rank(R)]]));
	return Evaluate(C, Y);
end function;

C0 := ChangeOfBasis(C, P0);
C1 := ChangeOfBasis(C, P1);

R<s, t, w> := PolynomialRing(BaseRing(Parent(C0)), [1,1,2]);
f0 := Evaluate(C0, [s^2, s*t, t^2, w]);
f1 := Evaluate(C1, [s^2, s*t, t^2, w]);

alpha := MonomialCoefficient(f0, w^3);
f0 /:= alpha;        
f0 := Evaluate(f0, [s, t, w-ExactQuotient(Terms(f0, w)[3], 3*w^2)]);
//f0 := Evaluate(f0, [D*s, t, w]);

alpha := MonomialCoefficient(f1, w^3);
f1 /:= alpha;        
f1 := Evaluate(f1, [s, t, w-ExactQuotient(Terms(f1, w)[3], 3*w^2)]);
//f1 := Evaluate(f1, [-D*s, t, w]);

S<[x]> := PolynomialRing(BaseRing(Parent(f0)), 2);

f := S!Evaluate(f0, [x[1], x[2], 0]);
v := S!Evaluate(ExactQuotient(Terms(f0, w)[2], w), [x[1], x[2], 0]);	

k24 := Transvectant(v, v, 2);
k36 := Transvectant(v, k24, 1);

J431 := Evaluate(Transvectant(k36, f, 6), [0,0]);

f := S!Evaluate(f1, [x[1], x[2], 0]);
v := S!Evaluate(ExactQuotient(Terms(f1, w)[2], w), [x[1], x[2], 0]);	

k24 := Transvectant(v, v, 2);
k36 := Transvectant(v, k24, 1);

J432 := Evaluate(Transvectant(k36, f, 6), [0,0]);
J431+J432;