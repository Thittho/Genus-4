K := Rationals();
R0<x,y,u,v> := PolynomialRing(K, 4);
f0 := 0;
for i in [0..3] do
	for j in [0..3] do
		f0 := f0 + Random(-10, 10)*x^i*y^(3-i)*u^j*v^(3-j);
	end for;
end for;
a1 := Random(1,10);
b1 := Random(-10,10);
c1 := Random(-10,10);
d1 := (1-b1*c1)/a1;
a2 := Random(1,10);
b2 := Random(-10,10);
c2 := Random(-10,10);
d2 := (1-b2*c2)/a2;
f1 := Evaluate(f0, [a1*x+b1*y, c1*x+d1*y, a2*u+b2*v, c2*u+d2*v]);
f0;
f1;
I1 := eval_inv(list_invariants, f0);
I2 := eval_inv(list_invariants, f1);


//same invariants !
J1, J2 := same_wps(list_invariants, I1, I2);
for i in [1..#J1] do
	if J1[i]-J2[i] ne 0 then
		i, J1[i], J2[i];
	end if;
end for;

/* Test */
QQ := Rationals();
Rtest<x,y,z,w> := PolynomialRing(QQ, [1,1,1,1]);
Quadric1:=-10*x^2 - x*y + 8*x*z + 9*y*z - 6*z^2;
Cubic1:=-x^2*y - x^2*z - 5*x^2*w - 6*x*y^2 - 2*x*y*z - 9*x*y*w + 7*x*z^2 + 3*x*z*w -
    8*x*w^2 - 10*y^3 + 3*y^2*z - y^2*w - 3*y*z^2 - 7*y*w^2 - z^3 + z^2*w -
    10*z*w^2 + 3*w^3;
time I1 := InvariantsGenus4Curves(Quadric1, Cubic1);

Quadric2 := Evaluate(Quadric1, [2*y+3*x, x-2*y, 3*z, -3*w]);
Cubic2 := Evaluate(Cubic1, [2*y+3*x, x-2*y, 3*z, -3*w]);
time I2 := InvariantsGenus4Curves(Quadric2, Cubic2);
I2 eq I1;





C<X> := PolynomialRing(Rationals());   
time InvariantsGenus4HyperellipticCurves(X^10+5*X^8-7X+1);
