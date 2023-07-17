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
