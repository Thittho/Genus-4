/* computation of the discriminant */
R<x,y,z,t> := PolynomialRing(Rationals(), 4);
Q := &+[Random(10)*m : m in MonomialsOfDegree(R,2)];
E := &+[Random(10)*m : m in MonomialsOfDegree(R,3)];
inv := InvariantsGenus4Curves(Q,E);
time D := DiscriminantFromInvariantsGenus4(inv);
D1 := DiscriminantGenus4(Q,E);

Factorization(D1/D);



R<x,y,z,t> := PolynomialRing(Rationals(), 4);
Q := &+[Random(10)*m : m in [x^2,x*y,x*z,y^2,y*z,z^2]];
//Q := Random(100)*(x*z-y^2);
E := &+[Random(10)*m : m in MonomialsOfDegree(R,3)];
inv := InvariantsGenus4Curves(Q,E);
time D := DiscriminantFromInvariantsGenus4(inv);
D1 := DiscriminantGenus4(Q,E);
Factorization(D1/D);

alpha := 7;
r2 := -20475/2*-126;//-219877/4*2488;
//Factorization(215);
det := 1/325;
Factorization(D1/(D*(alpha^2)^17));
Factorization(r2^3/det);



alpha := 5;
r2 := 1;
det := 1;
Factorization(D1/(D*(alpha^2)^17));
Factorization(r2^3/det);



R<x,y,z,t> := PolynomialRing(Rationals(), 4);
//Q := x*t-y*z;
//Q1 := 6*(x*t-y*z);
Q1 := &+[Random(10)*m : m in MonomialsOfDegree(R,2)];
E := &+[Random(10)*m : m in MonomialsOfDegree(R,3)];
//inv := InvariantsGenus4Curves(Q,E);
inv1 := InvariantsGenus4Curves(Q1,E);
time D := Rationals()!DiscriminantFromInvariantsGenus4(inv1);//*(&*[c : c in Coefficients(DiagonalForm(Q1))])^4;
D1 := DiscriminantGenus4(Q1,E);
Factorization(D1/D);