/* example  rank 3 */
QQ := Rationals();
P3 := ProjectiveSpace(QQ, 3);
Rtest<x,y,z,w> := CoordinateRing(P3);
Quadric1:=-10*x^2 - x*y + 8*x*z + 9*y*z - 6*z^2;
Cubic1:= 4*x^3-x^2*y - x^2*z - 5*x^2*w - 6*x*y^2 - 2*x*y*z - 9*x*y*w + 7*x*z^2 + 3*x*z*w - 8*x*w^2 - 10*y^3 + 3*y^2*z - y^2*w - 3*y*z^2 - 7*y*w^2 - z^3 + z^2*w - 10*z*w^2 + 3*w^3;
time J1 := InvariantsGenus4Curves(Quadric1, Cubic1);

Quadric2 := Evaluate(Rtest!Quadric1, [2*y+3*x, x-2*y, 3*z, -3*w]);
Cubic2 := Evaluate(Rtest!Cubic1, [2*y+3*x, x-2*y, 3*z, -3*w]);
time J2 := InvariantsGenus4Curves(Quadric2, Cubic2 : normalize := false);

// Check if they are isomorphic (they should be)
IsIsomorphicG4(Quadric1, Cubic1, Quadric2, Cubic2);

// Compute the same invariants, but we give a curve directly
C1 := Curve(P3, [Quadric1, Cubic1]);
C2 := Curve(P3, [Quadric2, Cubic2]);
IsIsomorphicG4(C1, C2);


/* Test hyperelliptic */
C<X> := PolynomialRing(Rationals());
time Wgt, I := InvariantsGenus4Curves(X^10+5*X^8-7*X+1);
