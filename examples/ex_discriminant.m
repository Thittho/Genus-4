/*
 *  Genus 4 curves
 *
 *  Thomas Bouchet
 *
 *  See LICENSE.txt for license details.
*/
 
/* computation of the discriminant */
// Rank 4 case
R<x,y,z,t> := PolynomialRing(Rationals(), 4);
Q := &+[Random(10)*m : m in MonomialsOfDegree(R,2)];
E := &+[Random(10)*m : m in MonomialsOfDegree(R,3)];

if Genus(Curve(Proj(R), [Q, E])) eq 4 then
    time inv, _, const := InvariantsGenus4Curves(Q,E);
    time D := DiscriminantFromInvariantsGenus4(inv : norm := const);
    D1 := DiscriminantGenus4(Q,E);
    D eq D1;
else 
    "Curves are not smooth";
end if;

// Rank 3 case
Q := &+[Random(10)*m : m in [x^2,x*y,x*z,y^2,y*z,z^2]];
E := &+[Random(10)*m : m in MonomialsOfDegree(R,3)];
if Genus(Curve(Proj(R), [Q, E])) eq 4 then 
    inv, _, const := InvariantsGenus4Curves(Q,E);
    time D := DiscriminantFromInvariantsGenus4(inv : norm := const);
    D1 := DiscriminantGenus4(Q,E);
    D eq D1;
else 
    "Curves are not smooth";
end if;
