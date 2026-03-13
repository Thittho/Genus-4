/*
 *  Genus 4 curves
 *
 *  Thomas Bouchet
 *
 *  See LICENSE.txt for license details.
*/

SetVerbose("Genus4", 1);

K := GF(11);
R<x,y,z,w> := PolynomialRing(K, 4);


// Rank 3 example
l0 := &+[Random(-5,5)*m : m in MonomialsOfDegree(R, 1)];
M := 3*ChangeRing(RandomSLnZ(4, 10, 10), K);

Q := &+[&+[Random(-2,2)*R.i : i in [1..4]]^2 : j in [1..3]];
E := &+[Random(-2,2)*m : m in MonomialsOfDegree(R, 3)]+3*w^3;

Q1 := 2*Q^M;
E1 := 3*(E+l0*Q)^M;

if Genus(Curve(Proj(R), [Q, E])) eq 4 then
    C := Curve(Proj(R), [Q, E]);
    C1 := Curve(Proj(R), [E1, Q1]);
    IsIsomorphicGenus4(C, C1);
else 
    "The curves are not smooth";
end if;


// Rank 4 example
l0 := &+[Random(-5,5)*m : m in MonomialsOfDegree(R, 1)];
M := 3*ChangeRing(RandomSLnZ(4, 10, 10), K);

Q := &+[&+[Random(-2,2)*R.i : i in [1..4]]^2 : j in [1..4]];
E := &+[Random(-2,2)*m : m in MonomialsOfDegree(R, 3)]+3*w^3;

Q1 := 2*Q^M;
E1 := 3*(E+l0*Q)^M;

if Genus(Curve(Proj(R), [Q, E])) eq 4 then
    C := Curve(Proj(R), [Q, E]);
    C1 := Curve(Proj(R), [E1, Q1]);
    IsIsomorphicGenus4(C, C1);
else 
    "The curves are not smooth";
end if;
