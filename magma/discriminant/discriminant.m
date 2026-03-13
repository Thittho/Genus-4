/*
 *  Genus 4 curves
 *
 *  Thomas Bouchet
 *
 *  See LICENSE.txt for license details.
*/

import "decomposition_disc_rk4.m" : DiscriminantRk4;
import "decomposition_disc_rk3.m" : DiscriminantRk3;

intrinsic DiscriminantFromInvariantsGenus4(I::SeqEnum : norm := 1) -> RngInt
	{Given a list of invariants of a non-hyperelliptic genus 4 curve, return its discriminant. If norm is set to be the third output of InvariantsGenus4Curves, the value returned is the exact one (not up to a constant).}
	if #I eq 60 then 
		return DiscriminantRk3(I)/norm;
	elif #I eq 65 then
		return DiscriminantRk4(I)/norm;
	elif #I eq 106 then	
		error("Not coded for hyperelliptic curves of genus 4.");
	end if;
	error("The size of invariants does not match that of a curve of genus 4.");
end intrinsic;

/*
Developed with the help and software of Laurent Bus\'e (https://www-sop.inria.fr/members/Laurent.Buse/index.html)
*/

import "../tools.m" : Jaco, MacaulayResultant, DiscriminantTernary;

intrinsic DiscriminantGenus4(Q::RngMPolElt, E::RngMPolElt) -> RngInt
    {Given a quadratic form Q and a cubic form E in 4 variables (over a field of char > 5), return the discriminant of the curve given by the complete intersection of the vanishing locus of Q and E.}
    
    require (Parent(Q) eq Parent(E)): "Q and E must have the same parent";
	require (Rank(Parent(Q)) eq 4): "Q and E must be polynomials in 4 variables";
	require IsHomogeneous(Q) and IsHomogeneous(E): "Q and E must be homogeneous";
	require (Degree(Q) eq 2) and (Degree(E) eq 3): "Q must be of degree 2 and E of degree 3";
    
    vprint Genus4 : "Trying with Macaulay resultants...";

    R<X,Y,Z,T> := Parent(Q);
    
    vars := Matrix([[X],[Y],[Z],[T]]);
    M := ChangeRing(RandomSLnZ(4, 3, 12), R); // add some probabilistic method to increase the chance of having well-defined Macaulay resultants
    Q0 := Evaluate(Q, Eltseq(M*vars));
    E0 := Evaluate(E, Eltseq(M*vars));
    
    for i in [1..5] do // try computing the Macaulay resultants
        d1 := MacaulayResultant([E0, Derivative(Q0, 2), Q0, Derivative(E0, 2)]);
        _<x,y,z> := PolynomialRing(BaseRing(R), 3);
        Disc_red := DiscriminantTernary(Evaluate(E0, [x,y,z,0]), Evaluate(Q0, [x,y,z,0]));
        res := MacaulayResultant([Jaco(E0, Q0, 1, 2), E0 , Jaco(E0, Q0, 2, 3), Q0]);
        if (Type(d1) eq MonStgElt) or (Type(Disc_red) eq MonStgElt) or (Type(res) eq MonStgElt) or (d1*Disc_red eq 0) then
            M := ChangeRing(RandomSLnZ(4, 5, 5), R);
            Q0 := Evaluate(Q, Eltseq(M*vars));
            E0 := Evaluate(E, Eltseq(M*vars));
        else 
            vprint Genus4 : "Done!";
            return res/(d1*Disc_red);
        end if;
    end for;  
    vprint Genus4 : "Fail, we use invariants instead...";
    Inv, _, norm := InvariantsGenus4Curves(Q, E);
    vprint Genus4: "Done!";
    return DiscriminantFromInvariantsGenus4(Inv : norm := norm);
end intrinsic;

intrinsic DiscriminantGenus4(C::Crv) -> RngInt
    {Given a curve C of genus 4, return its discriminant.}
    
	require Genus(C) eq 4: "C must be of genus 4";
    
    test_hyp, C1 := IsHyperelliptic(C);
    if test_hyp then
        return DiscriminantGenus4(C1);
    end if;

    Eq := Equations(C);
	ParallelSort([Degree(l) : l in Eq], Eq);
    Q, E := Explode(Eq[1..2]);
    
    return DiscriminantGenus4(Q, E);
end intrinsic;

intrinsic DiscriminantGenus4(f::RngUPolElt) -> RngInt
    {Given a univariate polynomial f of degree 9 or 10, return the discriminant of the hyperelliptic curve given by y^2 = f(x).}

	require Rank(Parent(f)) eq 1: "f must be a univariate polynomial";    
	require Degree(f) in {9,10}: "f must be of degree 9 or 10";
	
    C := HyperellipticCurve(f);
    
    return Discriminant(C);
end intrinsic; 

intrinsic DiscriminantGenus4(C::CrvHyp) -> RngInt
    {Given a hyperelliptic curve C of genus 4, return its discriminant.}    
    return Discriminant(C);
end intrinsic; 