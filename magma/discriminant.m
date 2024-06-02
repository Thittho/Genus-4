import "tools.m" : Jaco, MacaulayResultant, DiscriminantTernary;

intrinsic DiscriminantGenus4(Q::RngMPolElt, E::RngMPolElt) -> RngInt
    {Given a quadratic form Q and a cubic form E in 4 variables (over a field of char > 5), return the discriminant of the curve given by the complete intersection of the vanishing locus of Q and E.
    This method is not deterministic, it may fail in very unlucky cases.}
    
    require (Parent(Q) eq Parent(E)): "Q and E must have the same parent";
	require (Rank(Parent(Q)) eq 4): "Q and E must be polynomials in 4 variables";
	require IsHomogeneous(Q) and IsHomogeneous(E): "Q and E must be homogeneous";
	require (Degree(Q) eq 2) and (Degree(E) eq 3): "Q must be of degree 2 and E of degree 3";
    
    R<X,Y,Z,T> := Parent(Q);
    
    vars := Matrix([[X],[Y],[Z],[T]]);
    M := ChangeRing(RandomSLnZ(4, 3, 12), R); // add some probabilistic method to increase the chance of having well-defined Macaulay resultants
    Q0 := Evaluate(Q, Eltseq(M*vars));
    E0 := Evaluate(E, Eltseq(M*vars));
    
    for i in [1..100] do // try computing the Macaulay resultants
        d1 := MacaulayResultant([E0, Derivative(Q0, 2), Q0, Derivative(E0, 2)]);
        _<x,y,z> := PolynomialRing(BaseRing(R), 3);
        Disc_red := DiscriminantTernary(Evaluate(E0, [x,y,z,0]), Evaluate(Q0, [x,y,z,0]));
        res := MacaulayResultant([Jaco(E0, Q0, 1, 2), E0 , Jaco(E0, Q0, 2, 3), Q0]);
        if (Type(d1) eq MonStgElt) or (Type(Disc_red) eq MonStgElt) or (Type(res) eq MonStgElt) or (d1*Disc_red eq 0) then
            M := ChangeRing(RandomSLnZ(4, 5, 5), R);
            Q0 := Evaluate(Q, Eltseq(M*vars));
            E0 := Evaluate(E, Eltseq(M*vars));
        else 
            return res/(d1*Disc_red);
        end if;
    end for;
    "Unlucky, try again!";
    return "";
end intrinsic; 
