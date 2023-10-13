intrinsic Transvectant(f::RngMPolElt, g::RngMPolElt, r::RngIntElt, s::RngIntElt : invariant := false) -> RngMPolElt
	{Given two covariants f and g given as two bihomogeneous polynomials, return their transvectant of level (r,s). 
	If invariant is set to true, the element returned is an element of the base ring, not a polynomial.}

    require Parent(f) eq Parent(f): "f and g must have the same parent";

    P := Parent(f);
	R<X,Y> := PolynomialRing(P, 2);

    require IsHomogeneous(Evaluate(f, [P.1, P.2, X, Y])) and IsHomogeneous(Evaluate(f, [X, Y, P.3, P.4])) and IsHomogeneous(Evaluate(g, [P.1, P.2, X, Y])) and IsHomogeneous(Evaluate(g, [X, Y, P.3, P.4])): "f and g must be bihomogeneous";

    if f eq 0 or g eq 0 then return P!0; end if;
    
    Sf := [[Derivative(Derivative(Derivative(Derivative(f, j, 1), r-j, 2), i, 3), s-i, 4) : j in [0..r]] : i in [0..s]];
	Sg := [[Derivative(Derivative(Derivative(Derivative(g, j, 1), r-j, 2), i, 3), s-i, 4) : j in [0..r]] : i in [0..s]];
    Tfg := P!0;
    
    for i := 0 to s do
		for j := 0 to r do
        		Tfg +:= (-1)^(i+j)*Binomial(s, i)*Binomial(r, j)*(Sf[i+1][j+1]*Sg[s+1-i][r+1-j]);
		end for;
    end for;
    
	if Characteristic(BaseRing(P)) eq 0 then
		m1 := Degree(Evaluate(f, [X, Y, P.3, P.4]));
		n1 := Degree(Evaluate(f, [P.1, P.2, X, Y]));
		m2 := Degree(Evaluate(g, [X, Y, P.3, P.4]));
		n2 := Degree(Evaluate(g, [P.1, P.2, X, Y]));
		//cfg := Factorial(m1-r)*Factorial(m2-r)*Factorial(n1-s)*Factorial(n2-s)/(Factorial(m1)*Factorial(m2)*Factorial(n1)*Factorial(n2));
		cfg := 1;
	else
		cfg := 1;
	end if;	
	
	if invariant then 
		return cfg*Evaluate(Tfg, [0,0,0,0]);
	else
		return cfg*Tfg;
	end if;

end intrinsic;