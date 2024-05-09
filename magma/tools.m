function QuadraticFormToMatrix(Q)
        R := Parent(Q);
        K := CoefficientRing(R);
        Q_mat := Matrix(K, [[MonomialCoefficient(Q, R.i*R.j)/2 : j in [1..4]] : i in [1..4]]);

        for i in [1..4] do
                Q_mat[i][i] := 2*Q_mat[i][i];
        end for;

        return Q_mat;
end function;

function NewBasis(Q)
    K := BaseRing(Parent(Q));
    D, P := DiagonalForm(Q);
    D := QuadraticFormToMatrix(D);
    if IsExact(K) then
        t := Rank(D);
    else
        vprint Genus4 : "Base ring is precision field; using numerical algorithms";
        prec := Precision(K);
        RR := RealField(prec);
        eps := RR!10^(-prec*1/4);
        t := NumericalRank(D : Epsilon:=eps);
    end if;
    vprint Genus4 : "rank =", t;

        if t lt 3 then
                "The quadric is not of rank 3 or 4";
                return D, t, 1;

        elif t eq 4 then
                L := [-D[4][4]/D[1][1], -D[3][3]/D[2][2]];

                bool1 := IsPower(L[1], 2);
                bool2 := IsPower(L[2], 2);

                if bool1 and bool2 then
                        S := K;
                        _, sq1 := IsPower(L[1], 2);
                        _, sq2 := IsPower(L[2], 2);
                        Sq := [sq1, sq2];
                else
                        _<x> := PolynomialRing(K);
                        S := SplittingField([x^2-L[1], x^2-L[2]]);
                        Sq := [Sqrt(S!L[1]), Sqrt(S!L[2])];
                end if;

                M2 := KMatrixSpace(S,4,4);
                P := ChangeRing(P, S);
                P_fin := (M2![S!1/(2*D[1][1]),0,0,S!1/(2*D[1][1]*Sq[1]),0,S!-1/(2*D[2][2]),S!-1/(2*D[2][2]*Sq[2]),0,0,S!1/2,S!-1/(2*Sq[2]),0,S!1/2,0,0,S!-1/(2*Sq[1])])*P;

                return P_fin, 4, 1;

        else
                i := 1;
                if IsExact(K) then
                    while (D[i][i] ne 0) and (i lt 4) do
                            i := i+1;
                    end while;
                else
                    m, i := Min([Abs(D[j][j]) : j in [1..4]]);

                end if;

                L_swap := [1,2,3,4];
                L_swap[i] := 4;
                 L_swap[4] := i;
                P_swap := PermutationMatrix(K, L_swap);

                D := P_swap*D*P_swap;
                P := P_swap*P;
                l := -D[3][3]/D[1][1];

                bool1 := IsPower(l, 2);

                if bool1 then
                        S := K;
                        _, sq := IsPower(l, 2);
                else
                        _<x> := PolynomialRing(K);
                        S := SplittingField(x^2-l);
                        sq := Sqrt(S!l);
                end if;

                M2 := KMatrixSpace(S,4,4);
                P := ChangeRing(P, S);
                P_fin := (M2![S!-D[2][2]/(2*D[1][1]),0,S!-D[2][2]/(2*D[1][1]*sq),0,0,1,0,0,S!1/2,0,S!-1/(2*sq),0,0,0,0,S!1])*P;
                return P_fin, 3, sq;
        end if;
end function;


// given a form and a change of variables (given as a matrix), returns the form after the change of variables
function ChangeOfBasis(C, P)
        R := ChangeRing(Parent(C), Parent(P[1][1]));
        C := R!C;
        P := Transpose(Matrix([[R!P[i][j] : j in [1..NumberOfColumns(P)]] : i in [1..NumberOfRows(P)]]));
        Y := ElementToSequence(P*Matrix([[R.i] : i in [1..Rank(R)]]));
        return Evaluate(C, Y);
end function;

function CubicNewBasis(Q, C)
        R := Parent(C);
        P, _, r := NewBasis(Q);
        R := ChangeRing(R, BaseRing(Parent(P)));
        C1 := R!C;
        return ChangeOfBasis(C1, P), r;
end function;


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
