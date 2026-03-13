/*
 *  Genus 4 curves
 *
 *  Thomas Bouchet
 *
 *  See LICENSE.txt for license details.
*/

intrinsic QuadraticFormToMatrix(Q::RngMPolElt) -> AlgMatElt
    {
        Given a homogeneous quadratic form, return the associated symmetric matrix. 
    }
    R := Parent(Q);
    K := BaseRing(R);
    assert Characteristic(K) ne 2;
    Q_mat := Matrix(FieldOfFractions(K), [[MonomialCoefficient(Q, R.i*R.j)/2: j in [1..i]] cat [0 : j in [i+1..Rank(R)]] : i in [1..Rank(R)]]);
    return Q_mat+Transpose(Q_mat);
end intrinsic;

function BasisNormalForm(Q)
    /* Given a quadratic form Q in 4 variables, put it in the form XT-YZ when Q defines a smooth quadric surface, or XZ-Y^2 when it defines a quadric cone.
    Output: 
        - P_fin is the transformation to that basis such that Q^P_fin = XT-YZ or XZ-Y^2,
        - t is the rank of Q as a quadratic form */
    K := BaseRing(Parent(Q));
    D, P := DiagonalForm(Q);
    D := QuadraticFormToMatrix(D);
    if IsExact(K) then
        t := Rank(D);
    else
        vprint Genus4 : "Base ring is precision field; using numerical algorithms";
        prec := Precision(K);
        RR := RealField(prec);
        eps := RR!10^(-prec*7/8);
        t := NumericalRank(D : Epsilon:=eps);
    end if;
    vprint Genus4 : "rank =", t;

    if t lt 3 then
        error("Warning: The quadric is not of rank 3 or 4");

    elif t eq 4 then
        L := [-D[4][4]/D[1][1], -D[3][3]/D[2][2]];
        bool1, bool2 := IsPower(L[1], 2), IsPower(L[2], 2);

        if bool1 and bool2 then
            S := K;
            _, sq1 := IsPower(L[1], 2);
            _, sq2 := IsPower(L[2], 2);
            Sq := [sq1, sq2];
        else
            _<x> := PolynomialRing(K);
            S := SplittingField((x^2-L[1])*(x^2-L[2]));
            Sq := [Sqrt(S!L[1]), Sqrt(S!L[2])];
        end if;

        M2 := KMatrixSpace(S,4,4);
        P := ChangeRing(P, S);
        P_fin := (M2![S!1/(2*D[1][1]),0,0,S!1/(2*D[1][1]*Sq[1]),0,S!-1/(2*D[2][2]),S!-1/(2*D[2][2]*Sq[2]),0,0,S!1/2,S!-1/(2*Sq[2]),0,S!1/2,0,0,S!-1/(2*Sq[1])])*P;
        return Transpose(P_fin), 4;

    else 
        // we first put the zero coefficient of the diagonal form to the last coordinate
        i := 1;
        if IsExact(K) then
            while (D[i][i] ne 0) and (i lt 4) do
                i := i+1;
            end while;
        else
            _, i := Min([Abs(D[j][j]) : j in [1..4]]);
        end if;

        L_swap := [1,2,3,4];
        L_swap[i] := 4;
        L_swap[4] := i;
        P_swap := PermutationMatrix(K, L_swap);

        D := P_swap*D*P_swap;
        P := P_swap*P;
        L := [-D[3][3]/D[1][1], -D[2][2]];
        bool1, sq1 := IsPower(L[1], 2);
        bool2, sq2 := IsPower(L[2], 2);

        if bool1 and bool2 then
            S := K;
            Sq := [sq1, sq2];
        else
            _<x> := PolynomialRing(K);
            S := SplittingField((x^2-L[1])*(x^2-L[2]));
            Sq := [Sqrt(S!L[1]), Sqrt(S!L[2])];
        end if;

        M2 := KMatrixSpace(S,4,4);
        P := ChangeRing(P, S);
        P_fin := (M2![S!1/(2*D[1][1]),0,S!1/(2*D[1][1]*Sq[1]),0,0,S!1/Sq[2],0,0,S!1/2,0,S!-1/(2*Sq[1]),0,0,0,0,S!1])*P;
        return Transpose(P_fin), 3;//, Sq;
    end if;
end function;

function CubicNewBasis(Gamma, P)
    /* Given a cubic form Gamma and a matrix P, apply the transformation P to Gamma. */
    R := ChangeRing(Parent(Gamma), BaseRing(Parent(P)));
    return (R!Gamma)^P;
end function;

intrinsic Transvectant(f::RngMPolElt, g::RngMPolElt, r::RngIntElt, s::RngIntElt : invariant := false) -> RngMPolElt
	{Given two covariants f and g given as two bihomogeneous polynomials, return their transvectant of level (r,s). Note that the normalizing factor is not applied.
	If the flag invariant is set to true, the element returned is an element of the base ring of f and g.}

    require Parent(f) eq Parent(g): "f and g must have the same parent";

    R := Parent(f);

    if f*g eq 0 then return R!0; end if;

    R0<X,Y> := PolynomialRing(R, 2);
    require IsHomogeneous(Evaluate(f, [R.1, R.2, X, Y])) and IsHomogeneous(Evaluate(f, [X, Y, R.3, R.4])) and IsHomogeneous(Evaluate(g, [R.1, R.2, X, Y])) and IsHomogeneous(Evaluate(g, [X, Y, R.3, R.4])): "f and g must be bihomogeneous";

    Sf := [[Derivative(Derivative(Derivative(Derivative(f, j, 1), r-j, 2), i, 3), s-i, 4) : j in [0..r]] : i in [0..s]];
    Sg := [[Derivative(Derivative(Derivative(Derivative(g, j, 1), r-j, 2), i, 3), s-i, 4) : j in [0..r]] : i in [0..s]];
    Tfg := R!0;

    for i := 0 to s do
        for j := 0 to r do
            Tfg +:= (-1)^(i+j)*Binomial(s, i)*Binomial(r, j)*(Sf[i+1][j+1]*Sg[s+1-i][r+1-j]);
        end for;
    end for;

    if invariant then
	    return Evaluate(Tfg, [0,0,0,0]);
    else
	    return Tfg;
    end if;

end intrinsic;

/*
The following functions were developed with the help and software of Laurent Bus\'e (https://www-sop.inria.fr/members/Laurent.Buse/index.html)
*/

// Compute the Macaulay matrix associated to a list of polynomials list_poly
function MacMatrix(list_poly)
	R := Parent(list_poly[1]);
    n := #list_poly;
	if (Rank(R) ne n) or (#[l : l in list_poly | l eq 0] ne 0) then
        error("The number of polynomials in the list must be the number of variables.");
    end if;
	list_deg := [Degree(p) : p in list_poly]; // the polynomials must be only polynomials in list_var only
    nu := &+list_deg - n + 1;

	list_mon := Set(MonomialsOfDegree(R, nu));
	dodu := []; // list of integers that give the submatrix
	Base := []; // list of monomials that index the matrix
	list_poly_mat := []; // the list of polynomials of the matrix

	for i in [1..n-1] do // i corresponds to the variable var[i]
		s := MonomialsOfDegree(R, nu-list_deg[i]);
		tt := [s[j]*(R.i)^list_deg[i] : j in [1..#s] | s[j]*(R.i)^(list_deg[i]) in list_mon];
		for j in [1..#tt] do
			Append(~list_poly_mat, R!(list_poly[i]*tt[j]/(R.i)^(list_deg[i])));
			for k in [1..n] do
                if Rank(R) ge 2 then
    				if (k ne i) and (Degree(tt[j], R.k) ge list_deg[k]) then
    					Append(~dodu, j+#Base);
                    end if;
                else
                    if (k ne i) and (Degree(tt[j]) ge list_deg[k]) then
    					Append(~dodu, j+#Base);
                    end if;
				end if;
			end for;
		end for;
		list_mon := list_mon diff Set(tt);
		Base cat:= tt;
	end for;

    tt := SetToSequence(list_mon);

    for j in [1..#tt] do
		Append(~list_poly_mat, R!(list_poly[n]*tt[j]/(R.n)^list_deg[n]));
	end for;

    Base cat:= tt;
	dodu := Sort(Setseq(Set(dodu)));
	N := #list_poly_mat;
	M := ZeroMatrix(BaseRing(R), N, N);

    for i in [1..N] do
		for j in [1..N] do
			M[j,i] := MonomialCoefficient(list_poly_mat[i], Base[j]);
		end for;
	end for;

    return M, Submatrix(M,dodu,dodu);
end function;

// Compute the Macaulay resultant associated to the list of polynomials list_poly
function MacaulayResultant(list_poly)
	M, N := MacMatrix(list_poly);
    dn := Determinant(N);
    if dn eq 0 then
        error("Not precise enough, try adding new variables");
    else
        dm := Determinant(M);
        return dm/dn;
    end if;
end function;

function Jaco(f, g, i, j)
    return (Derivative(f, i)*Derivative(g, j) - Derivative(f, j)*Derivative(g, i));
end function;

function DiscriminantTernary(f, g)
    R<x,y,z> := Parent(f);
    vars := Matrix([[x], [y], [z]]);
    R0 := BaseRing(R);
    jac2 := Jaco(f, g, 1, 2);
    d1 := MacaulayResultant([f, g, jac2]);
    d2 := MacaulayResultant([f, g, Parent(f).3]);
    for i in [1..5] do
        if (Type(d1) eq MonStgElt) or (Type(d2) eq MonStgElt) or (d2 eq 0) then
            M := ChangeRing(RandomSLnZ(3, 5, 5), R);
            f := Evaluate(f, Eltseq(M*vars));
            g := Evaluate(g, Eltseq(M*vars));
            d1 := MacaulayResultant([f, g, jac2]);
            d2 := MacaulayResultant([f, g, Parent(f).3]);
        else
            return d1/d2;
        end if;
    end for;
    error("Try modifying f and g");
end function;
