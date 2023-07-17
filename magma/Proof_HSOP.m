/*
intrinsic Transvectant(f::RngMPolElt, g::RngMPolElt, r::RngIntElt, s::RngIntElt) -> RngMPolElt
    	{Given two covariants f and g given as two bihomogeneous polynomials, return their transvectant of level (r,s)}
    	P := Parent(f);
    	require P eq Parent(g) : "Arguments 1 and 2 must be have the same parent.";
    	require IsHomogeneous(Evaluate(f, [P.1, P.2, 1, 1])) and IsHomogeneous(Evaluate(f, [1, 1, P.3, P.4])) and IsHomogeneous(Evaluate(g, [P.1, P.2, 1, 1])) and IsHomogeneous(Evaluate(g, [1, 1, P.3, P.4])) : "Arguments 1 and 2 must be bihomogeneous.";
    	if f eq 0 or g eq 0 then return P!0; end if;
    	Sf := [[Derivative(Derivative(Derivative(Derivative(f, j, 1), r-j, 2), i, 3), s-i, 4) : j in [0..r]] : i in [0..s]];
	Sg := [[Derivative(Derivative(Derivative(Derivative(g, j, 1), r-j, 2), i, 3), s-i, 4) : j in [0..r]] : i in [0..s]];
    	Tfg := P!0;
    	for i := 0 to s do
		for j := 0 to r do
        		Tfg +:= (-1)^(i+j)*Binomial(s, i)*Binomial(r, j)*(Sf[i+1][j+1]*Sg[s+1-i][r+1-j]);
		end for;
    	end for;
    	m1 := Degree(Evaluate(f, [P.1, P.2, 1, 2]));
	n1 := Degree(Evaluate(f, [1, 2, P.3, P.4]));
	m2 := Degree(Evaluate(g, [P.1, P.2, 1, 2]));
	n2 := Degree(Evaluate(g, [1, 2, P.3, P.4]));
    	cfg := Factorial(m1-r)*Factorial(m2-r)*Factorial(n1-s)*Factorial(n2-s)/(Factorial(m1)*Factorial(m2)*Factorial(n1)*Factorial(n2));
    return cfg*Tfg;
end intrinsic;


function Evaluation(I, f)
	if Type(I) ne List then
		return f;
	elif #I eq 1 then
		return f;
	elif #I eq 2 then
		return Evaluation(I[1], f)+Evaluation(I[2], f);
	end if;
	return Transvectant(Evaluation(I[1], f), Evaluation(I[2], f), I[3], I[4]);
end function;


function DegreeOrder(I)
	if Type(I) ne List then
		return [1,3,3];
	elif #I eq 1 then
		return [1,3,3];
	elif #I eq 2 then
		return DegreeOrder(I[1]);
	end if;
	c1 := DegreeOrder(I[1]);
	c2 := DegreeOrder(I[2]);
	return [c1[1]+c2[1], c1[2]+c2[2]-2*I[3], c1[3]+c2[3]-2*I[4]];
end function;

function CoefficientMatrix(f)
	P := Parent(f);
	R := BaseRing(P);
	m := Degree(Evaluate(f, [P.1, P.2, 1, 2]));	
	n := Degree(Evaluate(f, [1, 2, P.3, P.4]));
	M := [[R!MonomialCoefficient(f, y^i*x^(m-i)*v^j*u^(n-j)) : i in [0..m]] : j in [0..n]];
	return Matrix(M);
end function; 


*/

function Transvectant(f, g, r, s)
    	P := Parent(f);
    	if f eq 0 or g eq 0 then return P!0; end if;
    	Sf := [[Derivative(Derivative(Derivative(Derivative(f, j, 1), r-j, 2), i, 3), s-i, 4) : j in [0..r]] : i in [0..s]];
	Sg := [[Derivative(Derivative(Derivative(Derivative(g, j, 1), r-j, 2), i, 3), s-i, 4) : j in [0..r]] : i in [0..s]];
    	Tfg := P!0;
    	for i := 0 to s do
		for j := 0 to r do
        		Tfg +:= (-1)^(i+j)*Binomial(s, i)*Binomial(r, j)*(Sf[i+1][j+1]*Sg[s+1-i][r+1-j]);
		end for;
    	end for;
    	m1 := Degree(Evaluate(f, [P.1, P.2, 1, 2]));
	n1 := Degree(Evaluate(f, [1, 2, P.3, P.4]));
	m2 := Degree(Evaluate(g, [P.1, P.2, 1, 2]));
	n2 := Degree(Evaluate(g, [1, 2, P.3, P.4]));
    	cfg := Factorial(m1-r)*Factorial(m2-r)*Factorial(n1-s)*Factorial(n2-s)/(Factorial(m1)*Factorial(m2)*Factorial(n1)*Factorial(n2));
    if Degree(Tfg) eq 0 then 
		return cfg*Evaluate(Tfg, [0,0,0,0]);
	else
		return cfg*Tfg;
	end if;
end function;

function Evaluation(I, f)
	if Type(I) ne List then
		return f;
	elif #I eq 1 then
		return f;
	elif #I eq 2 then
		return Evaluation(I[1], f)+Evaluation(I[2], f);
	end if;
	return Transvectant(Evaluation(I[1], f), Evaluation(I[2], f), I[3], I[4]);
end function;

function CoefficientMatrix(f)
	P := Parent(f);
	R<a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22, a23, a30, a31, a32, a33, X> := CoefficientRing(P);
	m := Degree(Evaluate(f, [P.1, P.2, 1, 2]));	
	n := Degree(Evaluate(f, [1, 2, P.3, P.4]));
	M := [[R!MonomialCoefficient(f, (P.2)^i*(P.1)^(m-i)*(P.4)^j*(P.3)^(n-j)) : i in [0..m]] : j in [0..n]];
	return Matrix(M);
end function; 

function InvariantsHSOP(f0, d)
	R<a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22, a23, a30, a31, a32, a33, X> := CoefficientRing(Parent(f0));
	D<f> := PolynomialRing(K);
	H := [*f, f, 2, 2*];
	m := [*f, f, 1, 1*];
	H2 := [*H, H, 1, 1*];
	j2 := [*f, f, 3, 3*];
	j4 := [*[*m, f, 2, 2*], f, 3, 3*];
	j6 := [*[*[*[*[*f, f, 2, 2*], f, 2, 2*], f, 1, 1*], f, 1, 1*], f, 3, 3*];
	j8 := [*[*[*[*[*[*[*f, f, 2, 2*], f, 1, 1*], f, 2, 2*], f, 1, 1*], f, 2, 2*], f, 1, 1*], f, 3, 3*];
	j10 := [*[*[*[*[*[*[*[*[*f, f, 2, 2*], f, 2, 2*], f, 1, 1*], f, 1, 1*], f, 2, 2*], f, 2, 2*], f, 1, 1*], f, 1, 1*], f, 3, 3*];
	j12 := [*[*[*[*[*[*[*[*[*[*[*f, f, 2, 2*], f, 1, 1*], f, 2, 2*], f, 1, 1*], f, 2, 2*], f, 1, 1*], f, 1, 1*], f, 2, 2*], f, 0, 0*], f, 3, 3*], f, 3, 3*];
	j14 := [*[*[*[*[*[*[*[*[*[*[*H, f, 2, 2*], f, 1, 1*], f, 2, 2*], f, 1, 1*], f, 1, 1*], f, 2, 2*], f, 2, 2*], f, 1, 1*], f, 2, 2*], H, 0, 0*], f, 3, 3*];
	MH := CoefficientMatrix(Evaluation(H, f0));
	inv2 := R!Evaluate(Evaluation(j2, f0), [0,0,0,0]);
	inv4 := R!Evaluate(Evaluation(j4, f0), [0,0,0,0]);
	inv6 := R!Evaluate(Evaluation(j6, f0), [0,0,0,0]);
	inv8 := R!Evaluate(Evaluation(j8, f0), [0,0,0,0]);
	inv10 := R!Evaluate(Evaluation(j10, f0), [0,0,0,0]);
	inv12 := R!Evaluate(Evaluation(j12, f0), [0,0,0,0]);
	inv14 := R!Evaluate(Evaluation(j14, f0), [0,0,0,0]);
	return [inv2, MH[1][1], MH[2][1], MH[3][1], MH[2][2], MH[d][2], inv4, inv6, inv8, inv10, inv12, inv14];
end function;

function InvariantsHSOP(f, d)
	//Covariants
	//Degree 2
	R<a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22, a23, a30, a31, a32, a33, X> := CoefficientRing(Parent(f));
	Jac := Transvectant(f, f, 1, 1);
	H := Transvectant(f, f, 2, 2);
	MH := CoefficientMatrix(H);

	//Degree 3
	C33 := Transvectant(Jac, f, 2, 2);

	C31H := Transvectant(H, f, 2, 2);
	C33H := Transvectant(H, f, 1, 1);

	//Degree 4
	CH := Transvectant(H, H, 1, 1);
	C42H := Transvectant(C31H, f, 1, 1);
	C42H1 := Transvectant(C33H, f, 2, 2);

	//Degree 5
	C51H := Transvectant(C42H, f, 2, 2);
	C53H := Transvectant(C42H, f, 1, 1);
	C53H1 := Transvectant(C42H1, f, 1, 1);

	//Degree 6
	C62H := Transvectant(C53H, f, 2, 2);
	C62H1 := Transvectant(C53H1, f, 2, 2);
	C62H2 := Transvectant(C51H, f, 1, 1);

	//Degree 7
	C71H := Transvectant(C62H, f, 2, 2);
	C73H1 := Transvectant(C62H1, f, 1, 1);

	//Invariants
	//HSOP
	J2 := Transvectant(f, f, 3, 3);
	J4H := Transvectant(H, H, 2, 2);
	J4 := Transvectant(C33, f, 3, 3);	
	J6H := Transvectant(H, CH, 2, 2);
	J61 := Transvectant(C53H, f, 3, 3);
	J8H := Transvectant(CH, CH, 2, 2);
	J81 := Transvectant(C73H1, f, 3, 3);
	J101 := Transvectant(Transvectant(Transvectant(C71H, f, 1, 1), f, 1, 1), f, 3, 3);
	J121 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C73H1, f, 1, 1), f, 2, 2), f, 0, 0), f, 3, 3), f, 3, 3);
	J141 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C62H2, f, 1, 1), f, 2, 2), f, 2, 2), f, 1, 1), f, 2, 2), H, 0, 0), f, 3, 3);
	return [J2, MH[1][1], MH[2][1], MH[3][1], MH[2][2], MH[d][2], J4, J61, J81, J101, J121, J141];
end function;

K := Rationals();
R1<a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22, a23, a30, a31, a32, a33, X> := PolynomialRing(K, [1 : i in [1..17]]);
R<x, y, u, v> := PolynomialRing(R1, 4);


//Case 1 
f0 := a30*x^3*v^3+a22*x^2*y*u^2*v+a21*x^2*y*u*v^2+a20*x^2*y*v^3+a13*x*y^2*u^3+a12*x*y^2*u^2*v+a11*x*y^2*u*v^2+a10*x*y^2*v^3+a03*y^3*u^3+a02*y^3*u^2*v+a01*y^3*u*v^2+a00*y^3*v^3;
CoefficientMatrix(f0);
I := Ideal(InvariantsHSOP(f0, 1));
RadicalDecomposition(I);
//voir la décomposition des différents trucs pour voir si c'est okay


//Case 2 
f0 := x^3*u*v^2+a22*x^2*y*u^2*v+a20*x^2*y*v^3+a13*x*y^2*u^3+a12*x*y^2*u^2*v+a11*x*y^2*u*v^2+a10*x*y^2*v^3+a03*y^3*u^3+a02*y^3*u^2*v+a01*y^3*u*v^2+a00*y^3*v^3;
CoefficientMatrix(f0);
I := Ideal(InvariantsHSOP(f0, 1));
RadicalDecomposition(I);



//Case 3
f0 := x^3*u^2*v+a30*x^3*v^3+a21*x^2*y*u*v^2+a20*x^2*y*v^3+a13*x*y^2*u^3+a12*x*y^2*u^2*v+a11*x*y^2*u*v^2+a10*x*y^2*v^3+a03*y^3*u^3+a02*y^3*u^2*v+a01*y^3*u*v^2+a00*y^3*v^3;
CoefficientMatrix(f0);
MH := CoefficientMatrix(Transvectant(f0, f0, 2, 2));
I := Ideal(InvariantsHSOP(f0, 1) cat [MH[3][2]*X-1]);
[[IsInRadical(MH[i][j], I) : j in [1..3]] : i in [1..3]];
[[IsInRadical(MonomialCoefficient(f0, y^i*x^(3-i)*v^j*u^(3-j)), I) : i in [0..3]] : j in [0..3]];



//Case 4 
f0 := a31*x^3*u*v^2+a30*x^3*v^3+x^2*y*u^3+a21*x^2*y*u*v^2+a20*x^2*y*v^3+a12*x*y^2*u^2*v+a11*x*y^2*u*v^2+a10*x*y^2*v^3+a03*y^3*u^3+a02*y^3*u^2*v+a01*y^3*u*v^2+a00*y^3*v^3;
CoefficientMatrix(f0);
List_invariants := InvariantsHSOP(f0, 1);
I := Ideal(List_invariants);
MH := CoefficientMatrix(Transvectant(f0, f0, 2, 2));
[[IsInRadical(MH[i][j], I) : j in [1..3]] : i in [1..3]];

//First subcase
I := Ideal(List_invariants cat [MH[1][3]*X-1]);
[[IsInRadical(MonomialCoefficient(f0, y^i*x^(3-i)*v^j*u^(3-j)), I) : i in [0..3]] : j in [0..3]];

//Second subcase
I := Ideal(List_invariants cat [MH[2][3]*X-1]);
[[IsInRadical(MonomialCoefficient(f0, y^i*x^(3-i)*v^j*u^(3-j)), I) : i in [0..3]] : j in [0..3]];



//Case 5
f0 := x^3*u^2*v+a31*x^3*u*v^2+a30*x^3*v^3+x^2*y*u^3+a21*x^2*y*u*v^2+a20*x^2*y*v^3+a12*x*y^2*u^2*v+a11*x*y^2*u*v^2+a10*x*y^2*v^3+a03*y^3*u^3+a02*y^3*u^2*v+a01*y^3*u*v^2+a00*y^3*v^3;
CoefficientMatrix(f0);
MH := CoefficientMatrix(Transvectant(f0, f0, 2, 2));
I := Ideal(InvariantsHSOP(f0, 1));
[[IsInRadical(MH[i][j], I) : j in [1..3]] : i in [1..3]];


//Now the second case, where we turned H upside down
//Case 1
f0 := a30*x^3*v^3+a22*x^2*y*u^2*v+a21*x^2*y*u*v^2+a20*x^2*y*v^3+a13*x*y^2*u^3+a12*x*y^2*u^2*v+a11*x*y^2*u*v^2+a10*x*y^2*v^3+a03*y^3*u^3+a02*y^3*u^2*v+a01*y^3*u*v^2+a00*y^3*v^3;
CoefficientMatrix(f0);
I := Ideal(InvariantsHSOP(f0, 3));
MH := CoefficientMatrix(Transvectant(f0, f0, 2, 2));
[[IsInRadical(MH[i][j], I) : j in [1..3]] : i in [1..3]];


//Case 2 
f0 := x^3*u*v^2+a30*x^3*v^3+a22*x^2*y*u^2*v+a20*x^2*y*v^3+a13*x*y^2*u^3+a12*x*y^2*u^2*v+a11*x*y^2*u*v^2+a10*x*y^2*v^3+a03*y^3*u^3+a02*y^3*u^2*v+a01*y^3*u*v^2+a00*y^3*v^3;
CoefficientMatrix(f0);
MH := CoefficientMatrix(Transvectant(f0, f0, 2, 2));
I := Ideal(InvariantsHSOP(f0, 3) cat [MH[1][2]*X-1]);
IsInRadical(a30, I);

//Case 3
//First subcase
f0 := x^3*u^2*v+a31*x^3*u*v^2+a30*x^3*v^3+x^2*y*u*v^2+a20*x^2*y*v^3+a13*x*y^2*u^3+a12*x*y^2*u^2*v+a11*x*y^2*u*v^2+a10*x*y^2*v^3+a03*y^3*u^3+a02*y^3*u^2*v+a01*y^3*u*v^2+a00*y^3*v^3;
CoefficientMatrix(f0);
MH := CoefficientMatrix(Transvectant(f0, f0, 2, 2));
I := Ideal(InvariantsHSOP(f0, 3) cat [MH[1][2]*X-1]);
IsInRadical(a30, I);

//Second subcase
f0 := x^3*u^2*v+a31*x^3*u*v^2+a30*x^3*v^3+a20*x^2*y*v^3+a13*x*y^2*u^3+a12*x*y^2*u^2*v+a11*x*y^2*u*v^2+a10*x*y^2*v^3+a03*y^3*u^3+a02*y^3*u^2*v+a01*y^3*u*v^2+a00*y^3*v^3;
CoefficientMatrix(f0);
MH := CoefficientMatrix(Transvectant(f0, f0, 2, 2));
I := Ideal(InvariantsHSOP(f0, 3) cat [MH[1][2]*X-1]);
IsInRadical(a30, I);

//Case 4
//First subcase
f0 := x^3*u*v^2+a30*x^3*v^3+x^2*y*u^3+a22*x^2*y*u^2*v+a21*x^2*y*u*v^2+a20*x^2*y*v^3+a12*x*y^2*u^2*v+a11*x*y^2*u*v^2+a10*x*y^2*v^3+a03*y^3*u^3+a02*y^3*u^2*v+a01*y^3*u*v^2+a00*y^3*v^3;
CoefficientMatrix(f0);
MH := CoefficientMatrix(Transvectant(f0, f0, 2, 2));
I := Ideal(InvariantsHSOP(f0, 3) cat [MH[1][2]*X-1]);
IsInRadical(a30, I);

//Second subcase
f0 := a30*x^3*v^3+x^2*y*u^3+a22*x^2*y*u^2*v+a21*x^2*y*u*v^2+a20*x^2*y*v^3+a12*x*y^2*u^2*v+a11*x*y^2*u*v^2+a10*x*y^2*v^3+a03*y^3*u^3+a02*y^3*u^2*v+a01*y^3*u*v^2+a00*y^3*v^3;
CoefficientMatrix(f0);
MH := CoefficientMatrix(Transvectant(f0, f0, 2, 2));
I := Ideal(InvariantsHSOP(f0, 3) cat [MH[1][2]*X-1]);
IsInRadical(a30, I);


//Case 5 
f0 := x^3*u^2*v+a31*x^3*u*v^2+a30*x^3*v^3+x^2*y*u^3+a21*x^2*y*u*v^2+a20*x^2*y*v^3+a13*x*y^2*u^3+a12*x*y^2*u^2*v+a11*x*y^2*u*v^2+a10*x*y^2*v^3+a03*y^3*u^3+a02*y^3*u^2*v+a01*y^3*u*v^2+a00*y^3*v^3;
CoefficientMatrix(f0);
MH := CoefficientMatrix(Transvectant(f0, f0, 2, 2));
I := Ideal(InvariantsHSOP(f0, 3) cat [MH[1][2]*X-1]);
IsInRadical(a30, I);
