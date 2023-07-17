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


function ProofHsop()
	K := Rationals();
	R1<a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22, a23, a30, a31, a32, a33, X> := PolynomialRing(K, [1 : i in [1..17]]);
	R<x, y, u, v> := PolynomialRing(R1, 4);


	"First case for H:";
	"Case 1 for f:";"";
	f0 := a30*x^3*v^3+a22*x^2*y*u^2*v+a21*x^2*y*u*v^2+a20*x^2*y*v^3+a13*x*y^2*u^3+a12*x*y^2*u^2*v+a11*x*y^2*u*v^2+a10*x*y^2*v^3+a03*y^3*u^3+a02*y^3*u^2*v+a01*y^3*u*v^2+a00*y^3*v^3;
	Mat := CoefficientMatrix(f0);
	Mat;"";
	"f must be one of the following:";"";
	I := Ideal(InvariantsHSOP(f0, 1));
	Gb := RadicalDecomposition(I);
	for bas in Gb do
		Matrix([[NormalForm(Mat[i][j], bas) : j in [1..4]] : i in [1..4]]);
		"";
	end for;
	"";"";"";

	"Case 2 for f:";"";
	f0 := x^3*u*v^2+a22*x^2*y*u^2*v+a20*x^2*y*v^3+a13*x*y^2*u^3+a12*x*y^2*u^2*v+a11*x*y^2*u*v^2+a10*x*y^2*v^3+a03*y^3*u^3+a02*y^3*u^2*v+a01*y^3*u*v^2+a00*y^3*v^3;
	Mat := CoefficientMatrix(f0);
	Mat;"";
	"f must be one of the following:";"";
	I := Ideal(InvariantsHSOP(f0, 1));
	Gb := RadicalDecomposition(I);
	for bas in Gb do
		Matrix([[NormalForm(Mat[i][j], bas) : j in [1..4]] : i in [1..4]]);
		"";
	end for;
	"";"";"";


	"Case 3 for f:";"";
	f0 := x^3*u^2*v+a30*x^3*v^3+a21*x^2*y*u*v^2+a20*x^2*y*v^3+a13*x*y^2*u^3+a12*x*y^2*u^2*v+a11*x*y^2*u*v^2+a10*x*y^2*v^3+a03*y^3*u^3+a02*y^3*u^2*v+a01*y^3*u*v^2+a00*y^3*v^3;
	Mat := CoefficientMatrix(f0);
	Mat;"";
	MH := CoefficientMatrix(Transvectant(f0, f0, 2, 2));
	I := Ideal(InvariantsHSOP(f0, 1));
	"Only one coefficient of H does not vanish a priori:";"";
	[[IsInRadical(MH[i][j], I) : j in [1..3]] : i in [1..3]];"";
	"We can assume that b10 the coefficient of xyv^2 in H does not vanish, otherwise the lemma implies that f belongs to the nullcone. Then f must be:";"";
	I := Ideal(InvariantsHSOP(f0, 1) cat [MH[3][2]*X-1]);
	Gb := RadicalDecomposition(I);
	for bas in Gb do
		Matrix([[NormalForm(Mat[i][j], bas) : j in [1..4]] : i in [1..4]]);
		"";
	end for;
	"";"";"";


	"Case 4 for f:";"";
	f0 := a31*x^3*u*v^2+a30*x^3*v^3+x^2*y*u^3+a21*x^2*y*u*v^2+a20*x^2*y*v^3+a12*x*y^2*u^2*v+a11*x*y^2*u*v^2+a10*x*y^2*v^3+a03*y^3*u^3+a02*y^3*u^2*v+a01*y^3*u*v^2+a00*y^3*v^3;
	Mat := CoefficientMatrix(f0);
	Mat;"";
	List_invariants := InvariantsHSOP(f0, 1);
	I := Ideal(List_invariants);
	MH := CoefficientMatrix(Transvectant(f0, f0, 2, 2));
	"Only two coefficients of H do not vanish a priori:";"";
	[[IsInRadical(MH[i][j], I) : j in [1..3]] : i in [1..3]];"";

	"First subcase, the coefficient b02 of y^2u^2 in H does not vanish, f must be:";"";
	I := Ideal(List_invariants cat [MH[1][3]*X-1]);
	Gb := RadicalDecomposition(I);
	for bas in Gb do
		Matrix([[NormalForm(Mat[i][j], bas) : j in [1..4]] : i in [1..4]]);
		"";
	end for;
	
	"Second subcase, the coefficient b01 of y^2uv in H does not vanish, f must be:";"";
	I := Ideal(List_invariants cat [MH[2][3]*X-1]);
	Gb := RadicalDecomposition(I);
	for bas in Gb do
		Matrix([[NormalForm(Mat[i][j], bas) : j in [1..4]] : i in [1..4]]);
		"";
	end for;
	"";"";

	"Case 5 for f:";"";
	f0 := x^3*u^2*v+a31*x^3*u*v^2+a30*x^3*v^3+x^2*y*u^3+a21*x^2*y*u*v^2+a20*x^2*y*v^3+a12*x*y^2*u^2*v+a11*x*y^2*u*v^2+a10*x*y^2*v^3+a03*y^3*u^3+a02*y^3*u^2*v+a01*y^3*u*v^2+a00*y^3*v^3;
	CoefficientMatrix(f0);"";
	MH := CoefficientMatrix(Transvectant(f0, f0, 2, 2));
	I := Ideal(InvariantsHSOP(f0, 1));
	"We get that H vanishes:";"";
	[[IsInRadical(MH[i][j], I) : j in [1..3]] : i in [1..3]];
	"";"";"";"";

	"Second case for H:";
	"Case 1 for f:";"";
	f0 := a30*x^3*v^3+a22*x^2*y*u^2*v+a21*x^2*y*u*v^2+a20*x^2*y*v^3+a13*x*y^2*u^3+a12*x*y^2*u^2*v+a11*x*y^2*u*v^2+a10*x*y^2*v^3+a03*y^3*u^3+a02*y^3*u^2*v+a01*y^3*u*v^2+a00*y^3*v^3;
	CoefficientMatrix(f0);"";
	I := Ideal(InvariantsHSOP(f0, 3));
	MH := CoefficientMatrix(Transvectant(f0, f0, 2, 2));
	"The coefficient b12 of xyu^2 in H vanishes:", IsInRadical(MH[1][2], I);
	"Hence this case reduces to the first case for H.";
	"";"";"";

	"Case 2 for f:";"";
	f0 := x^3*u*v^2+a30*x^3*v^3+a22*x^2*y*u^2*v+a20*x^2*y*v^3+a13*x*y^2*u^3+a12*x*y^2*u^2*v+a11*x*y^2*u*v^2+a10*x*y^2*v^3+a03*y^3*u^3+a02*y^3*u^2*v+a01*y^3*u*v^2+a00*y^3*v^3;
	CoefficientMatrix(f0);"";
	MH := CoefficientMatrix(Transvectant(f0, f0, 2, 2));
	I := Ideal(InvariantsHSOP(f0, 3) cat [MH[1][2]*X-1]);
	"a30 vanishes:", IsInRadical(a30, I);
	"";"";"";

	"Case 3 for f, with the assumption a21 = 1 (always possible if a21 doest not vanish):";"";
	f0 := x^3*u^2*v+a31*x^3*u*v^2+a30*x^3*v^3+x^2*y*u*v^2+a20*x^2*y*v^3+a13*x*y^2*u^3+a12*x*y^2*u^2*v+a11*x*y^2*u*v^2+a10*x*y^2*v^3+a03*y^3*u^3+a02*y^3*u^2*v+a01*y^3*u*v^2+a00*y^3*v^3;
	CoefficientMatrix(f0);"";
	MH := CoefficientMatrix(Transvectant(f0, f0, 2, 2));
	I := Ideal(InvariantsHSOP(f0, 3) cat [MH[1][2]*X-1]);
	"a30 vanishes:", IsInRadical(a30, I);
	"";"";"";

	"Case 3 for f, with a21 = 0:";"";
	f0 := x^3*u^2*v+a31*x^3*u*v^2+a30*x^3*v^3+a20*x^2*y*v^3+a13*x*y^2*u^3+a12*x*y^2*u^2*v+a11*x*y^2*u*v^2+a10*x*y^2*v^3+a03*y^3*u^3+a02*y^3*u^2*v+a01*y^3*u*v^2+a00*y^3*v^3;
	CoefficientMatrix(f0);"";
	MH := CoefficientMatrix(Transvectant(f0, f0, 2, 2));
	I := Ideal(InvariantsHSOP(f0, 3) cat [MH[1][2]*X-1]);
	"a30 vanishes:", IsInRadical(a30, I);
	"";"";"";

	"Case 4 for f, with the assumption a31 = 1 (always possible if a31 doest not vanish):";"";
	f0 := x^3*u*v^2+a30*x^3*v^3+x^2*y*u^3+a22*x^2*y*u^2*v+a21*x^2*y*u*v^2+a20*x^2*y*v^3+a12*x*y^2*u^2*v+a11*x*y^2*u*v^2+a10*x*y^2*v^3+a03*y^3*u^3+a02*y^3*u^2*v+a01*y^3*u*v^2+a00*y^3*v^3;
	CoefficientMatrix(f0);"";
	MH := CoefficientMatrix(Transvectant(f0, f0, 2, 2));
	I := Ideal(InvariantsHSOP(f0, 3) cat [MH[1][2]*X-1]);
	"a30 vanishes:", IsInRadical(a30, I);
	"";"";"";

	"Case 4 for f, with a31 = 0:";"";
	f0 := a30*x^3*v^3+x^2*y*u^3+a22*x^2*y*u^2*v+a21*x^2*y*u*v^2+a20*x^2*y*v^3+a12*x*y^2*u^2*v+a11*x*y^2*u*v^2+a10*x*y^2*v^3+a03*y^3*u^3+a02*y^3*u^2*v+a01*y^3*u*v^2+a00*y^3*v^3;
	CoefficientMatrix(f0);"";
	MH := CoefficientMatrix(Transvectant(f0, f0, 2, 2));
	I := Ideal(InvariantsHSOP(f0, 3) cat [MH[1][2]*X-1]);
	"a30 vanishes:", IsInRadical(a30, I);
	"";"";"";

	"Case 5 for f:";"";
	f0 := x^3*u^2*v+a31*x^3*u*v^2+a30*x^3*v^3+x^2*y*u^3+a21*x^2*y*u*v^2+a20*x^2*y*v^3+a13*x*y^2*u^3+a12*x*y^2*u^2*v+a11*x*y^2*u*v^2+a10*x*y^2*v^3+a03*y^3*u^3+a02*y^3*u^2*v+a01*y^3*u*v^2+a00*y^3*v^3;
	CoefficientMatrix(f0);"";
	MH := CoefficientMatrix(Transvectant(f0, f0, 2, 2));
	I := Ideal(InvariantsHSOP(f0, 3) cat [MH[1][2]*X-1]);
	"a30 vanishes:", IsInRadical(a30, I);
end function;


function ProofLemma()
	K := Rationals();
	R1<a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22, a23, a30, a31, a32, a33, X> := PolynomialRing(K, [1 : i in [1..17]]);
	R<x, y, u, v> := PolynomialRing(R1, 4);
	f0 := a33*x^3*u^3+a32*x^3*u^2*v+a31*x^3*u*v^2+a30*x^3*v^3+a23*x^2*y*u^3+a22*x^2*y*u^2*v+a21*x^2*y*u*v^2+a20*x^2*y*v^3+a13*x*y^2*u^3+a12*x*y^2*u^2*v+a11*x*y^2*u*v^2+a10*x*y^2*v^3+a03*y^3*u^3+a02*y^3*u^2*v+a01*y^3*u*v^2+a00*y^3*v^3;
	MH := CoefficientMatrix(Transvectant(f0, f0, 2, 2));
	inv2 := Transvectant(f0, f0, 3, 3);
	I := Ideal([inv2, MH[1][1], MH[2][1], MH[3][1], MH[1][2], MH[2][2], MH[3][2], MH[1][3], MH[2][3], MH[3][3]]);
	"The invariants which come from J_{3,1} vanish:";
	s := Transvectant(f0, f0, 3, 1);
	"(J_{3,1}, J_{3,1})_4 = 0", IsInRadical(R1!Transvectant(s, s, 0, 4), I);
	"((J_{3,1}, J_{3,1})_2, J_{3,1})_4 = 0", IsInRadical(R1!Transvectant(Transvectant(s, s, 0, 2), s, 0, 4), I);
	"";
	"The invariants which come from J_{3,1} vanish:";
	s := Transvectant(f0, f0, 1, 3);
	"(J_{1,3}, J_{1,3})_4 = 0", IsInRadical(R1!Transvectant(s, s, 4, 0), I);
	"((J_{1,3}, J_{1,3})_2, J_{1,3})_4 = 0", IsInRadical(R1!Transvectant(Transvectant(s, s, 2, 0), s, 4, 0), I);
	"";
	"If we take into account that y^3 divides J_{1,3}:";
	liste_f0 := [a30*x^3*v^3+a22*x^2*y*u^2*v+a21*x^2*y*u*v^2+a20*x^2*y*v^3+a13*x*y^2*u^3+a12*x*y^2*u^2*v+a11*x*y^2*u*v^2+a10*x*y^2*v^3+a03*y^3*u^3+a02*y^3*u^2*v+a01*y^3*u*v^2+a00*y^3*v^3,
	 x^3*u*v^2+a22*x^2*y*u^2*v+a20*x^2*y*v^3+a13*x*y^2*u^3+a12*x*y^2*u^2*v+a11*x*y^2*u*v^2+a10*x*y^2*v^3+a03*y^3*u^3+a02*y^3*u^2*v+a01*y^3*u*v^2+a00*y^3*v^3, 
	 x^3*u^2*v+a30*x^3*v^3+a21*x^2*y*u*v^2+a20*x^2*y*v^3+a13*x*y^2*u^3+a12*x*y^2*u^2*v+a11*x*y^2*u*v^2+a10*x*y^2*v^3+a03*y^3*u^3+a02*y^3*u^2*v+a01*y^3*u*v^2+a00*y^3*v^3, 
	 a31*x^3*u*v^2+a30*x^3*v^3+x^2*y*u^3+a21*x^2*y*u*v^2+a20*x^2*y*v^3+a12*x*y^2*u^2*v+a11*x*y^2*u*v^2+a10*x*y^2*v^3+a03*y^3*u^3+a02*y^3*u^2*v+a01*y^3*u*v^2+a00*y^3*v^3, 
	 x^3*u^2*v+a31*x^3*u*v^2+a30*x^3*v^3+x^2*y*u^3+a21*x^2*y*u*v^2+a20*x^2*y*v^3+a12*x*y^2*u^2*v+a11*x*y^2*u*v^2+a10*x*y^2*v^3+a03*y^3*u^3+a02*y^3*u^2*v+a01*y^3*u*v^2+a00*y^3*v^3];
	for j in [1..5] do
		"Case " cat IntegerToString(j) cat":";"";
		f0 := liste_f0[j];
		Mat := CoefficientMatrix(f0);
		Mat;"";
		M := [R1!MonomialCoefficient(Transvectant(f0, f0, 1, 3),x^(4-i)*y^(i)) : i in [0..4]];
		MH := CoefficientMatrix(Transvectant(f0, f0, 2, 2));
		inv2 := Transvectant(f0, f0, 3, 3);
		I := Ideal([inv2, M[1], M[2], M[3], MH[1][1], MH[2][1], MH[3][1], MH[1][2], MH[2][2], MH[3][2], MH[1][3], MH[2][3], MH[3][3]]);
		"f must be of one of the following forms:";"";
		Gb := RadicalDecomposition(I);
		for bas in Gb do
			Matrix([[NormalForm(Mat[i][j], bas) : j in [1..4]] : i in [1..4]]);
			"";
		end for;
		"";"";
	end for;
	"The first subcase of case 5 is the only one which does not implies that f belongs to the nullcone. We do a suitable change of variables, and get:";"";
	f0 := liste_f0[5];
	M := [R1!MonomialCoefficient(Transvectant(f0, f0, 1, 3),x^(4-i)*y^(i)) : i in [0..4]];
	MH := CoefficientMatrix(Transvectant(f0, f0, 2, 2));
	inv2 := Transvectant(f0, f0, 3, 3);
	I := Ideal([inv2, M[1], M[2], M[3], MH[1][1], MH[2][1], MH[3][1], MH[1][2], MH[2][2], MH[3][2], MH[1][3], MH[2][3], MH[3][3]]);
	f1 := R!(Evaluate(f0, [x+a31/2*y, y, u-a31/2*v, v]));
	Gb := RadicalDecomposition(I);
	Matrice_f1 := CoefficientMatrix(f1);
	Matrix([[NormalForm(Matrice_f1[i][j], Gb[1]) : j in [1..4]] : i in [1..4]]);
	return "";
end function;
