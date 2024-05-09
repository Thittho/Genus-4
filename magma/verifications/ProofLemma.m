function CoefficientMatrix(f)
	P := Parent(f);
	R1 := CoefficientRing(P);
	
	if Rank(R1) eq 17 then
		R<a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22, a23, a30, a31, a32, a33, X> := CoefficientRing(P);
	elif Rank(R1) eq 9 then
		R<b00, b01, b02, b10, b11, b12, b20, b21, b22> := CoefficientRing(P);
	end if;

	m := Degree(Evaluate(f, [P.1, P.2, 1, 2]));	
	n := Degree(Evaluate(f, [1, 2, P.3, P.4]));
	M := [[R!MonomialCoefficient(f, (P.2)^i*(P.1)^(m-i)*(P.4)^j*(P.3)^(n-j)) : i in [0..m]] : j in [0..n]];
	return Matrix(M);
end function; 


/////////////////////////////////////////////////////////////////////////////
/* Proof that (f,f)_2 = (f,f)_3 = 0 implies f belongs to the nullcone of W3*/
/////////////////////////////////////////////////////////////////////////////


K := Rationals();
R1<a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22, a23, a30, a31, a32, a33, X> := PolynomialRing(K, [1 : i in [1..17]]);
R<x, y, u, v> := PolynomialRing(R1, 4);

f0 := a33*x^3*u^3+a32*x^3*u^2*v+a31*x^3*u*v^2+a30*x^3*v^3+a23*x^2*y*u^3+a22*x^2*y*u^2*v+a21*x^2*y*u*v^2+a20*x^2*y*v^3+a13*x*y^2*u^3+a12*x*y^2*u^2*v+a11*x*y^2*u*v^2+a10*x*y^2*v^3+a03*y^3*u^3+a02*y^3*u^2*v+a01*y^3*u*v^2+a00*y^3*v^3;
MH := CoefficientMatrix(Transvectant(f0, f0, 2, 2));
inv2 := Transvectant(f0, f0, 3, 3 : invariant := true);
I := Ideal([inv2, MH[1][1], MH[2][1], MH[3][1], MH[1][2], MH[2][2], MH[3][2], MH[1][3], MH[2][3], MH[3][3]]);

"The invariants of J_{1,3} seen as a binary quartic vanish:";
s := Transvectant(f0, f0, 1, 3);
"(J_{1,3}, J_{1,3})_4 = 0", IsInRadical(R1!Transvectant(s, s, 4, 0 : invariant := true), I);
"((J_{1,3}, J_{1,3})_2, J_{1,3})_4 = 0", IsInRadical(R1!Transvectant(Transvectant(s, s, 2, 0), s, 4, 0 : invariant := true), I);"";

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
		inv2 := Transvectant(f0, f0, 3, 3 : invariant := true);
		I := Ideal([inv2, M[1], M[2], M[3], MH[1][1], MH[2][1], MH[3][1], MH[1][2], MH[2][2], MH[3][2], MH[1][3], MH[2][3], MH[3][3]]);

		"f must be of one of the following forms:";"";
		Gb := RadicalDecomposition(I);
		for bas in Gb do
			Matrix([[NormalForm(Mat[i][j], bas) : j in [1..4]] : i in [1..4]]);"";
		end for;"";"";
	end for;

	"The first subcase of case 5 is the only one which does not implies that f belongs to the nullcone. We do a suitable change of variables, and get:";"";
		f0 := liste_f0[5];
		M := [R1!MonomialCoefficient(Transvectant(f0, f0, 1, 3),x^(4-i)*y^(i)) : i in [0..4]];
		MH := CoefficientMatrix(Transvectant(f0, f0, 2, 2));
		inv2 := Transvectant(f0, f0, 3, 3 : invariant := true);
		I := Ideal([inv2, M[1], M[2], M[3], MH[1][1], MH[2][1], MH[3][1], MH[1][2], MH[2][2], MH[3][2], MH[1][3], MH[2][3], MH[3][3]]);
		f1 := R!(Evaluate(f0, [x+a31/2*y, y, u-a31/2*v, v]));
		Gb := RadicalDecomposition(I);
		Matrix_f1 := CoefficientMatrix(f1);
		Matrix([[NormalForm(Matrix_f1[i][j], Gb[1]) : j in [1..4]] : i in [1..4]]);"";"";

