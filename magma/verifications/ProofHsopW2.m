
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


function InvariantsHSOPW2(q);
	H := Transvectant(q, q, 1, 1);
	return [Transvectant(q, q, 2, 2 : invariant := true), Transvectant(q, H, 2, 2 : invariant := true), Transvectant(H, H, 2, 2 : invariant := true)];
end function;

/////////////////////////////////////////////
/////////////* HSOP for W2 */////////////////
/////////////////////////////////////////////

R1<b00, b01, b02, b10, b11, b12, b20, b21, b22> := PolynomialRing(Rationals(), [1 : i in [1..9]]);
R<x, y, u, v> := PolynomialRing(R1, 4);

"Case 1:";"";
	q := b20*x^2*v^2+b11*x*y*u*v+b10*x*y*v^2+b02*y^2*u^2+b01*y^2*u*v+b00*y^2*v^2;
	Mat := CoefficientMatrix(q);
	Mat;"";
	"q must be one of the following:";"";
	I := Ideal(InvariantsHSOPW2(q));
	Gb := RadicalDecomposition(I);
	for bas in Gb do
		Matrix([[NormalForm(Mat[i][j], bas) : j in [1..3]] : i in [1..3]]);"";
	end for;"";"";"";

"Case 2::";"";
	q := b20*x^2*v^2+x*y*u^2+b10*x*y*v^2+b01*y^2*u*v+b00*y^2*v^2;
	Mat := CoefficientMatrix(q);
	Mat;"";
	"q must be one of the following:";"";
	I := Ideal(InvariantsHSOPW2(q));
	Gb := RadicalDecomposition(I);
	for bas in Gb do
		Matrix([[NormalForm(Mat[i][j], bas) : j in [1..3]] : i in [1..3]]);"";
	end for;"";"";"";


"Case 3:";"";
	q := x^2*u*v+b20*x^2*v^2+x*y*u^2+b10*x*y*v^2+b01*y^2*u*v+b00*y^2*v^2;
	Mat := CoefficientMatrix(q);
	Mat;"";
	"q must be one of the following:";"";
	I := Ideal(InvariantsHSOPW2(q));
	Gb := RadicalDecomposition(I);
	for bas in Gb do
		Matrix([[NormalForm(Mat[i][j], bas) : j in [1..3]] : i in [1..3]]);"";
	end for;"";"";"";

	"In the first case, we do a suitable change of variables and get:";
		q1 := R!(Evaluate(q, [x+b20*y, y, u-b20*v, v]));
		Matrix_q1 := CoefficientMatrix(q1);
		Matrix([[NormalForm(Matrix_q1[i][j], Gb[1]) : j in [1..3]] : i in [1..3]]);"";

