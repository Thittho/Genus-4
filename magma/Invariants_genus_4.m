//FUNCTIONS TO DETERMINE THE CUBIC IN THE BASIS IN WHICH Q=XT-YZ (the order of the variables is X,Y,Z,T)

//given a quadric and a field of definition of the quadric, returns a field and a matrix defined on that field which transforms the quadric into XT-YZ

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

function InvariantsGenus4Curves(L, f)
	return [Evaluation(L[i], f) : i in [1..#L]];
end function;

function CoefficientsMatrix(f)
	P := Parent(f);
	R<a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22, a23, a30, a31, a32, a33, X> := CoefficientRing(P);
	m := Degree(Evaluate(f, [P.1, P.2, 1, 2]));	
	n := Degree(Evaluate(f, [1, 2, P.3, P.4]));
	M := [[R!MonomialCoefficient(f, (P.2)^i*(P.1)^(m-i)*(P.4)^j*(P.3)^(n-j)) : i in [0..m]] : j in [0..n]];
	return Matrix(M);
end function; 

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
	Q_mat := QuadraticFormToMatrix(Q);
	K := BaseRing(Parent(Q));
	M1 := KMatrixSpace(K,4,4);
	D, P, t := OrthogonalizeGram(Q_mat);
	if t ne 4 then
		return "The quadric is not of rank 3 or 4"; //will be changed later to include rank 3 quadrics
	else
		L := [-D[4][4]/D[1][1], -D[3][3]/D[2][2]];
		if not Category(K) eq FldCom then //we take a bigger field to be sure that the change of variable is well defined, and AlgebraicClosure(ComplexField()) returns an error
			S := AlgebraicClosure(K);
			//[[Sqrt(S!L[i]), S!L[i]] : i in [1..2]]; //this is useful to know which square roots we are adding
		else
			S := K;
		end if;
		M2 := KMatrixSpace(S,4,4);
		P := ChangeRing(P, S);
		P_fin := (M2![1/(2*D[1][1]),0,0,1/(2*D[1][1]*Sqrt(S!L[1])),0,-1/(2*D[2][2]),-1/(2*D[2][2]*Sqrt(S!L[2])),0,0,1/2,-1/(2*Sqrt(S!L[2])),0,1/2,0,0,-1/(2*Sqrt(S!L[1]))])*P;
		return P_fin;
	end if;
end function;


//given a form and a change of variables (given as a matrix), returns the form after the change of variables
function ChangeOfBasis(C, P)
	R := ChangeRing(Parent(C), Parent(P[1][1]));
	C := R!C;
	P := Transpose(Matrix([[R!P[i][j] : j in [1..NumberOfColumns(P)]] : i in [1..NumberOfRows(P)]]));
	Y := ElementToSequence(P*Matrix([[R.i] : i in [1..Rank(R)]]));
	return Evaluate(C, Y);
end function;
	
function CubicNewBasis(Q, C)
	R := Parent(C);
	P := NewBasis(Q);
	R := ChangeRing(R, BaseRing(Parent(P)));
	C1 := R!C;
	return ChangeOfBasis(C1, P);
end function;


function InvariantsGenus4Curves_test(f)
	//Covariants
	//Degree 2
	f2 := Transvectant(f, f, 0, 0);
	Jac := Transvectant(f, f, 1, 1);
	H := Transvectant(f, f, 2, 2);

	//Degree 3
	C31 := Transvectant(Jac, f, 3, 3);
	C33 := Transvectant(Jac, f, 2, 2);
	C35 := Transvectant(Jac, f, 1, 1);
	C37 := Transvectant(Jac, f, 0, 0);

	C31H := Transvectant(H, f, 2, 2);
	C33H := Transvectant(H, f, 1, 1);
	C35H := Transvectant(H, f, 0, 0);

	f3 := Transvectant(f2, f, 0, 0);
	C37f := Transvectant(f2, f, 1, 1);
	C35f := Transvectant(f2, f, 2, 2);
	C33f := Transvectant(f2, f, 3, 3);

	//Degree 4
	CH := Transvectant(H, H, 1, 1);
	C42H := Transvectant(C31H, f, 1, 1);
	C44H := Transvectant(C31H, f, 0, 0);
	C44H1 := Transvectant(C33H, f, 1, 1);
	C42H1 := Transvectant(C33H, f, 2, 2);
	C42H2 := Transvectant(C35H, f, 3, 3);
	C46H := Transvectant(C33H, f, 0, 0);

	C42 := Transvectant(C33, f, 2, 2);
	C421 := Transvectant(C31, f, 1, 1);
	C44 := Transvectant(C33, f, 1, 1);
	C441 := Transvectant(C35, f, 2, 2);
	C46 := Transvectant(f3, f, 3, 3);
	C48 := Transvectant(f3, f, 2, 2);
	C48f := Transvectant(C35f, f, 0, 0);
	C46f := Transvectant(C37f, f, 2, 2);
	C44f := Transvectant(C33f, f, 1, 1);
	C44f2 := Transvectant(C37f, f, 3, 3);

	f4 := Transvectant(f3, f, 0, 0);

	//Degree 5
	C51H := Transvectant(C42H, f, 2, 2);
	C53H := Transvectant(C42H, f, 1, 1);
	C55H := Transvectant(C44H, f, 1, 1);
	C53H1 := Transvectant(C42H1, f, 1, 1);

	C55f := Transvectant(C46f, f, 2, 2);
	C513f := Transvectant(f4, f, 1, 1);

	C55 := Transvectant(C42H, f, 0, 0);
	C551 := Transvectant(C42, f, 0, 0);

	C57 := Transvectant(C441, f, 0, 0);

	//Degree 6
	C62H := Transvectant(C53H, f, 2, 2);
	C62H1 := Transvectant(C53H1, f, 2, 2);
	C62H2 := Transvectant(C51H, f, 1, 1);
	C66H := Transvectant(C55H, f, 1, 1);

	//Degree 7
	C71H := Transvectant(C62H, f, 2, 2);
	C73H1 := Transvectant(C62H1, f, 1, 1);
	C79H := Transvectant(C66H, f, 0, 0);

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
	invHSOP := [J2, J4H, J4, J6H, J61, J8H, J81, J101, J121, J141];

	//Degree 6
	J62 := Transvectant(Transvectant(Transvectant(f3, f, 3, 3), f, 3, 3), f, 3, 3);
	inv6 := [J62];

	//Degree 8
	J82 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C35H, f, 2, 2), f, 0, 0), f, 2, 2), f, 3, 3), f, 3, 3);
	J83 := Transvectant(Transvectant(C66H, f, 3, 3), f, 3, 3);
	inv8 := [J82, J83];
	
	//Degree 10
	J102 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C42H2, f, 0, 0), f, 0, 0), f, 2, 2), f, 3, 3), f, 2, 2), f, 3, 3);
	J103 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C48f, f, 2, 2), f, 1, 1), f, 1, 1), f, 3, 3), f, 3, 3), f, 3, 3);
	J104 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C48f, f, 3, 3), f, 2, 2), f, 3, 3), f, 1, 1), f, 1, 1), f, 3, 3);
	J105 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C35, f, 1, 1), f, 3, 3), f, 0, 0), f, 0, 0), f, 3, 3), f, 3, 3), f, 3, 3);
	J106 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C44H1, f, 3, 3), f, 0, 0), f, 1, 1), f, 2, 2), f, 2, 2), f, 3, 3);
	J107 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C42H2, f, 1, 1), f, 2, 2), f, 2, 2), f, 0, 0), f, 2, 2), f, 3, 3);
	inv10 := [J102, J103, J104, J105, J106, J107];

	//Degree 12
	J122 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C44f, f, 3, 3), f, 0, 0), f, 3, 3), f, 0, 0), f, 1, 1), f, 2, 2), f, 2, 2), f, 3, 3); 
	J123 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C37f, f, 1, 1), f, 2, 2), f, 2, 2), f, 0, 0), f, 1, 1), f, 3, 3), f, 3, 3), f, 2, 2), f, 3, 3); 
	J124 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C55f, f, 3, 3), f, 1, 1), f, 0, 0), f, 3, 3), f, 1, 1), f, 2, 2), f, 3, 3);
	J125 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C513f, f, 3, 3), f, 2, 2), f, 1, 1), f, 2, 2), f, 3, 3), f, 3, 3), f, 3, 3);
	J126 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C44, f, 3, 3), f, 1, 1), f, 0, 0), f, 1, 1), f, 2, 2), f, 1, 1), f, 3, 3), f, 3, 3);
	J127 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C44f, f, 0, 0), f, 1, 1), f, 1, 1), f, 2, 2), f, 1, 1), f, 3, 3), f, 3, 3), f, 3, 3);
	J128 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(f4, f, 2, 2), f, 2, 2), f, 1, 1), f, 1, 1), f, 3, 3), f, 3, 3), f, 3, 3), f, 3, 3);
	J129 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C48f, f, 0, 0), f, 3, 3), f, 2, 2), f, 2, 2), f, 3, 3), f, 0, 0), f, 3, 3), f, 3, 3);
	J1210 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C79H, f, 1, 1), f, 3, 3), f, 3, 3), f, 2, 2), f, 3, 3);
	inv12 := [J122, J123, J124, J125, J126, J127, J128, J129, J1210];

	//Degree 14
	J142 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C44H1, f, 0, 0), f, 2, 2), f, 0, 0), f, 2, 2), f, 0, 0), f, 2, 2), f, 2, 2), f, 3, 3), f, 3, 3), f, 3, 3);
	J143 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C48, f, 1, 1), f, 2, 2), f, 1, 1), f, 0, 0), f, 2, 2), f, 2, 2), f, 2, 2), f, 3, 3), f, 3, 3), f, 3, 3);
	J144 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C44H, f, 0, 0), f, 3, 3), f, 2, 2), f, 2, 2), f, 2, 2), f, 0, 0), f, 0, 0), f, 2, 2), f, 3, 3), f, 3, 3);
	J145 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C35, f, 3, 3), f, 2, 2), f, 0, 0), f, 1, 1), f, 1, 1), f, 3, 3), f, 0, 0), f, 1, 1), f, 3, 3), f, 2, 2), f, 3, 3);
	J146 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C44f2, f, 1, 1), f, 2, 2), f, 0, 0), f, 3, 3), f, 0, 0), f, 3, 3), f, 3, 3), f, 0, 0), f, 2, 2), f, 3, 3);
	J147 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C44, f, 1, 1), f, 1, 1), f, 0, 0), f, 1, 1), f, 1, 1), f, 2, 2), f, 3, 3), f, 3, 3), f, 2, 2), f, 3, 3);
	J148 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C44f2, f, 3, 3), f, 1, 1), f, 0, 0), f, 1, 1), f, 0, 0), f, 1, 1), f, 2, 2), f, 3, 3), f, 3, 3), f, 3, 3);
	J149 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C35f, f, 1, 1), f, 0, 0), f, 0, 0), f, 2, 2), f, 3, 3), f, 2, 2), f, 3, 3), f, 1, 1), f, 1, 1), f, 3, 3), f, 3, 3);
	J1410 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C37, f, 0, 0), f, 3, 3), f, 2, 2), f, 0, 0), f, 2, 2), f, 0, 0), f, 1, 1), f, 3, 3), f, 3, 3), f, 3, 3), f, 3, 3);
	J1411 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C513f, f, 0, 0), f, 1, 1), f, 2, 2), f, 2, 2), f, 3, 3), f, 3, 3), f, 3, 3), f, 3, 3), f, 3, 3);
	J1412 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C55, f, 2, 2), f, 3, 3), f, 1, 1), f, 0, 0), f, 0, 0), f, 3, 3), f, 1, 1), f, 3, 3), f, 3, 3);
	J1413 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C33f, f, 0, 0), f, 0, 0), f, 3, 3), f, 0, 0), f, 1, 1), f, 2, 2), f, 3, 3), f, 2, 2), f, 2, 2), f, 2, 2), f, 3, 3);
	inv14 := [J142, J143, J144, J145, J146, J147, J148, J149, J1410, J1411, J1412, J1413];

	//Degree 16
	J161 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C551, f, 1, 1), f, 2, 2), f, 2, 2), f, 0, 0), f, 1, 1), f, 0, 0), f, 3, 3), f, 3, 3), f, 2, 2), f, 2, 2), f, 3, 3);
	J162 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C44f2, f, 0, 0), f, 3, 3), f, 1, 1), f, 1, 1), f, 1,1), f, 1, 1), f, 2, 2), f, 1, 1), f, 3, 3), f, 2, 2), f, 2, 2), f, 3, 3);
	J163 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C55, f, 0, 0), f, 1, 1), f, 0, 0), f, 2, 2), f, 2, 2), f, 0, 0), f, 2, 2), f, 3, 3), f, 3, 3), f, 3, 3), f, 3, 3);
	J164 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C46H, f, 1, 1), f, 3, 3), f, 2, 2), f, 2, 2), f, 0,0), f, 2, 2), f, 3, 3), f, 0, 0), f, 0, 0), f, 3, 3), f, 2, 2), f, 3, 3);
	J165 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C44H, f, 3, 3), f, 1, 1), f, 1, 1), f, 0, 0), f, 2,2), f, 2, 2), f, 3, 3), f, 1, 1), f, 0, 0), f, 2, 2), f, 2, 2), f, 3, 3);
	J166 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C44H, f, 2, 2), f, 1, 1), f, 3, 3), f, 0, 0), f, 3,3), f, 1, 1), f, 0, 0), f, 0, 0), f, 1, 1), f, 3, 3), f, 3, 3), f, 3, 3);
	J167 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C35, f, 0, 0), f, 3, 3), f, 1, 1), f,1, 1), f, 2, 2), f, 3, 3), f, 2, 2), f, 2, 2), f, 0, 0), f, 3, 3), f, 0, 0), f, 2, 2), f, 3, 3);
	J168 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C33, f, 0, 0), f, 0, 0), f, 0, 0), f,0, 0), f, 2, 2), f, 1, 1), f, 0, 0), f, 3, 3), f, 3, 3), f, 3, 3), f, 3, 3), f, 3, 3), f, 3, 3);
	J169 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C441, f, 1, 1), f, 1, 1), f, 0, 0), f, 3, 3), f, 1,1), f, 0, 0), f, 1, 1), f, 2, 2), f, 2, 2), f, 3, 3), f, 3, 3), f, 3, 3);
	J1610 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C44H1, f, 2, 2), f, 1, 1), f, 1, 1), f, 1, 1), f, 1,1), f, 3, 3), f, 1, 1), f, 0, 0), f, 3, 3), f, 2, 2), f, 2, 2), f, 3, 3);
	J1611 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C37f, f, 0, 0), f, 0, 0), f, 1, 1), f,0, 0), f, 2, 2), f, 2, 2), f, 2, 2), f, 1, 1), f, 3, 3), f, 3, 3), f, 3, 3), f, 3, 3), f, 3, 3);
	J1612 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C57, f, 1, 1), f, 3, 3), f, 1, 1), f, 1, 1), f, 1, 1), f, 3, 3), f, 1, 1), f, 0, 0), f, 3, 3), f, 3, 3), f, 3, 3);
	J1613 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C421, f, 0, 0), f, 1, 1), f, 0, 0), f, 0, 0), f, 2,2), f, 3, 3), f, 1, 1), f, 0, 0), f, 3, 3), f, 3, 3), f, 3, 3), f, 3, 3);
	J1614 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C62H2, f, 0, 0), f, 1, 1), f, 2, 2), f, 2, 2), f, 1, 1), f, 3, 3), f, 2, 2), f, 1, 1), f, 1, 1), f, 3, 3);
	inv16 := [J161, J162, J163, J164, J165, J166, J167, J168, J169, J1610, J1611, J1612, J1613, J1614];

	//Degree 18
	J181 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C71H, f, 0, 0), f, 0, 0), f, 0, 0), f, 2, 2), f, 3, 3), f, 0, 0), f, 3, 3), f, 1, 1), f, 3, 3), f, 2, 2), f, 3, 3);
	J182 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C55f, f, 0, 0), f, 0, 0), f, 0, 0), f,0, 0), f, 3, 3), f, 0, 0), f, 3, 3), f, 3, 3), f, 2, 2), f, 2, 2), f, 3, 3), f, 3, 3), f, 3, 3);
	J183 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C79H, f, 3, 3), f, 1, 1), f, 1, 1), f, 1, 1), f, 1, 1), f, 2, 2), f, 1, 1), f, 2, 2), f, 3, 3), f, 3, 3), f, 3, 3);
	J184 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(f3, f, 1, 1), f, 2, 2), f, 3, 3), f, 1, 1), f, 3, 3), f, 1, 1), f, 0, 0), f, 1, 1), f, 3, 3), f, 2, 2), f, 1, 1), f, 0, 0), f, 3, 3), f, 3, 3), f, 3, 3);
	J185 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C57, f, 0, 0), f, 2, 2), f, 1, 1), f,2, 2), f, 3, 3), f, 1, 1), f, 3, 3), f, 3, 3), f, 0, 0), f, 0, 0), f, 2, 2), f, 3, 3), f, 3, 3);
	J186 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C46H, f, 2, 2), f, 0, 0),f, 1, 1), f, 3, 3), f, 0, 0), f, 1, 1), f, 2, 2), f, 3, 3), f, 2, 2), f, 2, 2), f, 1, 1), f, 3, 3), f, 1, 1), f, 3, 3);
	J187 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C551, f, 0, 0), f, 0, 0), f, 2, 2), f,2, 2), f, 2, 2), f, 3, 3), f, 1, 1), f, 0, 0), f, 1, 1), f, 3, 3), f, 2, 2), f, 3, 3), f, 3, 3);
	J188 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C31, f, 0, 0), f, 0, 0), f, 1, 1), f, 1, 1), f, 0, 0), f, 3, 3), f, 2, 2), f, 3, 3), f, 2, 2), f, 3, 3), f, 1, 1), f, 2, 2), f, 1, 1), f, 1, 1), f, 3, 3);
	J189 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C35H, f, 2, 2), f, 2, 2), f, 0, 0), f, 2, 2), f, 3, 3), f, 1, 1), f, 0, 0), f, 3, 3), f, 2, 2), f, 0, 0), f, 2, 2), f, 3, 3), f, 0, 0), f, 2, 2), f, 3, 3);
	J1810 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C421, f, 0, 0), f, 2, 2),f, 1, 1), f, 1, 1), f, 1, 1), f, 1, 1), f, 2, 2), f, 2, 2), f, 3, 3), f, 1, 1), f, 0, 0), f, 3, 3), f, 2, 2), f, 3, 3);
	J1811 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C48, f, 0, 0), f, 0, 0),f, 3, 3), f, 0, 0), f, 1, 1), f, 3, 3), f, 3, 3), f, 1, 1), f, 1, 1), f, 3, 3), f, 1, 1), f, 3, 3), f, 3, 3), f, 3, 3);
	inv18 := [J181, J182, J183, J184, J185, J186, J187, J188, J189, J1810, J1811];

	return invHSOP cat inv6 cat inv8 cat inv10 cat inv12 cat inv14 cat inv16 cat inv18;
end function;


d<f> := PolynomialRing(Rationals(), 1); //only to write "f" in the transvectants, I don't know how else to define a variable

list_invariants := [*[*f, f, 3, 3*], [*[*f, f, 2, 2*], [*f, f, 2, 2*], 2, 2*], [*[*[*f, f, 1, 1*], f, 2, 2*], f, 3, 3*], [*[*[*f, f, 2, 2*], [*f, f, 2, 2*], 1, 1 *], [*f, f, 2, 2 *], 2, 2 *], [*[*[*[*[*f, f, 2, 2 *], f, 2, 2 *], f, 1, 1 *], f, 1, 1 *], f, 3, 3 *], [*[*[*f, f, 2, 2*], [*f, f, 2, 2*], 1, 1 *], [*[*f, f, 2, 2*], [*f, f, 2, 2*], 1, 1 *], 2, 2 *], [* [* [* [* [* [* [* f, f, 2, 2 *], f, 1, 1 *], f, 2, 2 *], f, 1, 1 *], f, 2, 2 *], f, 1, 1 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* f, f, 2, 2 *], f, 2, 2 *], f, 1, 1 *], f, 1, 1 *], f, 2, 2 *], f, 2, 2 *], f, 1, 1 *], f, 1, 1 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* f, f, 2, 2 *], f, 1, 1 *], f, 2, 2 *], f, 1, 1 *], f, 2, 2 *], f, 1, 1 *], f, 1, 1 *], f, 2, 2 *], f, 0, 0 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* f, f, 2, 2 *], f, 2, 2 *], f, 1, 1 *], f, 2, 2 *], f, 1, 1 *], f, 1, 1 *], f, 2, 2 *], f, 2, 2 *], f, 1, 1 *], f, 2, 2 *], [* f, f, 2, 2 *], 0, 0 *], f, 3, 3 *], [* [* [* [* [* f, f, 0, 0 *], f, 0, 0 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* f, f, 2, 2 *], f, 0, 0 *], f, 2, 2 *], f, 0, 0 *], f, 2, 2 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* f, f, 2, 2 *], f, 2, 2 *], f, 0, 0 *], f, 1, 1 *], f, 1, 1 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* f, f, 2, 2 *], f, 0, 0 *], f, 3, 3 *], f, 0, 0 *], f, 0, 0 *], f, 2, 2 *], f, 3, 3 *], f, 2, 2 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* f, f, 0, 0 *], f, 2, 2 *], f, 0, 0 *], f, 2, 2 *], f, 1, 1 *], f, 1, 1 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* f, f, 0, 0 *], f, 2, 2 *], f, 0, 0 *], f, 3, 3 *], f, 2, 2 *], f, 3, 3 *], f, 1, 1 *], f, 1, 1 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* f, f, 1, 1 *], f, 1, 1 *], f, 1, 1 *], f, 3, 3 *], f, 0, 0 *], f, 0, 0 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* f, f, 2, 2 *], f, 1, 1 *], f, 1, 1 *], f, 3, 3 *], f, 0, 0 *], f, 1, 1 *], f, 2, 2 *], f, 2, 2 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* f, f, 2, 2 *], f, 0, 0 *], f, 3, 3 *], f, 1, 1 *], f, 2, 2 *], f, 2, 2 *], f, 0, 0 *], f, 2, 2 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* f, f, 0, 0 *], f, 3, 3 *], f, 1, 1 *], f, 3, 3 *], f, 0, 0 *], f, 3, 3 *], f, 0, 0 *], f, 1, 1 *], f, 2, 2 *], f, 2, 2 *], f, 3, 3 *], [*[*[* [* [* [* [* [* [* [* [* f, f, 0, 0 *], f, 1, 1 *], f, 1, 1 *], f, 2, 2 *], f, 2, 2 *], f, 0, 0 *], f, 1, 1 *], f, 3, 3 *], f, 3, 3 *], f, 2, 2 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* f, f, 0, 0 *], f, 1, 1 *], f, 2, 2 *], f, 2, 2 *], f, 3, 3 *], f, 1, 1 *], f, 0, 0 *], f, 3, 3 *], f, 1, 1 *], f, 2, 2 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* f, f, 0, 0 *], f, 0, 0 *], f, 0, 0 *], f, 1, 1 *], f, 3, 3 *], f, 2, 2 *], f, 1, 1 *], f, 2, 2 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* f, f, 1, 1 *], f, 2, 2 *], f, 1, 1 *], f, 3, 3 *], f, 1, 1 *], f, 0, 0 *], f, 1, 1 *], f, 2, 2 *], f, 1, 1 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* f, f, 0, 0 *], f, 3, 3 *], f, 1, 1 *], f, 0, 0 *], f, 1, 1 *], f, 1, 1 *], f, 2, 2 *], f, 1, 1 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* f, f, 0, 0 *], f, 0, 0 *], f, 0, 0 *], f, 2, 2 *], f, 2, 2 *], f, 1, 1 *], f, 1, 1 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* f, f, 0, 0 *], f, 2, 2 *], f, 0, 0 *], f, 0, 0 *], f, 3, 3 *], f, 2, 2 *], f, 2, 2 *], f, 3, 3 *], f, 0, 0 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* f, f, 2, 2 *], f, 2, 2 *], f, 0, 0 *], f, 1, 1 *], f, 1, 1 *], f, 0, 0 *], f, 1, 1 *], f, 3, 3 *], f, 3, 3 *], f, 2, 2 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 2, 2 *], f, 1, 1 *], f, 1, 1 *], f, 0, 0 *], f, 2, 2 *], f, 0, 0 *], f, 2, 2 *], f, 0, 0 *], f, 2, 2 *], f, 2, 2 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 0, 0 *], f, 0, 0 *], f, 2, 2 *], f, 1, 1 *], f, 2, 2 *], f, 1, 1 *], f, 0, 0 *], f, 2, 2 *], f, 2, 2 *], f, 2, 2 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 2, 2 *], f, 2, 2 *], f, 0, 0 *], f, 0, 0 *], f, 3, 3 *], f, 2, 2 *], f, 2, 2 *], f, 2, 2 *], f, 0, 0 *], f, 0, 0 *], f, 2, 2 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 1, 1 *], f, 1, 1 *], f, 3, 3 *], f, 2, 2 *], f, 0, 0 *], f, 1, 1 *], f, 1, 1 *], f, 3, 3 *], f, 0, 0 *], f, 1, 1 *], f, 3, 3 *], f, 2, 2 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 0, 0 *], f, 1, 1 *], f, 3, 3 *], f, 1, 1 *], f, 2, 2 *], f, 0, 0 *], f, 3, 3 *], f, 0, 0 *], f, 3, 3 *], f, 3, 3 *], f, 0, 0 *], f, 2, 2 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 1, 1 *], f, 2, 2 *], f, 1, 1 *], f, 1, 1 *], f, 1, 1 *], f, 0, 0 *], f, 1, 1 *], f, 1, 1 *], f, 2, 2 *], f, 3, 3 *], f, 3, 3 *], f, 2, 2 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 0, 0 *], f, 1, 1 *], f, 3, 3 *], f, 3, 3 *], f, 1, 1 *], f, 0, 0 *], f, 1, 1 *], f, 0, 0 *], f, 1, 1 *], f, 2, 2 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 0, 0 *], f, 2, 2 *], f, 1, 1 *], f, 0, 0 *], f, 0, 0 *], f, 2, 2 *], f, 3, 3 *], f, 2, 2 *], f, 3, 3 *], f, 1, 1 *], f, 1, 1 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 1, 1 *], f, 0, 0 *], f, 0, 0 *], f, 3, 3 *], f, 2, 2 *], f, 0, 0 *], f, 2, 2 *], f, 0, 0 *], f, 1, 1 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 0, 0 *], f, 0, 0 *], f, 0, 0 *], f, 1, 1 *], f, 0, 0 *], f, 1, 1 *], f, 2, 2 *], f, 2, 2 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 2, 2 *], f, 2, 2 *], f, 1, 1 *], f, 0, 0 *], f, 2, 2 *], f, 3, 3 *], f, 1, 1 *], f, 0, 0 *], f, 0, 0 *], f, 3, 3 *], f, 1, 1 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 0, 0 *], f, 3, 3 *], f, 0, 0 *], f, 0, 0 *], f, 3, 3 *], f, 0, 0 *], f, 1, 1 *], f, 2, 2 *], f, 3, 3 *], f, 2, 2 *], f, 2, 2 *], f, 2, 2 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 1, 1 *], f, 2, 2 *], f, 2, 2 *], f, 0, 0 *], f, 1, 1 *], f, 2, 2 *], f, 2, 2 *], f, 0, 0 *], f, 1, 1 *], f, 0, 0 *], f, 3, 3 *], f, 3, 3 *], f, 2, 2 *], f, 2, 2 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 0, 0 *], f, 1, 1 *], f, 3, 3 *], f, 0, 0 *], f, 3, 3 *], f, 1, 1 *], f, 1, 1 *], f, 1, 1 *], f, 1, 1 *], f, 2, 2 *], f, 1, 1 *], f, 3, 3 *], f, 2, 2 *], f, 2, 2 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 2, 2 *], f, 2, 2 *], f, 1, 1 *], f, 0, 0 *], f, 0, 0 *], f, 1, 1 *], f, 0, 0 *], f, 2, 2 *], f, 2, 2 *], f, 0, 0 *], f, 2, 2 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 2, 2 *], f, 1, 1 *], f, 0, 0 *], f, 1, 1 *], f, 3, 3 *], f, 2, 2 *], f, 2, 2 *], f, 0, 0 *], f, 2, 2 *], f, 3, 3 *], f, 0, 0 *], f, 0, 0 *], f, 3, 3 *], f, 2, 2 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 2, 2 *], f, 2, 2 *], f, 0, 0 *], f, 3, 3 *], f, 1, 1 *], f, 1, 1 *], f, 0, 0 *], f, 2, 2 *], f, 2, 2 *], f, 3, 3 *], f, 1, 1 *], f, 0, 0 *], f, 2, 2 *], f, 2, 2 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 2, 2 *], f, 2, 2 *], f, 0, 0 *], f, 2, 2 *], f, 1, 1 *], f, 3, 3 *], f, 0, 0 *], f, 3, 3 *], f, 1, 1 *], f, 0, 0 *], f, 0, 0 *], f, 1, 1 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 1, 1 *], f, 1, 1 *], f, 0, 0 *], f, 3, 3 *], f, 1, 1 *], f, 1, 1 *], f, 2, 2 *], f, 3, 3 *], f, 2, 2 *], f, 2, 2 *], f, 0, 0 *], f, 3, 3 *], f, 0, 0 *], f, 2, 2 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 1, 1 *], f, 2, 2 *], f, 0, 0 *], f, 0, 0 *], f, 0, 0 *], f, 0, 0 *], f, 2, 2 *], f, 1, 1 *], f, 0, 0 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 1, 1 *], f, 1, 1 *], f, 2, 2 *], f, 1, 1 *], f, 1, 1 *], f, 0, 0 *], f, 3, 3 *], f, 1, 1 *], f, 0, 0 *], f, 1, 1 *], f, 2, 2 *], f, 2, 2 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 2, 2 *], f, 1, 1 *], f, 1, 1 *], f, 2, 2 *], f, 1, 1 *], f, 1, 1 *], f, 1, 1 *], f, 1, 1 *], f, 3, 3 *], f, 1, 1 *], f, 0, 0 *], f, 3, 3 *], f, 2, 2 *], f, 2, 2 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 0, 0 *], f, 1, 1 *], f, 0, 0 *], f, 0, 0 *], f, 1, 1 *], f, 0, 0 *], f, 2, 2 *], f, 2, 2 *], f, 2, 2 *], f, 1, 1 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 1, 1 *], f, 1, 1 *], f, 2, 2 *], f, 0, 0 *], f, 1, 1 *], f, 3, 3 *], f, 1, 1 *], f, 1, 1 *], f, 1, 1 *], f, 3, 3 *], f, 1, 1 *], f, 0, 0 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 1, 1 *], f, 3, 3 *], f, 1, 1 *], f, 0, 0 *], f, 1, 1 *], f, 0, 0 *], f, 0, 0 *], f, 2, 2 *], f, 3, 3 *], f, 1, 1 *], f, 0, 0 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 2, 2 *], f, 2, 2 *], f, 1, 1 *], f, 2, 2 *], f, 1, 1 *], f, 0, 0 *], f, 1, 1 *], f, 2, 2 *], f, 2, 2 *], f, 1, 1 *], f, 3, 3 *], f, 2, 2 *], f, 1, 1 *], f, 1, 1 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 2, 2 *], f, 2, 2 *], f, 1, 1 *], f, 1, 1 *], f, 2, 2 *], f, 2, 2 *], f, 0, 0 *], f, 0, 0 *], f, 0, 0 *], f, 2, 2 *], f, 3, 3 *], f, 0, 0 *], f, 3, 3 *], f, 1, 1 *], f, 3, 3 *], f, 2, 2 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 0, 0 *], f, 1, 1 *], f, 2, 2 *], f, 2, 2 *], f, 0, 0 *], f, 0, 0 *], f, 0, 0 *], f, 0, 0 *], f, 3, 3 *], f, 0, 0 *], f, 3, 3 *], f, 3, 3 *], f, 2, 2 *], f, 2, 2 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 2, 2 *], f, 2, 2 *], f, 0, 0 *], f, 1, 1 *], f, 1, 1 *], f, 0, 0 *], f, 3, 3 *], f, 1, 1 *], f, 1, 1 *], f, 1, 1 *], f, 1, 1 *], f, 2, 2 *], f, 1, 1 *], f, 2, 2 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 0, 0 *], f, 0, 0 *], f, 1, 1 *], f, 2, 2 *], f, 3, 3 *], f, 1, 1 *], f, 3, 3 *], f, 1, 1 *], f, 0, 0 *], f, 1, 1 *], f, 3, 3 *], f, 2, 2 *], f, 1, 1 *], f, 0, 0 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 1, 1 *], f, 1, 1 *], f, 2, 2 *], f, 0, 0 *], f, 0, 0 *], f, 2, 2 *], f, 1, 1 *], f, 2, 2 *], f, 3, 3 *], f, 1, 1 *], f, 3, 3 *], f, 3, 3 *], f, 0, 0 *], f, 0, 0 *], f, 2, 2 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 2, 2 *], f, 1, 1 *], f, 0, 0 *], f, 2, 2 *], f, 0, 0 *], f, 1, 1 *], f, 3, 3 *], f, 0, 0 *], f, 1, 1 *], f, 2, 2 *], f, 3, 3 *], f, 2, 2 *], f, 2, 2 *], f, 1, 1 *], f, 3, 3 *], f, 1, 1 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 1, 1 *], f, 2, 2 *], f, 2, 2 *], f, 0, 0 *], f, 0, 0 *], f, 0, 0 *], f, 2, 2 *], f, 2, 2 *], f, 2, 2 *], f, 3, 3 *], f, 1, 1 *], f, 0, 0 *], f, 1, 1 *], f, 3, 3 *], f, 2, 2 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 1, 1 *], f, 3, 3 *], f, 0, 0 *], f, 0, 0 *], f, 1, 1 *], f, 1, 1 *], f, 0, 0 *], f, 3, 3 *], f, 2, 2 *], f, 3, 3 *], f, 2, 2 *], f, 3, 3 *], f, 1, 1 *], f, 2, 2 *], f, 1, 1 *], f, 1, 1 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 2, 2 *], f, 0, 0 *], f, 2, 2 *], f, 2, 2 *], f, 0, 0 *], f, 2, 2 *], f, 3, 3 *], f, 1, 1 *], f, 0, 0 *], f, 3, 3 *], f, 2, 2 *], f, 0, 0 *], f, 2, 2 *], f, 3, 3 *], f, 0, 0 *], f, 2, 2 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 1, 1 *], f, 3, 3 *], f, 1, 1 *], f, 0, 0 *], f, 2, 2 *], f, 1, 1 *], f, 1, 1 *], f, 1, 1 *], f, 1, 1 *], f, 2, 2 *], f, 2, 2 *], f, 3, 3 *], f, 1, 1 *], f, 0, 0 *], f, 3, 3 *], f, 2, 2 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 0, 0 *], f, 0, 0 *], f, 2, 2 *], f, 0, 0 *], f, 0, 0 *], f, 3, 3 *], f, 0, 0 *], f, 1, 1 *], f, 3, 3 *], f, 3, 3 *], f, 1, 1 *], f, 1, 1 *], f, 3, 3 *], f, 1, 1 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *]*];


function conv(I)
	if Type(I) ne List then
		return "f, ";
	elif #I eq 1 then
		return "f, ";
	end if;
	if I[3] eq 0 then
		c := "0, 0), ";
	elif I[3] eq 1 then
		c := "1, 1), ";
	elif I[3] eq 2 then
		c := "2, 2), ";
	elif I[3] eq 3 then
		c := "3, 3), ";
	end if;
	return "Transvectant(" cat conv(I[1]) cat conv(I[2]) cat c;
end function;











QQ := Rationals();
R<x,y,z,w> := PolynomialRing(QQ, [1,1,1,1]);
Quadric1:=-10*x^2 - x*y + 8*x*z + 3*x*w - 9*y*z + y*w - 6*z^2 - 5*z*w - 5*w^2;
Cubic1:=-x^2*y - x^2*z - 5*x^2*w - 6*x*y^2 - 2*x*y*z - 9*x*y*w + 7*x*z^2 + 3*x*z*w -
    8*x*w^2 - 10*y^3 + 3*y^2*z - y^2*w - 3*y*z^2 - 7*y*w^2 - z^3 + z^2*w -
    10*z*w^2 + 3*w^3;
f1 := CubicNewBasis(Quadric1,Cubic1);
R<x, y, u, v> := PolynomialRing(BaseRing(Parent(f1)), 4);
f1 := Evaluate(f1, [x*u, x*v, y*u, y*v]);
time I1 := InvariantsGenus4Curves(list_invariants, f1);
same_wps(list_invariants, I1, I1);


time I2 := InvariantsGenus4Curves_test(f1);

function normal_form(f1)
	R := Parent(f1);
	a33 := MonomialCoefficient(f1, R.1^3*R.3^3);
	a32 := MonomialCoefficient(f1, R.1^3*R.3^2*R.4);
	a31 := MonomialCoefficient(f1, R.1^3*R.3*R.4^2);  
	a30 := MonomialCoefficient(f1, R.1^3*R.4^3);  
	a := Roots(a30*x0^3-a31*x0^2+a32*x0-a33)[1][1];
	f2 := Evaluate(f1, [R.1, R.2, R.3, R.4-a*R.3]);
	//f2;
	alpha := Roots(x0^8-MonomialCoefficient(f2, R.1^2*R.2*R.3^3)/MonomialCoefficient(f2, R.1^3*R.3^2*R.4)^3)[1][1];
	beta := 1/(alpha^3*MonomialCoefficient(f2, R.1^3*R.3^2*R.4));
	f3 := Evaluate(f2, [alpha*R.1, 1/alpha*R.2, beta*R.3, 1/beta*R.4]);
	f4 := Evaluate(f3, [R.1-MonomialCoefficient(f3, R.1*R.2^2*R.3^3)/2*R.2, R.2, R.3, R.4]);
	f5 := Evaluate(f4, [R.1, R.2, R.3-MonomialCoefficient(f4, R.1^2*R.2*R.3^2*R.4)/3*R.4, R.4]);
	return f5;
end function;

f1 := Evaluate(f1, [x*u, y*u, x*v, y*v]);
f1 := f1/Sqrt(K!Evaluate(transvectant(f1, f1, 3, 3), [0,0,0,0]));
I1 := eval_inv(list_invariants, f1);
f2 := normal_form(f1);
I2 := eval_inv(list_invariants, f1);









//Field of definition
function Check(L)
	for i in [1..Floor(#L/2)] do
		if L[2*i] ne 0 then
			return false;
		end if;
	end for;
	return true;
end function;

QQ := Rationals();
//R1<a3000, a2100, a2010, a2001, a1200, a1110, a1101, a1020, a1011, a0300, a0210, a0201, a0120, a0111, a0030, a0021, A, B, D1, D2> := PolynomialRing(QQ, [1 : i in [1..20]]);
R1<a3000, a2100, a2010, a2001, a1200, a1110, a1101, a1020, a1011, a0300, a0210, a0201, a0120, a0111, a0030, a0021, D1, D2> := PolynomialRing(QQ, [1 : i in [1..18]]);
R<X, Y, Z, T> := PolynomialRing(FieldOfFractions(R1), [1,1,1,1]);
A := 10;
B := 12;
//P := Transpose(Matrix(R, [[1/(2*A),0,0,1/(2*A*D1)],[0,-1/(2*B),-1/(2*B*D2),0],[0,1/2,-1/(2*D2),0],[1/2,0,0,-1/(2*D1)]]));
P := Transpose(Matrix(R, [[D1,0,0,1],[0,-D2,-1,0],[0,D2,-1,0],[D1,0,0,-1]]));
S := ElementToSequence(P*Matrix([[X], [Y], [Z], [T]]));
C := 0*X^3+2*X^2*Y+3*X^2*Z+a2001*X^2*T+a1200*X*Y^2+a1110*X*Y*Z+a1101*X*Y*T+a1020*X*Z^2+a1011*X*Z*T+a0300*Y^3+a0210*Y^2*Z+a0201*Y^2*T+a0120*Y*Z^2+a0111*Y*Z*T+a0030*Z^3+Z^2*T;
C := Evaluate(C, S);
S<x, y, u, v> := PolynomialRing(FieldOfFractions(R1), [1,1,1,1]);
f0 := Evaluate(C, [x*u, x*v, y*u, y*v]); 
for i in [1..#list_invariants] do
	time inv := R1!Evaluation(list_invariants[i], f0);
	DegreeOrder(list_invariants[i])[1];
	Check(Terms(inv, D1));
	Check(Terms(inv, D2));
end for;

























