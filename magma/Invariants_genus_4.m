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
	if t lt 3 then
		"The quadric is not of rank 3 or 4";
		return D, t;
	elif t eq 4 then
		L := [-D[4][4]/D[1][1], -D[3][3]/D[2][2]];
		if not Category(K) eq FldCom then //we take a bigger field to be sure that the change of variable is well defined, and AlgebraicClosure(ComplexField()) returns an error
			S := AlgebraicClosure(K);
			//[[Sqrt(S!L[i]), S!L[i]] : i in [1..2]]; // this is useful to know which square roots we are adding
		else
			S := K;
		end if;
		M2 := KMatrixSpace(S,4,4);
		P := ChangeRing(P, S);
		P_fin := (M2![1/(2*D[1][1]),0,0,1/(2*D[1][1]*Sqrt(S!L[1])),0,-1/(2*D[2][2]),-1/(2*D[2][2]*Sqrt(S!L[2])),0,0,1/2,-1/(2*Sqrt(S!L[2])),0,1/2,0,0,-1/(2*Sqrt(S!L[1]))])*P;
		return P_fin, 4;
	else
		i := 1;
		while D[i][i] ne 0 do
			i := i+1;
		end while;
		L := [1,2,3,4];
		L[i] := 4;
		L[4] := i;
		P_swap := PermutationMatrix(K, L);
		D := P_swap*D*P_swap;
		P := P_swap*P;
		L := [-D[3][3]/D[1][1], -D[2][2]];
		if not Category(K) eq FldCom then // we take a bigger field to be sure that the change of variable is well defined, and AlgebraicClosure(ComplexField()) returns an error
			S := AlgebraicClosure(K);
			// [[Sqrt(S!L[i]), S!L[i]] : i in [1..2]]; // this is useful to know which square roots we are adding
		else
			S := K;
		end if;
		M2 := KMatrixSpace(S,4,4);
		P := ChangeRing(P, S);
		P_fin := (M2![1/(2*D[1][1]),0,1/(2*D[1][1]*Sqrt(S!L[1])),0,0,1/(Sqrt(S!L[2])),0,0,1/2,0,-1/(2*Sqrt(S!L[1])),0,0,0,0,1])*P;
		return P_fin, 3;
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
	P := NewBasis(Q);
	R := ChangeRing(R, BaseRing(Parent(P)));
	C1 := R!C;
	return ChangeOfBasis(C1, P);
end function;

function InvariantsGenus4CurvesRank4(f)
	// Covariants
	// Degree 2
	f2 := Transvectant(f, f, 0, 0);
	Jac := Transvectant(f, f, 1, 1);
	H := Transvectant(f, f, 2, 2);

	// Degree 3
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

	// Degree 4
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

	// Degree 5
	C51H := Transvectant(C42H, f, 2, 2);
	C53H := Transvectant(C42H, f, 1, 1);
	C55H := Transvectant(C44H, f, 1, 1);
	C53H1 := Transvectant(C42H1, f, 1, 1);

	C55f := Transvectant(C46f, f, 2, 2);
	C513f := Transvectant(f4, f, 1, 1);

	C55 := Transvectant(C42H, f, 0, 0);
	C551 := Transvectant(C42, f, 0, 0);

	C57 := Transvectant(C441, f, 0, 0);

	// Degree 6
	C62H := Transvectant(C53H, f, 2, 2);
	C62H1 := Transvectant(C53H1, f, 2, 2);
	C62H2 := Transvectant(C51H, f, 1, 1);
	C66H := Transvectant(C55H, f, 1, 1);

	// Degree 7
	C71H := Transvectant(C62H, f, 2, 2);
	C73H1 := Transvectant(C62H1, f, 1, 1);
	C79H := Transvectant(C66H, f, 0, 0);

	// Invariants
	// HSOP
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

	// Degree 6
	J62 := Transvectant(Transvectant(Transvectant(f3, f, 3, 3), f, 3, 3), f, 3, 3);
	inv6 := [J62];

	// Degree 8
	J82 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C35H, f, 2, 2), f, 0, 0), f, 2, 2), f, 3, 3), f, 3, 3);
	J83 := Transvectant(Transvectant(C66H, f, 3, 3), f, 3, 3);
	inv8 := [J82, J83];
	
	// Degree 10
	J102 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C42H2, f, 0, 0), f, 0, 0), f, 2, 2), f, 3, 3), f, 2, 2), f, 3, 3);
	J103 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C48f, f, 2, 2), f, 1, 1), f, 1, 1), f, 3, 3), f, 3, 3), f, 3, 3);
	J104 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C48f, f, 3, 3), f, 2, 2), f, 3, 3), f, 1, 1), f, 1, 1), f, 3, 3);
	J105 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C35, f, 1, 1), f, 3, 3), f, 0, 0), f, 0, 0), f, 3, 3), f, 3, 3), f, 3, 3);
	J106 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C44H1, f, 3, 3), f, 0, 0), f, 1, 1), f, 2, 2), f, 2, 2), f, 3, 3);
	J107 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C42H2, f, 1, 1), f, 2, 2), f, 2, 2), f, 0, 0), f, 2, 2), f, 3, 3);
	inv10 := [J102, J103, J104, J105, J106, J107];

	// Degree 12
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

	// Degree 14
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

	// Degree 16
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

	// Degree 18
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

	return 	[2,4,4,6,6,8,8,10,12,14,6,8,8,10,10,10,10,10,10,12,12,12,12,12,12,12,12,12,14,14,14,14,14,14,14,14,14,14,14,14,16,16,16,16,16,16,16,16,16,16,16,16,16,16,18,18,18,18,18,18,18,18,18,18,18], invHSOP cat inv6 cat inv8 cat inv10 cat inv12 cat inv14 cat inv16 cat inv18;
end function;


function InvariantsGenus4CurvesRank3(f, v)
	// Covariants of f
	h24 := Transvectant(f, f, 4);
	h28 := Transvectant(f, f, 2);
	h32 := Transvectant(h24, f, 4);
	h36 := Transvectant(h24, f, 2);
	h38 := Transvectant(h24, f, 1);
	h312 := Transvectant(h28, f, 1);
	h44 := Transvectant(h32, f, 2);
	h46 := Transvectant(h32, f, 1);
	h52 := Transvectant(h24, h32, 2);
	h54 := Transvectant(h24, h32, 1);
	h58 := Transvectant(h28, h32, 1);
	h661 := Transvectant(h38, h32, 2);
	h662 := Transvectant(h36, h32, 1);
	h74 := Transvectant(f, h32^2, 3);
	h82 := Transvectant(h24, h32^2, 3);
	h94 := Transvectant(h38, h32^2, 4);
	h102 := Transvectant(h32^3, f, 5);

	// Covariants of v
	k24 := Transvectant(v, v, 2);
	k36 := Transvectant(v, k24, 1);

	// Invariants
	// Invariants of f
	J2f := Evaluate(Transvectant(f, f, 6), [0,0]);
	J4f := Evaluate(Transvectant(h24, h24, 4), [0,0]);
	J6f := Evaluate(Transvectant(h32, h32, 2), [0,0]);
	J10f := Evaluate(Transvectant(h32^3, f, 6), [0,0]);
	J15f := Evaluate(Transvectant(h38, h32^4, 8), [0,0]);
	invf := [J2f, J4f, J6f, J10f, J15f];

	// Invariants of v
	J2v := Evaluate(Transvectant(v, v, 4), [0,0]);
	J3v := Evaluate(Transvectant(k24, v, 4), [0,0]);
	invv := [J2v, J3v];
 
	//  Joint degree 3
	J3 := Evaluate(Transvectant(h24, v, 4), [0,0]);
	inv3 := [J3];

	//  Joint degree 4
	J41 := Evaluate(Transvectant(h28, v^2, 8), [0,0]);
	J42 := Evaluate(Transvectant(h24, k24, 4), [0,0]);
	J43 := Evaluate(Transvectant(k36, f, 6), [0,0]);
	inv4 := [J41, J42, J43];

	// Joint degree 5
	J51 := Evaluate(Transvectant(h38, v^2, 8), [0,0]);
	J52 := Evaluate(Transvectant(h44, v, 4), [0,0]);
	J53 := Evaluate(Transvectant(h28, v*k24, 8), [0,0]);
	J54 := Evaluate(Transvectant(f^2, v^3, 12), [0,0]);
	inv5 := [J51, J52, J53, J54];

	// Joint degree 6
	J61 := Evaluate(Transvectant(h38, v*k24, 8), [0,0]);
	J62 := Evaluate(Transvectant(f^2, v^2*k24, 12), [0,0]);
	J63 := Evaluate(Transvectant(h28, k24^2, 8), [0,0]);
	J64 := Evaluate(Transvectant(h36, k36, 6), [0,0]);
	J65 := Evaluate(Transvectant(h312, v^3, 12), [0,0]);
	J66 := Evaluate(Transvectant(h54, v, 4), [0,0]);
	J67 := Evaluate(Transvectant(h44, k24, 4), [0,0]);
	J68 := Evaluate(Transvectant(h32*f, v^2, 8), [0,0]);
	inv6 := [J61, J62, J63, J64, J65, J66, J67, J68];

	// Joint degree 7
	J71 := Evaluate(Transvectant(h32^2, v, 4), [0,0]);
	J72 := Evaluate(Transvectant(h54, k24, 4), [0,0]);
	J73 := Evaluate(Transvectant(h58, v^2, 8), [0,0]);
	J74 := Evaluate(Transvectant(f*h36, v^3, 12), [0,0]);
	J75 := Evaluate(Transvectant(f^2, v*k24^2, 12), [0,0]);
	J76 := Evaluate(Transvectant(h32*f, v*k24, 8), [0,0]);
	J77 := Evaluate(Transvectant(h46, k36, 6), [0,0]);
	J78 := Evaluate(Transvectant(h312, v^2*k24, 12), [0,0]);
	J79 := Evaluate(Transvectant(h38, k24^2, 8), [0,0]);
	inv7 := [J71, J72, J73, J74, J75, J76, J77, J78, J79];

	// Joint degree 8
	J81 := Evaluate(Transvectant(h32*h24, k36, 6), [0,0]);
	J82 := Evaluate(Transvectant(h312, v*k24^2, 12), [0,0]);
	J83 := Evaluate(Transvectant(h32*h36, v^2, 8), [0,0]);
	J84 := Evaluate(Transvectant(h32^2, k24, 4), [0,0]);
	J85 := Evaluate(Transvectant(h74, v, 4), [0,0]);
	J86 := Evaluate(Transvectant(f*h46, v^3, 12), [0,0]);
	J87 := Evaluate(Transvectant(f*h36, v^2*k24, 12), [0,0]);
	J88 := Evaluate(Transvectant(h32*f, k24^2, 8), [0,0]);
	J89 := Evaluate(Transvectant(h58, v*k24, 8), [0,0]);
	inv8 := [J81, J82, J83, J84, J85, J86, J87, J88, J89];

	// Joint degree 9
	J91 := Evaluate(Transvectant(h74, k24, 4), [0,0]);
	J92 := Evaluate(Transvectant(h32*h52, v, 4), [0,0]);
	J93 := Evaluate(Transvectant(h52*f, v*k24, 8), [0,0]);
	J94 := Evaluate(Transvectant(h312, k24^3, 12), [0,0]);
	J95 := Evaluate(Transvectant(h32*h28, v*k36, 10), [0,0]);
	J96 := Evaluate(Transvectant(f*h46, v^2*k24, 12), [0,0]);
	J97 := Evaluate(Transvectant(h36^2, v^3, 12), [0,0]);
	J98 := Evaluate(Transvectant(h32*h46, v^2, 8), [0,0]);
	inv9 := [J91, J92, J93, J94, J95, J96, J97, J98];

	// Joint degree 10
	J101 := Evaluate(Transvectant(h94, v, 4), [0,0]);
	J102 := Evaluate(Transvectant(h32*h28, k24*k36, 10), [0,0]);
	J103 := Evaluate(Transvectant(h52*h36, v^2, 8), [0,0]);
	J104 := Evaluate(Transvectant(f*h661, v^3, 12), [0,0]);
	inv10 := [J101, J102, J103, J104];

	// Joint degree 11
	J111 := Evaluate(Transvectant(h52^2, v, 4), [0,0]);
	J112 := Evaluate(Transvectant(f*h662, v^2*k24, 12), [0,0]);
	J113 := Evaluate(Transvectant(h32*h661, v^2, 8), [0,0]);
	inv11 := [J111, J112, J113];

	// Joint degree 12
	J121 := Evaluate(Transvectant(h32*h82, v, 4), [0,0]);
	J122 := Evaluate(Transvectant(h32*h662, v*k24, 8), [0,0]);
	inv12 := [J121, J122];

	// Joint degree 13
	J13 := Evaluate(Transvectant(h82*h36, v^2, 8), [0,0]);
	inv13 := [J13];

	// Joint degree 14
	J14 := Evaluate(Transvectant(h32*h102, v, 4), [0,0]);
	inv14 := [J14];

	return [2,4,6,10,15,2,3,3,4,4,4,5,5,5,5,6,6,6,6,6,6,6,6,7,7,7,7,7,7,7,7,7,8,8,8,8,8,8,8,8,8,9,9,9,9,9,9,9,9,10,10,10,10,11,11,11,12,12,13,14], invf cat invv cat inv3 cat inv4 cat inv5 cat inv6 cat inv7 cat inv8 cat inv9 cat inv10 cat inv11 cat inv12 cat inv13 cat inv14;
end function;

intrinsic InvariantsGenus4Curves(Q::RngMPolElt, C::RngMPolElt : normalize := false) -> SeqEnum, SeqEnum
	{Given a homogeneous quadric and a homogeneous cubic in 4 variables, returns its invariants. This depends on the }

	require (Parent(Q) eq Parent(C)): "Q and C must have the same parent";
	require (Rank(Parent(Q)) eq 4): "Q and C must be polynomials in 4 variables";
	require IsHomogeneous(Q) and IsHomogeneous(C): "Q and C must be homogeneous";
	require (Degree(Q) eq 2) and (Degree(C) eq 3): "Q must be of degree 2 and C of degree 3";

	R0<X,Y,Z,T> := Parent(Q);
	K := BaseRing(R0);
	P, t := NewBasis(Q);

	if t eq 4 then
		//ChangeOfBasis(Q, P);
		f0 := CubicNewBasis(Q,C);

		R<x, y, u, v> := PolynomialRing(BaseRing(Parent(f0)), 4);
		f_bic := Evaluate(f0, [x*u, y*u, x*v, y*v]);
		
		Wgt, Inv := InvariantsGenus4CurvesRank4(f_bic);
		
		if normalize then
			return Wgt, WPSNormalize(Wgt, Inv);
		end if;

		return Wgt, Inv;

	elif t eq 3 then
		//ChangeOfBasis(Q, P);
		f0 := CubicNewBasis(Q,C);
		
		R<s, t, w> := PolynomialRing(BaseRing(Parent(f0)), [1,1,2]);
		f_weighted := Evaluate(f0, [s^2, s*t, t^2, w]);

		require MonomialCoefficient(f_weighted, w^3) ne 0: "The curve is not smooth";
		
		// we put the curve in normal form
		alpha := Root(MonomialCoefficient(f_weighted, w^3), 3);
		f_weighted := Evaluate(f_weighted, [s, t, w/alpha]);        
		f_weighted := Evaluate(f_weighted, [s, t, w-ExactQuotient(Terms(f_weighted, w)[3], 3*w^2)]);

		S<[x]> := PolynomialRing(BaseRing(Parent(f_weighted)), 2);

		Wgt, Inv := InvariantsGenus4CurvesRank3(S!Evaluate(f_weighted, [x[1], x[2], 0]), S!Evaluate(ExactQuotient(Terms(f_weighted, w)[2], w), [x[1], x[2], 0]));
		
		if normalize then
			return Wgt, WPSNormalize(Wgt, Inv);
		end if;

		return Wgt, Inv;
	end if;

end intrinsic;

import "gordan-10.dat" : FdCov;
import "InvS10.m" : GetCovariant;

intrinsic InvariantsGenus4Curves(f::RngUPolElt : normalize := false) -> SeqEnum, SeqEnum
	{Compute the invariants of a univariate polynomial of degree smaller than 10 as a binary form of degree 10.}

	require Degree(f) le 10: "f must be of degree smaller than 10";

	IdxInv := [idx : idx in [1..#FdCov] | FdCov[idx]`order eq 0];
	List_invariants := [GetCovariant(FdCov[IdxInv[i]], FdCov, f) : i in [1..#IdxInv]];
	return [List_invariants[i][2] : i in [1..#IdxInv]], [List_invariants[i][1] : i in [1..#IdxInv]];

end intrinsic;


intrinsic InvariantsGenus4Curves(f::RngMPolElt : normalize := false) -> SeqEnum, SeqEnum
	{Compute the invariants of a bivariate homogeneous polynomial of degree 10.}

	require Rank(Parent(f)) eq 2: "f must be a bivariate polynomial";
	require IsHomogeneous(f): "f must be homogeneous";
	require Degree(f) eq 10: "f must be of degree smaller than 10";
	
	C<x> := PolynomialRing(BaseRing(Parent(f)));
	F := C!Evaluate(f, [x, 1]);
	
	Wgt, Inv := InvariantsGenus4Curves(f);

	if normalize then
		return Wgt, WPSNormalize(Wgt, Inv);
	end if;

	return Wgt, Inv;
end intrinsic;


intrinsic InvariantsGenus4Curves(C::CrvHyp : normalize := false) -> SeqEnum, SeqEnum
	{Given a hyperelliptic curve of genus 4, return its invariants.}
	
	require Genus(C) eq 4: "Curve must be of genus 4.";

    K := BaseField(C);
    R := PolynomialRing(K); x := R.1;
    f0, h0 := HyperellipticPolynomials(C);

	require (Degree(h0) le 5) and (Degree(f0) le 10): "The polynomials h and f must have degree at most 5 and 10, respectively.";

	f := (h0/2)^2+f0;

	Wgt, Inv := InvariantsGenus4Curves(f);

	if normalize then
		return Wgt, WPSNormalize(Wgt, Inv);
	end if;

	return Wgt, Inv;
end intrinsic;

intrinsic IsIsomorphic(Q1::RngMPolElt, C1::RngMPolElt, Q2::RngMPolElt, C2::RngMPolElt : epsilon := 0) -> Bool
	{Given two non-hyperelliptic curves of genus 4, returns if their invariants are the same up to espilon}

	Wgt1, I1 := InvariantsGenus4Curves(Q1, C1 : normalize := true);
	Wgt2, I2 := InvariantsGenus4Curves(Q2, C2 : normalize := true);

	require Wgt1 eq Wgt2 : "Curves must have a quadric of the same rank 3 or 4";
	
	for i in [1..#I1] do
		if Abs(I1[i]-I2[i]) gt epsilon then
			return false;
		end if;
	end for;
	return true;

end intrinsic;



























