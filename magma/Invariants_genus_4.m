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


//given a cubic and a change of variables (given as a matrix), returns the cubic after the change of variables
function ChangeOfBasis(C, P)
	R := ChangeRing(Parent(C), Parent(P[1][1]));
	C := R!C;
	P := Transpose(Matrix([[R!P[i][j] : j in [1..NumberOfColumns(P)]] : i in [1..NumberOfRows(P)]]));
	Y := ElementToSequence(P*Matrix([[R.i] : i in [1..Rank(R)]]));
	//Y := [P[1][i]*R.1+P[2][i]*R.2+P[3][i]*R.3+P[4][i]*R.4 : i in [1..Rank(R)]];
	return Evaluate(C, Y);
end function;
	
function CubicNewBasis(Q, C)
	R := Parent(C);
	P := NewBasis(Q);
	R := ChangeRing(R, BaseRing(Parent(P)));
	C1 := R!C;
	return ChangeOfBasis(C1, P);
end function;


//goes from weighted projective to projective, so we can compare two sets of invariants
//it divides by the first invariant (it's almost never zero), but it can be adapted to divide by the first invariants which is non-zero
function same_wps(L, I1, I2)
	res := [];
	for i in [1..#L] do
		l := I2[i]/I2[1]^(ExactQuotient(DegreeOrder(L[i])[1],2));
		Append(~res, l);
	end for;
	return [I1[i]/I1[1]^(ExactQuotient(DegreeOrder(L[i])[1],2)) : i in [1..#L]], res;
end function;



d<f> := PolynomialRing(Rationals(), 1); //only to write "f" in the transvectants, I don't know how else to define a variable

//the invariants
list_invariants := [*[*f, f, 3, 3*], [*[*f, f, 2, 2*], [*f, f, 2, 2*], 2, 2*], [*[*[*f, f, 1, 1*], f, 2, 2*], f, 3, 3*], [* [* [* f, f, 2, 2*], [* f, f, 2, 2*], 1, 1 *], [* f, f, 2, 2 *], 2, 2 *], [* [* [* [* [* f, f, 2, 2 *], f, 2, 2 *], f, 1, 1 *], f, 1, 1 *], f, 3, 3 *], [* [* [* f, f, 2, 2*], [* f, f, 2, 2*], 1, 1 *], [* [* f, f, 2, 2*], [* f, f, 2, 2*], 1, 1 *], 2, 2 *], [* [* [* [* [* [* [* f, f, 2, 2 *], f, 1, 1 *], f, 2, 2 *], f, 1, 1 *], f, 2, 2 *], f, 1, 1 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* f, f, 2, 2 *], f, 2, 2 *], f, 1, 1 *], f, 1, 1 *], f, 2, 2 *], f, 2, 2 *], f, 1, 1 *], f, 1, 1 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* f, f, 2, 2 *], f, 1, 1 *], f, 2, 2 *], f, 1, 1 *], f, 2, 2 *], f, 1, 1 *], f, 1, 1 *], f, 2, 2 *], f, 0, 0 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* f, f, 2, 2 *], f, 2, 2 *], f, 1, 1 *], f, 2, 2 *], f, 1, 1 *], f, 1, 1 *], f, 2, 2 *], f, 2, 2 *], f, 1, 1 *], f, 2, 2 *], [* f, f, 2, 2 *], 0, 0 *], f, 3, 3 *], [* [* [* [* [* f, f, 0, 0 *], f, 0, 0 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* f, f, 2, 2 *], f, 0, 0 *], f, 2, 2 *], f, 0, 0 *], f, 2, 2 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* f, f, 2, 2 *], f, 2, 2 *], f, 0, 0 *], f, 1, 1 *], f, 1, 1 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* f, f, 2, 2 *], f, 0, 0 *], f, 3, 3 *], f, 0, 0 *], f, 0, 0 *], f, 2, 2 *], f, 3, 3 *], f, 2, 2 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* f, f, 0, 0 *], f, 2, 2 *], f, 0, 0 *], f, 2, 2 *], f, 1, 1 *], f, 1, 1 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* f, f, 0, 0 *], f, 2, 2 *], f, 0, 0 *], f, 3, 3 *], f, 2, 2 *], f, 3, 3 *], f, 1, 1 *], f, 1, 1 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* f, f, 1, 1 *], f, 1, 1 *], f, 1, 1 *], f, 3, 3 *], f, 0, 0 *], f, 0, 0 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* f, f, 2, 2 *], f, 1, 1 *], f, 1, 1 *], f, 3, 3 *], f, 0, 0 *], f, 1, 1 *], f, 2, 2 *], f, 2, 2 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* f, f, 2, 2 *], f, 0, 0 *], f, 3, 3 *], f, 1, 1 *], f, 2, 2 *], f, 2, 2 *], f, 0, 0 *], f, 2, 2 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* f, f, 0, 0 *], f, 3, 3 *], f, 1, 1 *], f, 3, 3 *], f, 0, 0 *], f, 3, 3 *], f, 0, 0 *], f, 1, 1 *], f, 2, 2 *], f, 2, 2 *], f, 3, 3 *], [*[*[* [* [* [* [* [* [* [* [* f, f, 0, 0 *], f, 1, 1 *], f, 1, 1 *], f, 2, 2 *], f, 2, 2 *], f, 0, 0 *], f, 1, 1 *], f, 3, 3 *], f, 3, 3 *], f, 2, 2 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* f, f, 0, 0 *], f, 1, 1 *], f, 2, 2 *], f, 2, 2 *], f, 3, 3 *], f, 1, 1 *], f, 0, 0 *], f, 3, 3 *], f, 1, 1 *], f, 2, 2 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* f, f, 0, 0 *], f, 0, 0 *], f, 0, 0 *], f, 1, 1 *], f, 3, 3 *], f, 2, 2 *], f, 1, 1 *], f, 2, 2 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* f, f, 1, 1 *], f, 2, 2 *], f, 1, 1 *], f, 3, 3 *], f, 1, 1 *], f, 0, 0 *], f, 1, 1 *], f, 2, 2 *], f, 1, 1 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* f, f, 0, 0 *], f, 3, 3 *], f, 1, 1 *], f, 0, 0 *], f, 1, 1 *], f, 1, 1 *], f, 2, 2 *], f, 1, 1 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* f, f, 0, 0 *], f, 0, 0 *], f, 0, 0 *], f, 2, 2 *], f, 2, 2 *], f, 1, 1 *], f, 1, 1 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* f, f, 0, 0 *], f, 2, 2 *], f, 0, 0 *], f, 0, 0 *], f, 3, 3 *], f, 2, 2 *], f, 2, 2 *], f, 3, 3 *], f, 0, 0 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* f, f, 2, 2 *], f, 2, 2 *], f, 0, 0 *], f, 1, 1 *], f, 1, 1 *], f, 0, 0 *], f, 1, 1 *], f, 3, 3 *], f, 3, 3 *], f, 2, 2 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 2, 2 *], f, 1, 1 *], f, 1, 1 *], f, 0, 0 *], f, 2, 2 *], f, 0, 0 *], f, 2, 2 *], f, 0, 0 *], f, 2, 2 *], f, 2, 2 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 0, 0 *], f, 0, 0 *], f, 2, 2 *], f, 1, 1 *], f, 2, 2 *], f, 1, 1 *], f, 0, 0 *], f, 2, 2 *], f, 2, 2 *], f, 2, 2 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 2, 2 *], f, 2, 2 *], f, 0, 0 *], f, 0, 0 *], f, 3, 3 *], f, 2, 2 *], f, 2, 2 *], f, 2, 2 *], f, 0, 0 *], f, 0, 0 *], f, 2, 2 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 1, 1 *], f, 1, 1 *], f, 3, 3 *], f, 2, 2 *], f, 0, 0 *], f, 1, 1 *], f, 1, 1 *], f, 3, 3 *], f, 0, 0 *], f, 1, 1 *], f, 3, 3 *], f, 2, 2 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 0, 0 *], f, 1, 1 *], f, 3, 3 *], f, 1, 1 *], f, 2, 2 *], f, 0, 0 *], f, 3, 3 *], f, 0, 0 *], f, 3, 3 *], f, 3, 3 *], f, 0, 0 *], f, 2, 2 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 1, 1 *], f, 2, 2 *], f, 1, 1 *], f, 1, 1 *], f, 1, 1 *], f, 0, 0 *], f, 1, 1 *], f, 1, 1 *], f, 2, 2 *], f, 3, 3 *], f, 3, 3 *], f, 2, 2 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 0, 0 *], f, 1, 1 *], f, 3, 3 *], f, 3, 3 *], f, 1, 1 *], f, 0, 0 *], f, 1, 1 *], f, 0, 0 *], f, 1, 1 *], f, 2, 2 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 0, 0 *], f, 2, 2 *], f, 1, 1 *], f, 0, 0 *], f, 0, 0 *], f, 2, 2 *], f, 3, 3 *], f, 2, 2 *], f, 3, 3 *], f, 1, 1 *], f, 1, 1 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 1, 1 *], f, 0, 0 *], f, 0, 0 *], f, 3, 3 *], f, 2, 2 *], f, 0, 0 *], f, 2, 2 *], f, 0, 0 *], f, 1, 1 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 0, 0 *], f, 0, 0 *], f, 0, 0 *], f, 1, 1 *], f, 0, 0 *], f, 1, 1 *], f, 2, 2 *], f, 2, 2 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 2, 2 *], f, 2, 2 *], f, 1, 1 *], f, 0, 0 *], f, 2, 2 *], f, 3, 3 *], f, 1, 1 *], f, 0, 0 *], f, 0, 0 *], f, 3, 3 *], f, 1, 1 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 0, 0 *], f, 3, 3 *], f, 0, 0 *], f, 0, 0 *], f, 3, 3 *], f, 0, 0 *], f, 1, 1 *], f, 2, 2 *], f, 3, 3 *], f, 2, 2 *], f, 2, 2 *], f, 2, 2 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 1, 1 *], f, 2, 2 *], f, 2, 2 *], f, 0, 0 *], f, 1, 1 *], f, 2, 2 *], f, 2, 2 *], f, 0, 0 *], f, 1, 1 *], f, 0, 0 *], f, 3, 3 *], f, 3, 3 *], f, 2, 2 *], f, 2, 2 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 0, 0 *], f, 1, 1 *], f, 3, 3 *], f, 0, 0 *], f, 3, 3 *], f, 1, 1 *], f, 1, 1 *], f, 1, 1 *], f, 1, 1 *], f, 2, 2 *], f, 1, 1 *], f, 3, 3 *], f, 2, 2 *], f, 2, 2 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 2, 2 *], f, 2, 2 *], f, 1, 1 *], f, 0, 0 *], f, 0, 0 *], f, 1, 1 *], f, 0, 0 *], f, 2, 2 *], f, 2, 2 *], f, 0, 0 *], f, 2, 2 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 2, 2 *], f, 1, 1 *], f, 0, 0 *], f, 1, 1 *], f, 3, 3 *], f, 2, 2 *], f, 2, 2 *], f, 0, 0 *], f, 2, 2 *], f, 3, 3 *], f, 0, 0 *], f, 0, 0 *], f, 3, 3 *], f, 2, 2 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 2, 2 *], f, 2, 2 *], f, 0, 0 *], f, 3, 3 *], f, 1, 1 *], f, 1, 1 *], f, 0, 0 *], f, 2, 2 *], f, 2, 2 *], f, 3, 3 *], f, 1, 1 *], f, 0, 0 *], f, 2, 2 *], f, 2, 2 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 2, 2 *], f, 2, 2 *], f, 0, 0 *], f, 2, 2 *], f, 1, 1 *], f, 3, 3 *], f, 0, 0 *], f, 3, 3 *], f, 1, 1 *], f, 0, 0 *], f, 0, 0 *], f, 1, 1 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 1, 1 *], f, 1, 1 *], f, 0, 0 *], f, 3, 3 *], f, 1, 1 *], f, 1, 1 *], f, 2, 2 *], f, 3, 3 *], f, 2, 2 *], f, 2, 2 *], f, 0, 0 *], f, 3, 3 *], f, 0, 0 *], f, 2, 2 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 1, 1 *], f, 2, 2 *], f, 0, 0 *], f, 0, 0 *], f, 0, 0 *], f, 0, 0 *], f, 2, 2 *], f, 1, 1 *], f, 0, 0 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 1, 1 *], f, 1, 1 *], f, 2, 2 *], f, 1, 1 *], f, 1, 1 *], f, 0, 0 *], f, 3, 3 *], f, 1, 1 *], f, 0, 0 *], f, 1, 1 *], f, 2, 2 *], f, 2, 2 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 2, 2 *], f, 1, 1 *], f, 1, 1 *], f, 2, 2 *], f, 1, 1 *], f, 1, 1 *], f, 1, 1 *], f, 1, 1 *], f, 3, 3 *], f, 1, 1 *], f, 0, 0 *], f, 3, 3 *], f, 2, 2 *], f, 2, 2 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 0, 0 *], f, 1, 1 *], f, 0, 0 *], f, 0, 0 *], f, 1, 1 *], f, 0, 0 *], f, 2, 2 *], f, 2, 2 *], f, 2, 2 *], f, 1, 1 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 1, 1 *], f, 1, 1 *], f, 2, 2 *], f, 0, 0 *], f, 1, 1 *], f, 3, 3 *], f, 1, 1 *], f, 1, 1 *], f, 1, 1 *], f, 3, 3 *], f, 1, 1 *], f, 0, 0 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 1, 1 *], f, 3, 3 *], f, 1, 1 *], f, 0, 0 *], f, 1, 1 *], f, 0, 0 *], f, 0, 0 *], f, 2, 2 *], f, 3, 3 *], f, 1, 1 *], f, 0, 0 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 2, 2 *], f, 2, 2 *], f, 1, 1 *], f, 2, 2 *], f, 1, 1 *], f, 0, 0 *], f, 1, 1 *], f, 2, 2 *], f, 2, 2 *], f, 1, 1 *], f, 3, 3 *], f, 2, 2 *], f, 1, 1 *], f, 1, 1 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 2, 2 *], f, 2, 2 *], f, 1, 1 *], f, 1, 1 *], f, 2, 2 *], f, 2, 2 *], f, 0, 0 *], f, 0, 0 *], f, 0, 0 *], f, 2, 2 *], f, 3, 3 *], f, 0, 0 *], f, 3, 3 *], f, 1, 1 *], f, 3, 3 *], f, 2, 2 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 0, 0 *], f, 1, 1 *], f, 2, 2 *], f, 2, 2 *], f, 0, 0 *], f, 0, 0 *], f, 0, 0 *], f, 0, 0 *], f, 3, 3 *], f, 0, 0 *], f, 3, 3 *], f, 3, 3 *], f, 2, 2 *], f, 2, 2 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 2, 2 *], f, 2, 2 *], f, 0, 0 *], f, 1, 1 *], f, 1, 1 *], f, 0, 0 *], f, 3, 3 *], f, 1, 1 *], f, 1, 1 *], f, 1, 1 *], f, 1, 1 *], f, 2, 2 *], f, 1, 1 *], f, 2, 2 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 0, 0 *], f, 0, 0 *], f, 1, 1 *], f, 2, 2 *], f, 3, 3 *], f, 1, 1 *], f, 3, 3 *], f, 1, 1 *], f, 0, 0 *], f, 1, 1 *], f, 3, 3 *], f, 2, 2 *], f, 1, 1 *], f, 0, 0 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 1, 1 *], f, 1, 1 *], f, 2, 2 *], f, 0, 0 *], f, 0, 0 *], f, 2, 2 *], f, 1, 1 *], f, 2, 2 *], f, 3, 3 *], f, 1, 1 *], f, 3, 3 *], f, 3, 3 *], f, 0, 0 *], f, 0, 0 *], f, 2, 2 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 2, 2 *], f, 1, 1 *], f, 0, 0 *], f, 2, 2 *], f, 0, 0 *], f, 1, 1 *], f, 3, 3 *], f, 0, 0 *], f, 1, 1 *], f, 2, 2 *], f, 3, 3 *], f, 2, 2 *], f, 2, 2 *], f, 1, 1 *], f, 3, 3 *], f, 1, 1 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 1, 1 *], f, 2, 2 *], f, 2, 2 *], f, 0, 0 *], f, 0, 0 *], f, 0, 0 *], f, 2, 2 *], f, 2, 2 *], f, 2, 2 *], f, 3, 3 *], f, 1, 1 *], f, 0, 0 *], f, 1, 1 *], f, 3, 3 *], f, 2, 2 *], f, 3, 3 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 1, 1 *], f, 3, 3 *], f, 0, 0 *], f, 0, 0 *], f, 1, 1 *], f, 1, 1 *], f, 0, 0 *], f, 3, 3 *], f, 2, 2 *], f, 3, 3 *], f, 2, 2 *], f, 3, 3 *], f, 1, 1 *], f, 2, 2 *], f, 1, 1 *], f, 1, 1 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 2, 2 *], f, 0, 0 *], f, 2, 2 *], f, 2, 2 *], f, 0, 0 *], f, 2, 2 *], f, 3, 3 *], f, 1, 1 *], f, 0, 0 *], f, 3, 3 *], f, 2, 2 *], f, 0, 0 *], f, 2, 2 *], f, 3, 3 *], f, 0, 0 *], f, 2, 2 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 1, 1 *], f, 3, 3 *], f, 1, 1 *], f, 0, 0 *], f, 2, 2 *], f, 1, 1 *], f, 1, 1 *], f, 1, 1 *], f, 1, 1 *], f, 2, 2 *], f, 2, 2 *], f, 3, 3 *], f, 1, 1 *], f, 0, 0 *], f, 3, 3 *], f, 2, 2 *], f, 3, 3 *], [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* [* f, f, 0, 0 *], f, 0, 0 *], f, 2, 2 *], f, 0, 0 *], f, 0, 0 *], f, 3, 3 *], f, 0, 0 *], f, 1, 1 *], f, 3, 3 *], f, 3, 3 *], f, 1, 1 *], f, 1, 1 *], f, 3, 3 *], f, 1, 1 *], f, 3, 3 *], f, 3, 3 *], f, 3, 3 *]*];

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
//Examples of computations: first with Bring's curve and an approximation of it, and then on a random curve over Q

//exact equations of Bring's curve
R1<X,Y,Z,T> := PolynomialRing(Rationals(), 4);
Q := X^2+Y^2+Z^2+T^2+(X+Y+Z+T)^2;
C := X^3+Y^3+Z^3+T^3-(X+Y+Z+T)^3;
P := NewBasis(Q);
ChangeOfBasis(Q, P);
f0 := CubicNewBasis(Q,C);
R<x, y, u, v> := PolynomialRing(BaseRing(Parent(f0)), 4);
f0 := Evaluate(f0, [x*u, y*u, x*v, y*v]); //this is the pullback of the cubic by the Segre morphism
time I1 := InvariantsGenus4Curves(list_invariants, f0);
I1;

//now the approximation, given with period matrices and theta functions
K<I> := ComplexField();
R2<X,Y,Z,T> := PolynomialRing(K, 4);
Q := -0.696204170879482*X^2 - 8.92722674847333*I*X^2 - 50.7464824844223*X*Y + 58.7433272900886*I*X*Y - 57.8475326042462*X*Z - 32.3114052362709*I*X*Z + 0.696204169859874*X*T + 8.92722674924129*I*X*T + 47.4047605707472*Y^2 - 101.593270607375*I*Y^2 + 5.27347385941716e-10*Y*Z + 2.16410098974995e-10*I*Y*Z + 3.89862714549051*Y*T + 49.9909796383706*I*Y*T + 57.8475326039864*Z^2 + 32.311405236749*I*Z^2 + 57.8475326042301*Z*T + 32.3114052362822*I*Z*T + 1.25310940216974*T^2 + 16.0682630702241*I*T^2;
C := -234.90098969853*X^3 + 18.3191324015837*I*X^3 + 731.606628191784*X^2*Y + 478.455421156368*I*X^2*Y - 28.0203433984233*X^2*Z + 537.696155252943*I*X^2*Z + 352.35148455507*X^2*T - 27.4786985925642*I*X^2*T - 1147.27882034153*X*Y^2 - 485.876613084882*I*X*Y^2 + 562.593434153083*X*Y*Z - 32.1564704803837*I*X*Y*Z + 980.788369655334*X*Y*T - 92.8898492454102*I*X*Y*T + 28.0203433999316*X*Z^2 - 537.696155256996*I*X*Z^2 + 46.4622057542801*X*Z*T - 1058.24383026716*I*X*Z*T - 117.49502119373*X*T^2 + 9.16303864839564*I*X*T^2 + 125.61555530265*Y^3 - 446.88807153401*I*Y^3 + 6.75526150060275e-9*Y^2*Z - 1.19815129405316e-9*I*Y^2*Z + 26.7719595933429*Y^2*T + 14.3136325339934*I*Y^2*T - 562.593434151639*Y*Z^2 + 32.1564704772876*I*Y*Z^2 - 562.593434153289*Y*Z*T + 32.1564704813713*I*Y*Z*T - 537.802876178166*Y*T^2 + 41.9414243755401*I*Y*T^2 + 2.42764898083213e-9*Z^3 + 3.72099942130995e-9*I*Z^3 - 18.4418623558656*Z^2*T + 520.547675015364*I*Z^2*T - 18.4418623559262*Z*T^2 + 520.547675014923*I*Z*T^2 + 0.0222631708007216*T^3 - 0.00173622441208977*I*T^3;
f1 := CubicNewBasis(Q,C);
R<x, y, u, v> := PolynomialRing(K, 4);
f1 := Evaluate(f1, [x*u, y*u, x*v, y*v]);
time I2 := InvariantsGenus4Curves(list_invariants, f1);
I2;

//indeed, the invariants are the same up to a small precision
J1, J2 := same_wps(list_invariants, I1, I2);

J1;
J2;

for i in [1..#J1] do
	ComplexField()!J1[i]-J2[i];
end for;

//here we suppose that 10^-9 = 0
Q := -0.696204170879482*X^2 - 8.92722674847333*I*X^2 - 50.7464824844223*X*Y + 58.7433272900886*I*X*Y - 57.8475326042462*X*Z - 32.3114052362709*I*X*Z + 0.696204169859874*X*T + 8.92722674924129*I*X*T + 47.4047605707472*Y^2 - 101.593270607375*I*Y^2 + 3.89862714549051*Y*T + 49.9909796383706*I*Y*T + 57.8475326039864*Z^2 + 32.311405236749*I*Z^2 + 57.8475326042301*Z*T + 32.3114052362822*I*Z*T + 1.25310940216974*T^2 + 16.0682630702241*I*T^2;
C := -234.90098969853*X^3 + 18.3191324015837*I*X^3 + 731.606628191784*X^2*Y + 478.455421156368*I*X^2*Y - 28.0203433984233*X^2*Z + 537.696155252943*I*X^2*Z + 352.35148455507*X^2*T - 27.4786985925642*I*X^2*T - 1147.27882034153*X*Y^2 - 485.876613084882*I*X*Y^2 + 562.593434153083*X*Y*Z - 32.1564704803837*I*X*Y*Z + 980.788369655334*X*Y*T - 92.8898492454102*I*X*Y*T + 28.0203433999316*X*Z^2 - 537.696155256996*I*X*Z^2 + 46.4622057542801*X*Z*T - 1058.24383026716*I*X*Z*T - 117.49502119373*X*T^2 + 9.16303864839564*I*X*T^2 + 125.61555530265*Y^3 - 446.88807153401*I*Y^3 + 26.7719595933429*Y^2*T + 14.3136325339934*I*Y^2*T - 562.593434151639*Y*Z^2 + 32.1564704772876*I*Y*Z^2 - 562.593434153289*Y*Z*T + 32.1564704813713*I*Y*Z*T - 537.802876178166*Y*T^2 + 41.9414243755401*I*Y*T^2 - 18.4418623558656*Z^2*T + 520.547675015364*I*Z^2*T - 18.4418623559262*Z*T^2 + 520.547675014923*I*Z*T^2 + 0.0222631708007216*T^3 - 0.00173622441208977*I*T^3;


//here we don't


//takes a random bicubic, a random change of variables, returns the set of invariants 
K := Rationals();
R0<x,y,u,v> := PolynomialRing(K, 4);
f0 := 0;
for i in [0..3] do
	for j in [0..3] do
		f0 := f0 + Random(-10, 10)*x^i*y^(3-i)*u^j*v^(3-j);
	end for;
end for;
a1 := Random(1,10);
b1 := Random(-10,10);
c1 := Random(-10,10);
d1 := (1-b1*c1)/a1;
a2 := Random(1,10);
b2 := Random(-10,10);
c2 := Random(-10,10);
d2 := (1-b2*c2)/a2;
f1 := Evaluate(f0, [a1*x+b1*y, c1*x+d1*y, a2*u+b2*v, c2*u+d2*v]);
f0;
f1;
I1 := eval_inv(list_invariants, f0);
I2 := eval_inv(list_invariants, f1);


//same invariants !
J1, J2 := same_wps(list_invariants, I1, I2);
for i in [1..#J1] do
	if J1[i]-J2[i] ne 0 then
		i, J1[i], J2[i];
	end if;
end for;


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


























