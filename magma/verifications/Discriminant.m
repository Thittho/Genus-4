K := Rationals();

S1<a33,a32,a31,a30,a23,a22,a21,a20,a13,a12,a11,a10,a03,a02,a01,a00> := PolynomialRing(K, [1 : i in [1..16]]);
S<x,y,u,v> := PolynomialRing(S1, 4);
f := a33*x^3*u^3+a32*x^3*u^2*v+a31*x^3*u*v^2+a30*x^3*v^3+a23*x^2*y*u^3+a22*x^2*y*u^2*v+a21*x^2*y*u*v^2+a20*x^2*y*v^3+a13*x*y^2*u^3+a12*x*y^2*u^2*v+a11*x*y^2*u*v^2+a10*x*y^2*v^3+a03*y^3*u^3+a02*y^3*u^2*v+a01*y^3*u*v^2+a00*y^3*v^3;

S<X,Y> := PolynomialRing(S1, [1,1]);

function matrice(g,m1,n1,m2,n2)
	res := ZeroMatrix(S1, (m1+1)*(n1+1), (m2+1)*(n2+1));
	for i1 in [0..m1] do
		for j1 in [0..n1] do
			for i2 in [0..m2] do
				for j2 in [0..n2] do
					res[i1+1+(m1+1)*j1][i2+1+(m2+1)*j2] := S1!MonomialCoefficient(X^(i1)*Y^(j2)*g, X^(i2)*Y^(j1));
				end for;
			end for;
		end for;
	end for;
	return Matrix(res);
end function;

function matrice_koszul(f, m, n)
	f1 := S!Derivative(f, 1, 1);	
	f2 := S!Derivative(f, 1, 2);
	d01 := m;
	d02 := n;
	d11 := d01-1;
	d12 := d02;
	d21 := d01;
	d22 := d02-1;
	M1 := -matrice(f1, d21-1, d02+d12-1, d11+d21-1, d02-1);
	M2 := matrice(f, d21-1, d02+d12-1, d01+d21-1, d12-1);
	M3 := ZeroMatrix(S1, d21*(d02+d12), d22*(d01+d11));
	res := HorizontalJoin(HorizontalJoin(M1,M2),M3);
	M4 := -matrice(f2, d11-1, d02+d22-1, d11+d21-1, d02-1);
	M5 := ZeroMatrix(S1, d11*(d02+d22), d12*(d01+d21));
	M6 := matrice(f, d11-1, d02+d22-1, d01+d11-1, d22-1);
	res := VerticalJoin(res, HorizontalJoin(HorizontalJoin(M4,M5),M6));
	M7 := ZeroMatrix(S1, d01*(d12+d22), d02*(d11+d21));
	M8 := -matrice(f2, d01-1, d12+d22-1, d01+d21-1, d12-1);
	M9 := matrice(f1, d01-1, d12+d22-1, d01+d11-1, d22-1);
	res := VerticalJoin(res, HorizontalJoin(HorizontalJoin(M7,M8),M9));
	return res;
end function;


function det_kos(f, m, n)
	M := matrice_koszul(f, m, n);
	L1 := Coefficients(f, X)[m+1];
	L2 := Coefficients(f, Y)[n+1];
	Disc1 := S1!Evaluate(Discriminant(L1, Y), [0,0]);
	Disc2 := S1!Evaluate(Discriminant(L2, X), [0,0]);
	return Determinant(M)/(Disc1*Disc2*MonomialCoefficient(f, X^m*Y^n));
end function;

/*
f := a11*X*Y+a10*X+a01*Y+a00;
L := Factorization(Determinant(matrice_koszul(f,1,1)));
L[#L][1]-det_kos(f,1,1);

f := a12*X*Y^2+a11*X*Y+a10*X+a02*Y^2+a01*Y+a00;
L := Factorization(Determinant(matrice_koszul(f,1,2)));
L[#L][1]-det_kos(f,1,2);

f := a22*X^2*Y^2+a21*X^2*Y+a20*X^2+a12*X*Y^2+a11*X*Y+a10*X+a02*Y^2+a01*Y+a00;
L := Factorization(Determinant(matrice_koszul(f,2,2)));
L[#L][1]-det_kos(f,2,2);


f := a33*X^3*Y^3+a32*X^3*Y^2+a31*X^3*Y+a30*X^3+a23*X^2*Y^3+a22*X^2*Y^2+a21*X^2*Y+a20*X^2+a13*X*Y^3+a12*X*Y^2+a11*X*Y+a10*X+a03*Y^3+a02*Y^2+a01*Y+a00;
res := det_kos(f,3,3);
*/

function FormsGenerator(n,K)
	R<x, y, u, v> := PolynomialRing(K, 4);
    res0 := [x^3*u^2*v+x^2*y*u^3+a21*x^2*y*u*v^2+a20*x^2*y*v^3+a13*x*y^2*u^3+a12*x*y^2*u^2*v+a11*x*y^2*u*v^2+a10*x*y^2*v^3+a03*y^3*u^3+a02*y^3*u^2*v+a01*y^3*u*v^2+a00*y^3*v^3 : a21 in [1..3], a20 in [1..3], a13 in [1..3], a12 in [1..3], a11 in [1..3], a10 in [1..3], a03 in [1..3], a02 in [1..3], a01 in [1..3], a00 in [1..3]];
	res := [];
	i := 1;
	while #res lt n do
		f := Evaluate(res0[i], [1, X, 1, Y]);
		L1 := Coefficients(f, X)[4];
		L2 := Coefficients(f, Y)[4];
		Disc1 := S1!Evaluate(Discriminant(L1, Y), [0,0]);
		Disc2 := S1!Evaluate(Discriminant(L2, X), [0,0]);
		if Disc1*Disc2*MonomialCoefficient(f, X^3*Y^3) ne 0 then
			Append(~res, res0[i]);
		end if;
		i +:= 1;
	end while;
	return res[1..n];
end function;

function FormsGenerator2(n,K)
	R<x, y, u, v> := PolynomialRing(K, 4);
	res := [];
	for i in [1..n] do
		a21 := Random(K);
		a20 := Random(K);
		a13 := Random(K);
		a12 := Random(K);
		a11 := Random(K);
		a10 := Random(K);
		a03 := Random(K);
		a02 := Random(K);
		a01 := Random(K);
		a00 := Random(K);
		Append(~res, x^3*u^2*v+x^2*y*u^3+a21*x^2*y*u*v^2+a20*x^2*y*v^3+a13*x*y^2*u^3+a12*x*y^2*u^2*v+a11*x*y^2*u*v^2+a10*x*y^2*v^3+a03*y^3*u^3+a02*y^3*u^2*v+a01*y^3*u*v^2+a00*y^3*v^3);
	end for;
    return res;
end function;



function ProdScal(f1, f2)
	L := Monomials(f1);
	S := 0;
	for l in L do
		S +:= MonomialCoefficient(f1, l)*MonomialCoefficient(f2, l);
	end for;
	return S;
end function;

function Invariants(f)
	K := BaseRing(Parent(f));
	
    GCD_hsop := [288, 12288, 746496, 12582912, 1741425868800, 19327352832, 764411904, 97844723712, 570630428688384, 901736973729792];
	GCD_others := [4718592, 679477248, 3057647616, 97844723712, 440301256704, 660451885056, 1981355655168, 2972033482752, 4458050224128, 3131031158784, 28179280429056, 21134460321792, 3131031158784, 42268920643584, 21134460321792, 225434243432448, 1014454095446016, 1521681143169024, 400771988324352, 100192997081088, 2705210921189376, 1352605460594688, 18260173718028288, 10820843684757504, 146081389744226304, 73040694872113152, 657366253849018368, 986049380773527552, 493024690386763776, 14427791579676672, 692533995824480256, 9349208943630483456, 4674604471815241728, 346266997912240128, 4674604471815241728, 7011906707722862592, 10517860061584293888, 94660740554258644992, 47330370277129322496, 70995555415693983744, 425973332494163902464, 638959998741245853696, 319479999370622926848, 1437659997167803170816, 44322175732766736384, 99724895398725156864, 448762029294263205888, 673143043941394808832, 6058287395472553279488, 3029143697736276639744, 4543715546604414959616, 22161087866383368192, 11080543933191684096, 224381014647131602944, 3029143697736276639744];

	Jac := Transvectant(f, f, 1, 1);
	H := Transvectant(f, f, 2, 2);

	// Covariants
	// Degree 3
	c31 := Transvectant(H, f, 2, 2);

	c331 := Transvectant(Jac, f, 2, 2);
	c332 := Transvectant(H, f, 1, 1);

	// Degree 4
	c421 := Transvectant(H, H, 1, 1);
	c422 := Transvectant(c31, f, 1, 1);
	c423 := Transvectant(c332, f, 2, 2);

	c441 := Transvectant(c332, f, 1, 1);
	c442 := Transvectant(Transvectant(Jac, f, 1, 1), f, 2, 2);

	// Degree 5
	c511 := Transvectant(c422, f, 2, 2);
	c512 := Transvectant(c441, f, 3, 3);
	c513 := Transvectant(c442, f, 3, 3);

	c531 := Transvectant(c422, f, 1, 1);
	c532 := Transvectant(c423, f, 1, 1);
	c533 := Transvectant(Transvectant(f^3, f, 3, 3), f, 3, 3);

	// Degree 6
	c621 := Transvectant(c531, f, 2, 2);
	c622 := Transvectant(c532, f, 2, 2);
	c623 := Transvectant(c511, f, 1, 1);

	// Degree 7
	c711 := Transvectant(c621, f, 2, 2);
	c712 := Transvectant(c511, Transvectant(f, f, 2, 2), 1, 1);
	c713 := Transvectant(c512, Transvectant(f, f, 2, 2), 1, 1);
    
	c731 := Transvectant(c622, f, 1, 1);
	c732 := Transvectant(c623, f, 1, 1);

	// Degree 8 
	c821 := Transvectant(c711, f, 1, 1);
	c822 := Transvectant(c732, f, 2, 2);

	c84 := Transvectant(c731, f, 1, 1);

	// Degree 9
	c91 := Transvectant(c822, f, 2, 2);
	
	c931 := Transvectant(c821, f, 1, 1);
	c932 := Transvectant(c84, f, 2, 2);

	// Degree 10
	c102 := Transvectant(c91, f, 1, 1);

	// Degree 11
	c111 := Transvectant(c102, f, 2, 2);

	c113 := Transvectant(c932*f, f, 3, 3);

	// Invariants
	// HSOP
	I2 := Transvectant(f, f, 3, 3 : invariant := true);
	I41 := Transvectant(H, H, 2, 2 : invariant := true);
	I42 := Transvectant(c331, f, 3, 3 : invariant := true);	
	I61 := Transvectant(H, c421, 2, 2 : invariant := true);
	I62 := Transvectant(c533, f, 3, 3 : invariant :=  true);
	I81 := Transvectant(c421, c421, 2, 2 : invariant := true);
	I82 := Transvectant(c731, f, 3, 3 : invariant := true);
	I10 := Transvectant(f, c31^3, 3, 3 : invariant := true);
	I12 := Transvectant(c113, f, 3, 3 : invariant := true);
	I14 := Transvectant(c111*H, f, 3, 3 : invariant := true);
	invHSOP := [K | I2,I41,I42,I61,I62,I81,I82,I10,I12,I14];

	// Degree 6
	j61 := Transvectant(c31, c31, 1, 1 : invariant := true);
	inv6 := [K | j61];

	// Degree 8
	j81 := Transvectant(c31, c511, 1, 1 : invariant := true);
	j82 := Transvectant(c31, c512, 1, 1 : invariant := true);
	inv8 := [K | j81,j82];
	
	// Degree 10
	j101 := Transvectant(c511, c511, 1, 1 : invariant := true);
    j102 := Transvectant(c511, c512, 1, 1 : invariant := true);
    j103 := Transvectant(c511, c513, 1, 1 : invariant := true);
    j104 := Transvectant(c512, c512, 1, 1 : invariant := true);
    j105 := Transvectant(c512, c513, 1, 1 : invariant := true);
    j106 := Transvectant(c513, c513, 1, 1 : invariant := true);
	inv10 := [K | j101,j102,j103,j104,j105,j106];

	// Degree 12	
    j121 := Transvectant(c711, c511, 1, 1 : invariant := true);
    j122 := Transvectant(c711, c512, 1, 1 : invariant := true);
    j123 := Transvectant(c711, c513, 1, 1 : invariant := true);
    j124 := Transvectant(c712, c511, 1, 1 : invariant := true);
    j125 := Transvectant(c712, c512, 1, 1 : invariant := true);
    j126 := Transvectant(c712, c513, 1, 1 : invariant := true);
    j127 := Transvectant(f, c511*c31^2, 3, 3 : invariant := true);
    j128 := Transvectant(f, c512*c31^2, 3, 3 : invariant := true);
    j129 := Transvectant(f, c513*c31^2, 3, 3 : invariant := true);
	inv12 := [K | j121,j122,j123,j124,j125,j126,j127,j128,j129];

	// Degree 14
	j141 := Transvectant(c711, c711, 1, 1 : invariant := true);
    j142 := Transvectant(c711, c712, 1, 1 : invariant := true);
	j143 := Transvectant(c711, c713, 1, 1 : invariant := true);
    j144 := Transvectant(c712, c713, 1, 1 : invariant := true);
	j145 := Transvectant(c713, c713, 1, 1 : invariant := true);
    j146 := Transvectant(f, c511*c511*c31, 3, 3 : invariant := true);
    j147 := Transvectant(f, c511*c512*c31, 3, 3 : invariant := true);
    j148 := Transvectant(f, c511*c513*c31, 3, 3 : invariant := true);
    j149 := Transvectant(f, c512*c512*c31, 3, 3 : invariant := true);
    j1410 := Transvectant(f, c512*c513*c31, 3, 3 : invariant := true);
    j1411 := Transvectant(f, c513*c513*c31, 3, 3 : invariant := true);
    j1412 := Transvectant(f, c711*c31*c31, 3, 3 : invariant := true);
	inv14 := [K | j141,j142,j143,j144,j145,j146,j147,j148,j149,j1410,j1411,j1412];

	// Degree 16
	j161 := Transvectant(f, c711*c511*c31, 3, 3 : invariant := true);
    j162 := Transvectant(f, c711*c512*c31, 3, 3 : invariant := true);
    j163 := Transvectant(f, c711*c513*c31, 3, 3 : invariant := true);
    j164 := Transvectant(f, c712*c511*c31, 3, 3 : invariant := true);
    j165 := Transvectant(f, c511*c511*c511, 3, 3 : invariant := true);
    j166 := Transvectant(f, c511*c511*c512, 3, 3 : invariant := true);
    j167 := Transvectant(f, c511*c511*c513, 3, 3 : invariant := true);
    j168 := Transvectant(f, c511*c512*c512, 3, 3 : invariant := true);
    j169 := Transvectant(f, c511*c512*c513, 3, 3 : invariant := true);
    j1610 := Transvectant(f, c511*c513*c513, 3, 3 : invariant := true);
    j1611 := Transvectant(f, c512*c512*c512, 3, 3 : invariant := true);
    j1612 := Transvectant(f, c512*c512*c513, 3, 3 : invariant := true);
    j1613 := Transvectant(f, c512*c513*c513, 3, 3 : invariant := true);
    j1614 := Transvectant(f, c513*c513*c513, 3, 3 : invariant := true);
    inv16 := [K | j161,j162,j163,j164,j165,j166,j167,j168,j169,j1610,j1611,j1612,j1613,j1614];

   
	// Degree 18
	j181 := Transvectant(f, c711*c711*c31, 3, 3 : invariant := true);
	j182 := Transvectant(f, c711*c511*c511, 3, 3 : invariant := true);
	j183 := Transvectant(f, c711*c511*c512, 3, 3 : invariant := true);
	j184 := Transvectant(f, c711*c511*c513, 3, 3 : invariant := true);
	j185 := Transvectant(f, c711*c512*c512, 3, 3 : invariant := true);
    j186 := Transvectant(f, c711*c512*c513, 3, 3 : invariant := true);
	j187 := Transvectant(f, c711*c513*c513, 3, 3 : invariant := true);
	j188 := Transvectant(f, c711*c712*c31, 3, 3 : invariant := true);
	j189 := Transvectant(f, c712*c712*c31, 3, 3 : invariant := true);
	j1810 := Transvectant(f, c712*c511*c512, 3, 3 : invariant := true);
	j1811 := Transvectant(f, c712*c512*c512, 3, 3 : invariant := true);
	inv18 := [K | j181,j182,j183,j184,j185,j186,j187,j188,j189,j1810,j1811];

	invOthers := inv6 cat inv8 cat inv10 cat inv12 cat inv14 cat inv16 cat inv18;

	return [ExactQuotient(invHSOP[i], GCD_hsop[i]) : i in [1..#invHSOP]], [ExactQuotient(invOthers[i], GCD_others[i]) : i in [1..#invOthers]];
end function;
	

function Degree_m(L, m)
	n := Min(Max(L), m);
	liste_ind := [[] : i in [1.. n]];

	for k in [1..#L] do
		if L[k] le n then
			Append(~liste_ind[L[k]], k);
		end if;
	end for;
	
	set_degrees := Set(L);
	S := RestrictedPartitions(m, set_degrees);
	res := [];
	
	for part in S do
		res_int := [[liste_ind[part[1]][i]] : i in [1..#liste_ind[part[1]]]];
		
		for i in [2..#part] do
			res_int := [r cat [s] : r in res_int, s in liste_ind[part[i]]];
		end for;
		
		res cat:= res_int;
	end for;
	res := SetToSequence(Set([Sort(el) : el in res]));
	return res;
end function;


function EvaluationInvariants(forms)
	res_hsop := [];
	res_inv := [];
	for L in forms do
		Hsop1, Inv1 := Invariants(L);
		Append(~res_hsop, Hsop1);
		Append(~res_inv, Inv1);
	end for;
	return res_hsop, res_inv;
end function;


function UpdateDual(N, p)
	i := 1;
	while p[i] eq 0 do
		i := i+1;
	end while;
	res := [];
	for j in [1..Nrows(N)] do
		if i ne j then
			Append(~res, N[j]-p[j]/p[i]*N[i]);
		end if;
	end for;
	return Matrix(res);
end function;


function EvaluationSecondaryInvariants(L, j, list_values)
	length := #L;
	if length eq 1 then
		return list_values[j][L[1]];
	else
		prod1 := list_values[j][L[1]]*list_values[j][L[2]];
		for i in [3..length] do
			prod1 := prod1*list_values[j][L[i]];
		end for;
		return prod1;
	end if;
end function;


// To compute the invariants of a certain degree that come from the HSOP
function InvariantsValuedHSOP(list_valued, forms, d, borne, L_inv34)
	list_deg_hsop := [2,4,4,6,6,8,8,10,12,14];
	anciens := Degree_m(list_deg_hsop, d);
	m := #anciens;
	res_sym := ZeroMatrix( K, borne, m);
	for i in [1..m] do
		g := anciens[i];
		if d eq 34 then
			Append(~L_inv34, g);
		end if;
		for j in [1..borne] do
			el := EvaluationSecondaryInvariants(g, j, list_valued);
			res_sym[j, i] := el;
		end for;
	end for;
	return res_sym, L_inv34;
end function;


function InvariantsValuedOthers(list_valued_hsop, list_valued_others, inv_sec, forms, d, n, borne, L_inv34)// To evaluate the products of hsop and secondary
	list_deg_hsop := [2,4,4,6,6,8,8,10,12,14];
	list_deg := [6,8,8,10,10,10,10,10,10,12,12,12,12,12,12,12,12,12,14,14,14,14,14,14,14,14,14,14,14,14,16,16,16,16,16,16,16,16,16,16,16,16,16,16,18,18,18,18,18,18,18,18,18,18,18];
	if d eq 0 then
		anciens_hsop := [[1 : i in [1..borne]]];
	else
		anciens_hsop := Degree_m(list_deg_hsop, d);
	end if;
	m_hsop := #anciens_hsop;

	anciens_autres := [];
	for i in [1..#inv_sec] do
		s := 0;
		for l in inv_sec[i] do
			s +:= list_deg[l];
		end for;
		if s eq n-d then
			Append(~anciens_autres, i);
		end if;
	end for;

	m_autres := #anciens_autres;
	res_sym := ZeroMatrix(K, borne, m_hsop*m_autres);
	for i in [1..m_hsop] do
		g := anciens_hsop[i];
		for j in [1..borne] do
			res_int := EvaluationSecondaryInvariants(g, j, list_valued_hsop);
			for k in [1..m_autres] do
				if j eq 1 then
					Append(~L_inv34, [*g, anciens_autres[k]*]);
				end if;
				el := EvaluationSecondaryInvariants(inv_sec[anciens_autres[k]], j, list_valued_others);
				res_sym[j, m_autres*(i-1)+k] := res_int*el;
			end for;
		end for;
	end for;
	return res_sym, L_inv34;
end function;

function ToSec(l, L)
	res := L[l[1]];
	for i in [2..#l] do
		res cat:= L[l[i]];
	end for;
	return res;
end function;


function invariants_secondaires_non_sym(inv_sec, forms, list_valued_hsop, list_valued_others, list_valued_inv_sec, L, n, L_inv34)
	m := L[n+1];
	list_deg := [6,8,8,10,10,10,10,10,10,12,12,12,12,12,12,12,12,12,14,14,14,14,14,14,14,14,14,14,14,14,16,16,16,16,16,16,16,16,16,16,16,16,16,16,18,18,18,18,18,18,18,18,18,18,18];
	M_sym, L_inv34 := InvariantsValuedHSOP(list_valued_hsop, forms, n, m+10, L_inv34);
	for d in [2..n-6] do
		d;
		if d mod 2 eq 0 then
			M0_sym, L_inv34 := InvariantsValuedOthers(list_valued_hsop, list_valued_others, inv_sec, forms, d, n, m+10, L_inv34);
			M_sym := HorizontalJoin(M_sym, M0_sym);
		end if;
	end for;

	deg := [];
	for i in [1..#inv_sec] do
		s := 0;
		for l in inv_sec[i] do
			s := s+list_deg[l];
		end for;
		if s eq n then
			Append(~deg, i);
		end if;
	end for;
	
	for i in deg do
		Append(~L_inv34, inv_sec[i]);
	end for;

	M0_sym := Matrix(K, [[list_valued_inv_sec[j][i] : i in deg] : j in [1..m+10]]);
	M_sym := HorizontalJoin(M_sym, M0_sym);

	time V_sym := Matrix(K, [[det_kos(S!Evaluate(forms[j], [1, -X, 1, -Y]), 3, 3)] : j in [1..m+10]]);
	M_sym := HorizontalJoin(M_sym, V_sym);

	time M_sym2 := EchelonForm(M_sym);
	return L_inv34, M_sym2;
end function;


function FirstOneRow(M)
	res := [];
	i := 1;
	while i le Min(Ncols(M), Nrows(M)) and #res lt 18928 do
		j := i;
		while j lt Ncols(M) and M[i,j] ne 1 do
			j +:= 1;
		end while;
		if M[i,j] eq 1 then
			Append(~res, j);
		end if;
		i +:= 1;
	end while;
	return res;
end function;


function Product2(el1, el2)
	res := "";
	for i in [1..#el1] do
		res := res cat "*L[" cat Sprint(el1[i]) cat "]"; 
	end for;
	for i in [1..#el2] do
		res := res cat "*L[" cat Sprint(el2[i]+10) cat "]"; 
	end for;
	return res;
end function;


function Producthsop(el)
	res := "";
	for i in [1..#el] do
		res := res cat"*L[" cat Sprint(el[i]) cat "]"; 
	end for;
	return res;
end function;


function Productothers(el)
	res := "";
	for i in [1..#el] do
		res := res cat"*L[" cat Sprint(el[i]+10) cat "]"; 
	end for;
	return res;
end function;


function DecompositionInv(L, M)
	s := "function discrim(L)\n decompo := ";
	m := Nrows(M);
	n := Ncols(M);
	list_dec := [M[i,n] : i in [1..m]];
	for i in [1..n-1] do
		if Type(L[i][1]) eq SeqEnum then
			Lhsop := L[i][1];
			Lothers := L[i][2];
			if list_dec[i] lt 0 then
				s := s cat Sprint(list_dec[i]) cat Product2(Lhsop, Lothers);
			else
				if i gt 1 then
					s := s cat "+" cat Sprint(list_dec[i]) cat Product2(Lhsop, Lothers);
				else 
					s := s cat Sprint(list_dec[i]) cat Product2(Lhsop, Lothers);
				end if;
			end if;
		elif i lt m/2 then
			Lhsop := L[i];
			if list_dec[i] lt 0 then
				s := s cat Sprint(list_dec[i]) cat Producthsop(Lhsop);
			else
				s := s cat "+" cat Sprint(list_dec[i]) cat Producthsop(Lhsop);
			end if;
		else
			Lothers := L[i];
			if list_dec[i] lt 0 then
				s := s cat Sprint(list_dec[i]) cat Productothers(Lothers);
			else
				s := s cat "+" cat Sprint(list_dec[i]) cat Productothers(Lothers);
			end if;
		end if;
	end for;
	s := s cat ";\n return decompo;\n end function;";
	return s;
end function;

L1 := [1, 0, 1, 0, 3, 0, 6, 0, 13, 0, 26, 0, 54, 0, 102, 0, 196, 0, 358, 0, 641, 0, 1113, 0, 1892, 0, 3124, 0, 5059, 0, 8006, 0, 12428, 0, 18928, 0, 28348, 0, 41754, 0, 60609, 0, 86732, 0, 122515, 0, 170944, 0, 235824, 0, 321820, 0, 434811, 0, 581904, 0, 771864, 0, 1015241];

inv_sec := [[ 1 ], [ 2 ], [ 3 ], [ 4 ], [ 5 ], [ 6 ], [ 7 ], [ 8 ], [ 9 ], [ 10 ], [ 11 ], [ 12 ], [ 13 ], [ 14 ], [ 15 ], [ 16 ], [ 17 ], [ 18 ], [ 19 ], [ 20 ], [ 21 ], [ 22 ], [ 23 ], [ 24 ], [ 25 ], [ 26 ], [ 27 ], [ 28 ], [ 29 ], [ 30 ], [ 31 ], [ 32 ], [ 33 ], [ 34 ], [ 35 ], [ 36 ], [ 37 ], [ 38 ], [ 39 ], [ 40 ], [ 41 ], [ 42 ], [ 43 ], [ 44 ], [ 45 ], [ 46 ], [ 47 ], [ 48 ], [ 49 ], [ 50 ], [ 51 ], [ 52 ], [ 53 ], [ 54 ], [ 55 ], [ 1, 1 ], [ 2, 1 ], [ 3, 1 ], [ 4, 1 ], [ 5, 1 ], [ 6, 1 ], [ 7, 1 ], [ 8, 1 ], [ 9, 1 ], [ 2, 2 ], [ 3, 2 ], [ 3, 3 ], [ 10, 1 ], [ 11, 1 ], [ 12, 1 ], [ 13, 1 ], [ 14, 1 ], [ 15, 1 ], [ 16, 1 ], [ 17, 1 ], [ 18, 1 ], [ 1, 1, 1 ], [ 4, 2 ], [ 5, 2 ], [ 6, 2 ], [ 7, 2 ], [ 8, 2 ], [ 9, 2 ], [ 4, 3 ], [ 5, 3 ], [ 6, 3 ], [ 7, 3 ], [ 8, 3 ], [ 9, 3 ], [ 19, 1 ], [ 20, 1 ], [ 21, 1 ], [ 22, 1 ], [ 23, 1 ], [ 24, 1 ], [ 25, 1 ], [ 26, 1 ], [ 27, 1 ], [ 28, 1 ], [ 29, 1 ], [ 30, 1 ], [ 2, 1, 1 ], [ 3, 1, 1 ], [ 10, 2 ], [ 11, 2 ], [ 12, 2 ], [ 13, 2 ], [ 14, 2 ], [ 15, 2 ], [ 16, 2 ], [ 17, 2 ], [ 18, 2 ], [ 10, 3 ], [ 11, 3 ], [ 12, 3 ], [ 13, 3 ], [ 14, 3 ], [ 15, 3 ], [ 16, 3 ], [ 17, 3 ], [ 18, 3 ], [ 4, 4 ], [ 5, 4 ], [ 6, 4 ], [ 7, 4 ], [ 8, 4 ], [ 9, 4 ], [ 5, 5 ], [ 6, 5 ], [ 7, 5 ], [ 8, 5 ], [ 9, 5 ], [ 6, 6 ], [ 7, 6 ], [ 31, 1 ], [ 32, 1 ], [ 33, 1 ], [ 34, 1 ], [ 35, 1 ], [ 36, 1 ], [ 37, 1 ], [ 38, 1 ], [ 39, 1 ], [ 40, 1 ], [ 41, 1 ], [ 42, 1 ], [ 43, 1 ], [ 44, 1 ], [ 4, 1, 1 ], [ 5, 1, 1 ], [ 6, 1, 1 ], [ 7, 1, 1 ], [ 8, 1, 1 ], [ 9, 1, 1 ], [ 2, 2, 1 ], [ 3, 2, 1 ], [ 3, 3, 1 ], [ 19, 2 ], [ 20, 2 ], [ 21, 2 ], [ 22, 2 ], [ 23, 2 ], [ 24, 2 ], [ 25, 2 ], [ 26, 2 ], [ 27, 2 ], [ 28, 2 ], [ 29, 2 ], [ 30, 2 ], [ 19, 3 ], [ 20, 3 ], [ 21, 3 ], [ 22, 3 ], [ 23, 3 ], [ 24, 3 ], [ 25, 3 ], [ 26, 3 ], [ 27, 3 ], [ 28, 3 ], [ 29, 3 ], [ 30, 3 ], [ 10, 4 ], [ 11, 4 ], [ 12, 4 ], [ 13, 4 ], [ 14, 4 ], [ 15, 4 ], [ 16, 4 ], [ 17, 4 ], [ 18, 4 ], [ 10, 5 ], [ 11, 5 ], [ 12, 5 ], [ 13, 5 ], [ 14, 5 ], [ 45, 1 ], [ 46, 1 ], [ 47, 1 ], [ 48, 1 ], [ 49, 1 ], [ 50, 1 ], [ 51, 1 ], [ 52, 1 ], [ 53, 1 ], [ 54, 1 ], [ 55, 1 ], [ 10, 1, 1 ], [ 11, 1, 1 ], [ 12, 1, 1 ], [ 13, 1, 1 ], [ 14, 1, 1 ], [ 15, 1, 1 ], [ 16, 1, 1 ], [ 17, 1, 1 ], [ 18, 1, 1 ], [ 1, 1, 1, 1 ], [ 4, 2, 1 ], [ 5, 2, 1 ], [ 6, 2, 1 ], [ 7, 2, 1 ], [ 8, 2, 1 ], [ 9, 2, 1 ], [ 4, 3, 1 ], [ 5, 3, 1 ], [ 6, 3, 1 ], [ 7, 3, 1 ], [ 8, 3, 1 ], [ 9, 3, 1 ], [ 31, 2 ], [ 32, 2 ], [ 33, 2 ], [ 34, 2 ], [ 35, 2 ], [ 36, 2 ], [ 37, 2 ], [ 38, 2 ], [ 39, 2 ], [ 40, 2 ], [ 41, 2 ], [ 42, 2 ], [ 43, 2 ], [ 44, 2 ], [ 2, 2, 2 ], [ 3, 2, 2 ], [ 3, 3, 2 ], [ 31, 3 ], [ 32, 3 ], [ 33, 3 ], [ 34, 3 ], [ 35, 3 ], [ 36, 3 ], [ 37, 3 ], [ 38, 3 ], [ 39, 3 ], [ 40, 3 ], [ 41, 3 ], [ 42, 3 ], [ 43, 3 ], [ 44, 3 ], [ 3, 3, 3 ], [ 19, 4 ], [ 20, 4 ], [ 21, 4 ], [ 22, 4 ], [ 23, 4 ], [ 24, 4 ], [ 25, 4 ], [ 26, 4 ], [ 27, 4 ], [ 28, 4 ], [ 19, 1, 1 ], [ 20, 1, 1 ], [ 21, 1, 1 ], [ 22, 1, 1 ], [ 23, 1, 1 ], [ 24, 1, 1 ], [ 25, 1, 1 ], [ 26, 1, 1 ], [ 27, 1, 1 ], [ 28, 1, 1 ], [ 29, 1, 1 ], [ 30, 1, 1 ], [ 2, 1, 1, 1 ], [ 3, 1, 1, 1 ], [ 10, 2, 1 ], [ 11, 2, 1 ], [ 12, 2, 1 ], [ 13, 2, 1 ], [ 14, 2, 1 ], [ 15, 2, 1 ], [ 16, 2, 1 ], [ 17, 2, 1 ], [ 18, 2, 1 ], [ 10, 3, 1 ], [ 11, 3, 1 ], [ 12, 3, 1 ], [ 13, 3, 1 ], [ 14, 3, 1 ], [ 15, 3, 1 ], [ 16, 3, 1 ], [ 17, 3, 1 ], [ 18, 3, 1 ], [ 4, 4, 1 ], [ 5, 4, 1 ], [ 6, 4, 1 ], [ 7, 4, 1 ], [ 8, 4, 1 ], [ 9, 4, 1 ], [ 5, 5, 1 ], [ 6, 5, 1 ], [ 7, 5, 1 ], [ 8, 5, 1 ], [ 9, 5, 1 ], [ 6, 6, 1 ], [ 7, 6, 1 ], [ 45, 2 ], [ 46, 2 ], [ 47, 2 ], [ 48, 2 ], [ 49, 2 ], [ 50, 2 ], [ 51, 2 ], [ 52, 2 ], [ 53, 2 ], [ 54, 2 ], [ 55, 2 ], [ 4, 2, 2 ], [ 5, 2, 2 ], [ 6, 2, 2 ], [ 7, 2, 2 ], [ 8, 2, 2 ], [ 9, 2, 2 ], [ 4, 3, 2 ], [ 5, 3, 2 ], [ 6, 3, 2 ], [ 7, 3, 2 ], [ 8, 3, 2 ], [ 9, 3, 2 ], [ 45, 3 ], [ 46, 3 ], [ 47, 3 ], [ 48, 3 ], [ 49, 3 ], [ 50, 3 ], [ 51, 3 ], [ 52, 3 ], [ 53, 3 ], [ 54, 3 ], [ 55, 3 ], [ 4, 3, 3 ], [ 5, 3, 3 ], [ 6, 3, 3 ], [ 7, 3, 3 ], [ 8, 3, 3 ], [ 9, 3, 3 ], [ 31, 4 ], [ 32, 4 ], [ 31, 1, 1 ], [ 32, 1, 1 ], [ 33, 1, 1 ], [ 34, 1, 1 ], [ 35, 1, 1 ], [ 36, 1, 1 ], [ 37, 1, 1 ], [ 38, 1, 1 ], [ 39, 1, 1 ], [ 40, 1, 1 ], [ 41, 1, 1 ], [ 42, 1, 1 ], [ 43, 1, 1 ], [ 44, 1, 1 ], [ 4, 1, 1, 1 ], [ 5, 1, 1, 1 ], [ 6, 1, 1, 1 ], [ 7, 1, 1, 1 ], [ 8, 1, 1, 1 ], [ 9, 1, 1, 1 ], [ 2, 2, 1, 1 ], [ 3, 2, 1, 1 ], [ 3, 3, 1, 1 ], [ 19, 2, 1 ], [ 20, 2, 1 ], [ 21, 2, 1 ], [ 22, 2, 1 ], [ 23, 2, 1 ], [ 24, 2, 1 ], [ 25, 2, 1 ], [ 26, 2, 1 ], [ 27, 2, 1 ], [ 28, 2, 1 ], [ 29, 2, 1 ], [ 30, 2, 1 ], [ 19, 3, 1 ], [ 20, 3, 1 ], [ 21, 3, 1 ], [ 22, 3, 1 ], [ 23, 3, 1 ], [ 24, 3, 1 ], [ 25, 3, 1 ], [ 26, 3, 1 ], [ 27, 3, 1 ], [ 28, 3, 1 ], [ 29, 3, 1 ], [ 30, 3, 1 ], [ 10, 4, 1 ], [ 11, 4, 1 ], [ 12, 4, 1 ], [ 13, 4, 1 ], [ 14, 4, 1 ], [ 15, 4, 1 ], [ 16, 4, 1 ], [ 17, 4, 1 ], [ 18, 4, 1 ], [ 10, 5, 1 ], [ 11, 5, 1 ], [ 12, 5, 1 ], [ 13, 5, 1 ], [ 14, 5, 1 ], [ 10, 2, 2 ], [ 11, 2, 2 ], [ 12, 2, 2 ], [ 13, 2, 2 ], [ 14, 2, 2 ], [ 15, 2, 2 ], [ 16, 2, 2 ], [ 17, 2, 2 ], [ 18, 2, 2 ], [ 10, 3, 2 ], [ 11, 3, 2 ], [ 12, 3, 2 ], [ 13, 3, 2 ], [ 14, 3, 2 ], [ 15, 3, 2 ], [ 16, 3, 2 ], [ 17, 3, 2 ], [ 18, 3, 2 ], [ 4, 4, 2 ], [ 5, 4, 2 ], [ 6, 4, 2 ], [ 7, 4, 2 ], [ 8, 4, 2 ], [ 9, 4, 2 ], [ 5, 5, 2 ], [ 6, 5, 2 ], [ 7, 5, 2 ], [ 8, 5, 2 ], [ 9, 5, 2 ], [ 6, 6, 2 ], [ 7, 6, 2 ], [ 10, 3, 3 ], [ 11, 3, 3 ], [ 12, 3, 3 ], [ 13, 3, 3 ], [ 45, 1, 1 ], [ 46, 1, 1 ], [ 47, 1, 1 ], [ 48, 1, 1 ], [ 49, 1, 1 ], [ 50, 1, 1 ], [ 51, 1, 1 ], [ 52, 1, 1 ], [ 53, 1, 1 ], [ 54, 1, 1 ], [ 55, 1, 1 ], [ 10, 1, 1, 1 ], [ 11, 1, 1, 1 ], [ 12, 1, 1, 1 ], [ 13, 1, 1, 1 ], [ 14, 1, 1, 1 ], [ 15, 1, 1, 1 ], [ 16, 1, 1, 1 ], [ 17, 1, 1, 1 ], [ 18, 1, 1, 1 ], [ 1, 1, 1, 1, 1 ], [ 4, 2, 1, 1 ], [ 5, 2, 1, 1 ], [ 6, 2, 1, 1 ], [ 7, 2, 1, 1 ], [ 8, 2, 1, 1 ], [ 9, 2, 1, 1 ], [ 4, 3, 1, 1 ], [ 5, 3, 1, 1 ], [ 6, 3, 1, 1 ], [ 7, 3, 1, 1 ], [ 8, 3, 1, 1 ], [ 9, 3, 1, 1 ], [ 31, 2, 1 ], [ 32, 2, 1 ], [ 33, 2, 1 ], [ 34, 2, 1 ], [ 35, 2, 1 ], [ 36, 2, 1 ], [ 37, 2, 1 ], [ 38, 2, 1 ], [ 39, 2, 1 ], [ 40, 2, 1 ], [ 41, 2, 1 ], [ 42, 2, 1 ], [ 43, 2, 1 ], [ 44, 2, 1 ], [ 2, 2, 2, 1 ], [ 3, 2, 2, 1 ], [ 3, 3, 2, 1 ], [ 31, 3, 1 ], [ 32, 3, 1 ], [ 33, 3, 1 ], [ 34, 3, 1 ], [ 35, 3, 1 ], [ 36, 3, 1 ], [ 37, 3, 1 ], [ 38, 3, 1 ], [ 39, 3, 1 ], [ 40, 3, 1 ], [ 41, 3, 1 ], [ 42, 3, 1 ], [ 43, 3, 1 ], [ 44, 3, 1 ], [ 3, 3, 3, 1 ], [ 19, 4, 1 ], [ 20, 4, 1 ], [ 21, 4, 1 ], [ 22, 4, 1 ], [ 23, 4, 1 ], [ 24, 4, 1 ], [ 25, 4, 1 ], [ 26, 4, 1 ], [ 27, 4, 1 ], [ 28, 4, 1 ], [ 19, 2, 2 ], [ 20, 2, 2 ], [ 21, 2, 2 ], [ 22, 2, 2 ], [ 23, 2, 2 ], [ 24, 2, 2 ], [ 25, 2, 2 ], [ 26, 2, 2 ], [ 27, 2, 2 ], [ 28, 2, 2 ], [ 29, 2, 2 ], [ 30, 2, 2 ], [ 19, 3, 2 ], [ 20, 3, 2 ], [ 21, 3, 2 ], [ 22, 3, 2 ], [ 23, 3, 2 ], [ 24, 3, 2 ], [ 25, 3, 2 ], [ 26, 3, 2 ], [ 27, 3, 2 ], [ 28, 3, 2 ], [ 29, 3, 2 ], [ 30, 3, 2 ], [ 19, 1, 1, 1 ], [ 20, 1, 1, 1 ], [ 21, 1, 1, 1 ], [ 22, 1, 1, 1 ], [ 23, 1, 1, 1 ], [ 24, 1, 1, 1 ], [ 25, 1, 1, 1 ], [ 26, 1, 1, 1 ], [ 27, 1, 1, 1 ], [ 28, 1, 1, 1 ], [ 29, 1, 1, 1 ], [ 30, 1, 1, 1 ], [ 2, 1, 1, 1, 1 ], [ 3, 1, 1, 1, 1 ], [ 10, 2, 1, 1 ], [ 11, 2, 1, 1 ], [ 12, 2, 1, 1 ], [ 13, 2, 1, 1 ], [ 14, 2, 1, 1 ], [ 15, 2, 1, 1 ], [ 16, 2, 1, 1 ], [ 17, 2, 1, 1 ], [ 18, 2, 1, 1 ], [ 10, 3, 1, 1 ], [ 11, 3, 1, 1 ], [ 12, 3, 1, 1 ], [ 13, 3, 1, 1 ], [ 14, 3, 1, 1 ], [ 15, 3, 1, 1 ], [ 16, 3, 1, 1 ], [ 17, 3, 1, 1 ], [ 18, 3, 1, 1 ], [ 4, 4, 1, 1 ], [ 5, 4, 1, 1 ], [ 6, 4, 1, 1 ], [ 7, 4, 1, 1 ], [ 8, 4, 1, 1 ], [ 9, 4, 1, 1 ], [ 5, 5, 1, 1 ], [ 6, 5, 1, 1 ], [ 7, 5, 1, 1 ], [ 8, 5, 1, 1 ], [ 9, 5, 1, 1 ], [ 6, 6, 1, 1 ], [ 7, 6, 1, 1 ], [ 45, 2, 1 ], [ 46, 2, 1 ], [ 47, 2, 1 ], [ 48, 2, 1 ], [ 49, 2, 1 ], [ 50, 2, 1 ], [ 51, 2, 1 ], [ 52, 2, 1 ], [ 53, 2, 1 ], [ 54, 2, 1 ], [ 55, 2, 1 ], [ 4, 2, 2, 1 ], [ 5, 2, 2, 1 ], [ 6, 2, 2, 1 ], [ 7, 2, 2, 1 ], [ 8, 2, 2, 1 ], [ 9, 2, 2, 1 ], [ 4, 3, 2, 1 ], [ 5, 3, 2, 1 ], [ 6, 3, 2, 1 ], [ 7, 3, 2, 1 ], [ 8, 3, 2, 1 ], [ 9, 3, 2, 1 ], [ 45, 3, 1 ], [ 46, 3, 1 ], [ 47, 3, 1 ], [ 48, 3, 1 ], [ 49, 3, 1 ], [ 50, 3, 1 ], [ 51, 3, 1 ], [ 52, 3, 1 ], [ 53, 3, 1 ], [ 54, 3, 1 ], [ 55, 3, 1 ], [ 4, 3, 3, 1 ], [ 5, 3, 3, 1 ], [ 6, 3, 3, 1 ], [ 7, 3, 3, 1 ], [ 8, 3, 3, 1 ], [ 9, 3, 3, 1 ], [ 31, 4, 1 ], [ 32, 4, 1 ], [ 31, 2, 2 ], [ 32, 2, 2 ], [ 33, 2, 2 ], [ 34, 2, 2 ], [ 35, 2, 2 ], [ 36, 2, 2 ], [ 37, 2, 2 ], [ 31, 1, 1, 1 ], [ 32, 1, 1, 1 ], [ 33, 1, 1, 1 ], [ 34, 1, 1, 1 ], [ 35, 1, 1, 1 ], [ 36, 1, 1, 1 ], [ 37, 1, 1, 1 ], [ 38, 1, 1, 1 ], [ 39, 1, 1, 1 ], [ 40, 1, 1, 1 ], [ 41, 1, 1, 1 ], [ 42, 1, 1, 1 ], [ 43, 1, 1, 1 ], [ 44, 1, 1, 1 ], [ 4, 1, 1, 1, 1 ], [ 5, 1, 1, 1, 1 ], [ 6, 1, 1, 1, 1 ], [ 7, 1, 1, 1, 1 ], [ 8, 1, 1, 1, 1 ], [ 9, 1, 1, 1, 1 ], [ 2, 2, 1, 1, 1 ], [ 3, 2, 1, 1, 1 ], [ 3, 3, 1, 1, 1 ], [ 19, 2, 1, 1 ], [ 20, 2, 1, 1 ], [ 21, 2, 1, 1 ], [ 22, 2, 1, 1 ], [ 23, 2, 1, 1 ], [ 24, 2, 1, 1 ], [ 25, 2, 1, 1 ], [ 26, 2, 1, 1 ], [ 27, 2, 1, 1 ], [ 28, 2, 1, 1 ], [ 29, 2, 1, 1 ], [ 30, 2, 1, 1 ], [ 19, 3, 1, 1 ], [ 20, 3, 1, 1 ], [ 21, 3, 1, 1 ], [ 22, 3, 1, 1 ], [ 23, 3, 1, 1 ], [ 24, 3, 1, 1 ], [ 25, 3, 1, 1 ], [ 26, 3, 1, 1 ], [ 27, 3, 1, 1 ], [ 28, 3, 1, 1 ], [ 29, 3, 1, 1 ], [ 30, 3, 1, 1 ], [ 10, 4, 1, 1 ], [ 11, 4, 1, 1 ], [ 12, 4, 1, 1 ], [ 13, 4, 1, 1 ], [ 14, 4, 1, 1 ], [ 15, 4, 1, 1 ], [ 16, 4, 1, 1 ], [ 17, 4, 1, 1 ], [ 18, 4, 1, 1 ], [ 10, 5, 1, 1 ], [ 11, 5, 1, 1 ], [ 12, 5, 1, 1 ], [ 13, 5, 1, 1 ], [ 14, 5, 1, 1 ], [ 10, 2, 2, 1 ], [ 11, 2, 2, 1 ], [ 12, 2, 2, 1 ], [ 13, 2, 2, 1 ], [ 14, 2, 2, 1 ], [ 15, 2, 2, 1 ], [ 16, 2, 2, 1 ], [ 17, 2, 2, 1 ], [ 18, 2, 2, 1 ], [ 10, 3, 2, 1 ], [ 11, 3, 2, 1 ], [ 12, 3, 2, 1 ], [ 13, 3, 2, 1 ], [ 14, 3, 2, 1 ], [ 15, 3, 2, 1 ], [ 16, 3, 2, 1 ], [ 17, 3, 2, 1 ], [ 18, 3, 2, 1 ], [ 4, 4, 2, 1 ], [ 5, 4, 2, 1 ], [ 6, 4, 2, 1 ], [ 7, 4, 2, 1 ], [ 8, 4, 2, 1 ]];

forms := FormsGenerator(L1[35]+10, IntegerRing());
time list_valued_hsop, list_valued_others := EvaluationInvariants(forms);

time list_valued_inv_sec := [[EvaluationSecondaryInvariants(g, j, list_valued_others) : g in inv_sec] : j in [1..#forms]];

L_inv34 := [**];

time L_inv34, M_2 := invariants_secondaires_non_sym(inv_sec, forms, list_valued_hsop, list_valued_others, list_valued_inv_sec, L1, 34, L_inv34);





