K := FiniteField(97);

// Returns a list of [f, sigma(f)] with f a bicubic form with coefficients in K, which vanishes on the invariants of degrees 2,4,4 in the HSOP
function FormsGenerator(n, K)
	R<x, y, u, v> := PolynomialRing(FieldOfFractions(K), 4);
	res := [];

	while #res lt n do
		a21 := Random(K);
		a20 := Random(K);
		a13 := Random(K);
		a12 := Random(K);
		a11 := Random(K);
		a10 := Random(K);
		a03 := Random(K);
		a01 := -(-a20*a13+3*a21*a12+a10);

		while (64*a21*a13-64*a11) eq 0 do
			a11 := Random(K);
		end while;
		
		a00 := -(4*a20^2*a13^2-24*a21*a20*a13*a12+36*a21^2*a12^2-8*a20*a13*a10+24*a21*a12*a10+64*a20*a11*a03-64*a21*a10*a03-72*a20*a13*a01+24*a21*a12*a01+4*a10^2+72*a10*a01+4*a01^2)/(64*a21*a13-64*a11);
		
		while (-24*a21*a20-24*a20*a12+12*a21*a11+8*a00) eq 0 do
			a20 := Random(K);
			a01 := -(-a20*a13+3*a21*a12+a10);
			a00 := -(4*a20^2*a13^2-24*a21*a20*a13*a12+36*a21^2*a12^2-8*a20*a13*a10+24*a21*a12*a10+64*a20*a11*a03-64*a21*a10*a03-72*a20*a13*a01+24*a21*a12*a01+4*a10^2+72*a10*a01+4*a01^2)/(64*a21*a13-64*a11);
		end while;
		
		a02 := -(a20^2*a13^2-6*a21*a20*a13*a12+33*a21^2*a12^2-24*a21^2*a13*a11+16*a21^3*a03+12*a20*a12*a11-24*a21*a11^2-24*a12*a11^2-14*a20*a13*a10+30*a21*a12*a10+48*a12^2*a10-24*a13*a11*a10+8*a20^2*a03+4*a20*a11*a03+8*a21*a10*a03+48*a21^2*a01+2*a20*a13*a01+30*a21*a12*a01+4*a21*a13*a00+a10^2+10*a10*a01+a01^2+8*a20*a00+8*a11*a00)/(-24*a21*a20-24*a20*a12+12*a21*a11+8*a00);
		l := 3*x^3*u^2*v+3*x^2*y*u^3+9*a21*x^2*y*u*v^2+3*a20*x^2*y*v^3+3*a13*x*y^2*u^3+9*a12*x*y^2*u^2*v+9*a11*x*y^2*u*v^2+3*a10*x*y^2*v^3+a03*y^3*u^3+3*a02*y^3*u^2*v+3*a01*y^3*u*v^2+a00*y^3*v^3;
		l1 := Evaluate(l, [u,v,x,y]);
		
		if a01+(-a20*a13+3*a21*a12+a10) ne 0 or a00+(4*a20^2*a13^2-24*a21*a20*a13*a12+36*a21^2*a12^2-8*a20*a13*a10+24*a21*a12*a10+64*a20*a11*a03-64*a21*a10*a03-72*a20*a13*a01+24*a21*a12*a01+4*a10^2+72*a10*a01+4*a01^2)/(64*a21*a13-64*a11) ne 0 or a02+(a20^2*a13^2-6*a21*a20*a13*a12+33*a21^2*a12^2-24*a21^2*a13*a11+16*a21^3*a03+12*a20*a12*a11-24*a21*a11^2-24*a12*a11^2-14*a20*a13*a10+30*a21*a12*a10+48*a12^2*a10-24*a13*a11*a10+8*a20^2*a03+4*a20*a11*a03+8*a21*a10*a03+48*a21^2*a01+2*a20*a13*a01+30*a21*a12*a01+4*a21*a13*a00+a10^2+10*a10*a01+a01^2+8*a20*a00+8*a11*a00)/(-24*a21*a20-24*a20*a12+12*a21*a11+8*a00) ne 0 then
			"Problem, not all three invariants vanish";
		else
			Append(~res, [R!l, R!l1]);
		end if;

	end while;
	return res;
end function;


// To compute the degree m invariants which are products of invariants of smaller degrees
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

// To evaluate a specific secondary invariant on one form and its "mirror" form
function EvaluationSecondaryInvariants(L, j, list_values)
	length := #L;
	if length eq 1 then
		return [list_values[j][L[1]][1], list_values[j][L[1]][2]];
	else
		prod1 := list_values[j][L[1]][1]*list_values[j][L[2]][1];
		prod2 := list_values[j][L[1]][2]*list_values[j][L[2]][2];
		for i in [3..length] do
			prod1 := prod1*list_values[j][L[i]][1];
			prod2 := prod2*list_values[j][L[i]][2];
		end for;
		return [prod1, prod2];
	end if;
end function;

// To evaluate a symmetric and an antisymmetric secondary invariant on one form
function EvaluationSecondaryInvariantsNormalized(L, j, list_values)
	length := #L;
	if length eq 1 then
		return [list_values[j][L[1]][1]+list_values[j][L[1]][2], list_values[j][L[1]][1]-list_values[j][L[1]][2]];
	else
		prod1 := list_values[j][L[1]][1]*list_values[j][L[2]][1];
		prod2 := list_values[j][L[1]][2]*list_values[j][L[2]][2];
		for i in [3..length] do
			prod1 := prod1*list_values[j][L[i]][1];
			prod2 := prod2*list_values[j][L[i]][2];
		end for;
		return [prod1+prod2, prod1-prod2];
	end if;
end function;

// To compute the invariants of a certain degree that come from the HSOP
function InvariantsValuedHSOP(list_valued, forms, d, borne)
	list_deg_hsop := [6,6,8,8,10,12,14];
	anciens := Degree_m(list_deg_hsop, d);
	m := #anciens;
	res_sym := ZeroMatrix(K, borne, m);
	res_non_sym := ZeroMatrix(K, borne, m);
	for i in [1..m] do
		g := anciens[i];
		for j in [1..borne] do
			el := EvaluationSecondaryInvariantsNormalized(g, j, list_valued);
			res_sym[j, i] := el[1];
			res_non_sym[j, i] := el[2];
		end for;
	end for;
	return res_sym, res_non_sym;
end function;

function InvariantsValuedOthers(list_valued_hsop, list_valued_others, inv_sec, forms, d, n, borne)// To evaluate the products of hsop and secondary
	list_deg_hsop := [6,6,8,8,10,12,14];
	list_deg := [6,8,8,10,10,10,10,10,10,12,12,12,12,12,12,12,12,12,14,14,14,14,14,14,14,14,14,14,14,14,16,16,16,16,16,16,16,16,16,16,16,16,16,16,18,18,18,18,18,18,18,18,18,18,18,6,8,10,10,10,12,12,12,12,12,14,14,14,14,14,14,14,14,14,16,16,16,16,16,16,16,16,16,16,16,16,18,18,18,18,18,18,18,18,18,20,22,24];
	anciens_hsop := Degree_m(list_deg_hsop, d);
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
	res_non_sym := ZeroMatrix(K, borne, m_hsop*m_autres);
	for i in [1..m_hsop] do
		g := anciens_hsop[i];
		for j in [1..borne] do
			res_int := EvaluationSecondaryInvariantsNormalized(g, j, list_valued_hsop)[1];
			for k in [1..m_autres] do
				el := EvaluationSecondaryInvariantsNormalized(inv_sec[anciens_autres[k]], j, list_valued_others);
				res_sym[j, m_autres*(i-1)+k] := res_int*el[1];
				res_non_sym[j, m_autres*(i-1)+k] := res_int*el[2];
			end for;
		end for;
	end for;
	return res_sym, res_non_sym;
end function;

function ToSec(l, L)
	res := L[l[1]];
	for i in [2..#l] do
		res cat:= L[l[i]];
	end for;
	return res;
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
	//I10 := Transvectant(c931, f, 3, 3 : invariant := true);
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
    //J84 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(f, f, 1, 1), f, 1, 1), f, 2, 2);, f, 3, 3), Transvectant(Transvectant(f, f, 2, 2), f, 2, 2), 1, 1 : invariant := true);
	inv8 := [K | j81,j82];
	
	// Degree 10
	j101 := Transvectant(c511, c511, 1, 1 : invariant := true);
    j102 := Transvectant(c511, c512, 1, 1 : invariant := true);
    j103 := Transvectant(c511, c513, 1, 1 : invariant := true);
    j104 := Transvectant(c512, c512, 1, 1 : invariant := true);
    j105 := Transvectant(c512, c513, 1, 1 : invariant := true);
    j106 := Transvectant(c513, c513, 1, 1 : invariant := true);
    //J108 := Transvectant(f, c31^3, 3, 3 : invariant := true);
    //J109 := Transvectant(c711, c31, 1, 1 : invariant := true);
    //J1010 := Transvectant(c712, c31, 1, 1 : invariant := true);
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
    //j144 := Transvectant(c712, c712, 1, 1 : invariant := true);
    j146 := Transvectant(f, c511*c511*c31, 3, 3 : invariant := true);
    j147 := Transvectant(f, c511*c512*c31, 3, 3 : invariant := true);
    j148 := Transvectant(f, c511*c513*c31, 3, 3 : invariant := true);
    j149 := Transvectant(f, c512*c512*c31, 3, 3 : invariant := true);
    j1410 := Transvectant(f, c512*c513*c31, 3, 3 : invariant := true);
    j1411 := Transvectant(f, c513*c513*c31, 3, 3 : invariant := true);
    j1412 := Transvectant(f, c711*c31*c31, 3, 3 : invariant := true);
    //j1413 := Transvectant(f, c712*c31*c31, 3, 3 : invariant := true);
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
	//j1616 := Transvectant(f, c712*c512*c31, 3, 3 : invariant := true);
    //j1617 := Transvectant(f, c712*c513*c31, 3, 3 : invariant := true);
	//j1618 := Transvectant(f, c713*c511*c31, 3, 3 : invariant := true);
    //j1619 := Transvectant(f, c713*c512*c31, 3, 3 : invariant := true);
    //j1620 := Transvectant(f, c713*c513*c31, 3, 3 : invariant := true);
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
	//j1810 := Transvectant(f, c712*c511*c511, 3, 3 : invariant := true);
	j1810 := Transvectant(f, c712*c511*c512, 3, 3 : invariant := true);
	//j1812 := Transvectant(f, c712*c511*c513, 3, 3 : invariant := true);
	j1811 := Transvectant(f, c712*c512*c512, 3, 3 : invariant := true);
    //j1814 := Transvectant(f, c712*c512*c513, 3, 3 : invariant := true);
	//j1815 := Transvectant(f, c712*c513*c513, 3, 3 : invariant := true);
	//j1816 := Transvectant(f, c713*c711*c31, 3, 3 : invariant := true);
	//j1817 := Transvectant(f, c713*c712*c31, 3, 3 : invariant := true);
	//j1818 := Transvectant(f, c713*c713*c31, 3, 3 : invariant := true);
	//j1819 := Transvectant(f, c713*c511*c511, 3, 3 : invariant := true);
	//j1820 := Transvectant(f, c713*c511*c512, 3, 3 : invariant := true);
	//j1821 := Transvectant(f, c713*c512*c512, 3, 3 : invariant := true);
	//j1822 := Transvectant(f, c713*c512*c513, 3, 3 : invariant := true);
	//j1823 := Transvectant(f, c713*c513*c513, 3, 3 : invariant := true);
	inv18 := [K | j181,j182,j183,j184,j185,j186,j187,j188,j189,j1810,j1811];

	// Non-symmetric covariants

	J31 := Transvectant(f,f,3,1);
	J13 := Transvectant(f,f,1,3);
	J20 := Transvectant(f,f,2,0); 
	J02 := Transvectant(f,f,0,2);

	CC337 := Transvectant(f^2,f,3,1);
	CC375 := Transvectant(f^2,f,1,2);

	CC3371 := J31*f;
	CC357 := Transvectant(Jac,f,1,0);

	CC359 := J20*f;
	CC339 := Transvectant(f^2,f,3,0);

	CC373 := Transvectant(J02,f,1,1);
	CC355 := Transvectant(J20,f,0,2);

	CC446 := Transvectant(J13,f,3,0)*f;
	CC408 := Transvectant(Transvectant(J31,f,0,1),f,3,0);

	CC553 := Transvectant(C44H,f,1,2);

	I61 := Transvectant(Transvectant(Transvectant(CC337,f,0,2),f,3,3),f,3,3 : invariant :=  true);
	inv61 := [I61];

	I81 := Transvectant(Transvectant(Transvectant(Transvectant(CC375*f,f,2,1),f,3,3),f,3,3),f,3,3 : invariant :=  true);
	inv81 := [I81];

	I101 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(CC3371,f,1,2),f,0,3),f,1,1),f,3,2),f,3,0),f,1,3),f,3,3 : invariant :=  true);
	I102 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(CC357,f,1,3),f,1,2),f,2,0),f,1,3),f,3,3),f,2,0),f,3,3 : invariant :=  true);
	I103 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(CC359,f,2,1),f,0,3),f,0,2),f,2,2),f,3,3),f,3,1),f,3,3 : invariant :=  true);
	inv101 := [I101, I102, I103];

	I121 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(f^2,f,0,3),f,0,3),f,2,0),f,3,2),f,2,1),f,3,1),f,0,1),f,2,1),f,3,3),f,3,3 : invariant :=  true);
	I122 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(CC339,f,1,1),f,1,2),f,3,2),f,2,1),f,1,2),f,0,1),f,3,3),f,1,3),f,3,3 : invariant :=  true);
	I123 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(J02,f,3,0),f,3,0),f,0,1),f,0,2),f,2,0),f,3,3),f,1,1),f,0,3),f,3,3),f,3,3 : invariant :=  true);
	I124 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(f^3,f,0,2),f,0,2),f,1,1),f,3,0),f,2,1),f,3,3),f,3,3),f,3,3),f,3,3 : invariant :=  true);
	I125 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(CC3371,f,2,2),f,2,3),f,1,0),f,2,2),f,1,0),f,2,2),f,0,3),f,2,2),f,3,3 : invariant :=  true);
	inv121 := [I121, I122, I123, I124, I125];

	I141 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(CC446,f,2,2),f,0,1),f,1,2),f,3,2),f,3,0),f,1,3),f,0,1),f,1,1),f,3,3),f,3,3 : invariant :=  true);
	I142 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(CC359,f,1,0),f,0,3),f,1,3)*f,f,1,3),f,3,3),f,3,0),f,1,2),f,3,3),f,3,1),f,3,3 : invariant :=  true);
	I143 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(CC408,f,0,1)*f,f,0,1),f,2,1),f,3,2),f,2,3),f,0,3),f,3,3),f,2,2),f,3,3 : invariant :=  true);
	I144 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(J02,f,2,2),f,3,0),f,1,2),f,0,2),f,2,2),f,2,0),f,2,2),f,1,3),f,3,0),f,1,0),f,1,3),f,3,3 : invariant :=  true);
	I145 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(CC446,f,3,0),f,0,2),f,3,0),f,1,3),f,2,2),f,1,1),f,0,2),f,2,3),f,2,2),f,3,3 : invariant :=  true);
	I146 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(J02*f,f,2,1),f,3,1),f,3,1),f,1,1),f,3,0),f,0,3),f,2,1),f,0,3),f,2,3),f,2,2),f,3,3 : invariant :=  true);
	I147 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(J20,f,1,0)*f,f,2,1),f,3,2),f,1,1)*f,f,2,3),f,2,2),f,1,3),f,1,3),f,3,3),f,3,3 : invariant :=  true);
	I148 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(CC553,f,1,3),f,2,0),f,1,0),f,2,1),f,1,1),f,1,2),f,3,3),f,2,2),f,3,3 : invariant :=  true);
	I149 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C44H,f,3,0),f,1,3)*f,f,0,3),f,0,2),f,1,1),f,3,1),f,3,3),f,3,1),f,3,3 : invariant :=  true);
	inv141 := [I141, I142, I143, I144, I145, I146, I147, I148, I149];

	I161 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(CC553,f,2,2),f,3,0),f,1,3),f,2,1),f,1,0),f,0,2),f,1,1),f,1,1),f,3,3),f,2,2),f,3,3 : invariant :=  true);
	I162 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(CC373,f,3,1),f,1,1),f,3,3),f,2,1),f,1,1),f,2,1),f,1,2),f,1,0),f,0,1),f,3,1),f,0,3),f,3,3),f,3,3 : invariant :=  true);
	I163 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(J20,f,0,1),f,1,0),f,1,1),f,3,2),f,1,2),f,1,0),f,1,2),f,3,1),f,2,2),f,3,1),f,0,3),f,0,3),f,3,3),f,3,3 : invariant :=  true);
	I164 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(CC337,f,1,3),f,1,3),f,0,1),f,1,2),f,3,0),f,3,0),f,2,3),f,1,2),f,0,3)*f,f,3,0),f,3,3),f,3,3 : invariant :=  true);
	I165 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(CC355,f,2,1),f,2,2),f,3,1),f,0,3),f,1,1),f,2,0),f,3,2),f,0,1),f,0,2),f,1,3),f,2,2),f,3,1),f,3,3 : invariant :=  true);
	I166 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(H,f,0,1),f,0,1),f,1,2),f,1,0),f,3,2),f,1,3),f,2,2),f,2,0),f,1,3),f,3,0),f,3,1),f,0,2),f,2,2),f,3,3 : invariant :=  true);
	I167 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Jac,f,0,3),f,1,1),f,3,1),f,2,1),f,1,2)*f,f,1,1),f,2,1),f,2,1),f,2,1),f,1,3),f,2,2),f,3,3),f,3,3 : invariant :=  true);
	I168 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Jac,f,3,1),f,0,2),f,0,2),f,2,1),f,0,1),f,2,1),f,2,3),f,1,1),f,1,3),f,1,1),f,3,2),f,2,1),f,3,1),f,3,3 : invariant :=  true);
	I169 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(H,f,2,1),f,0,1),f,1,2),f,2,1),f,0,1),f,0,1),f,2,0),f,0,1),f,1,0),f,2,2),f,3,3),f,3,3),f,3,3),f,3,3 : invariant :=  true);
	I1610 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(H,f,0,2),f,2,1),f,0,2),f,3,1),f,3,1),f,1,0),f,1,0),f,0,1),f,0,2),f,0,3),f,3,0),f,3,3),f,3,3),f,3,3 : invariant :=  true);
	I1611 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(CC339,f,0,2),f,2,0),f,2,2),f,0,2),f,3,2),f,0,1),f,1,0),f,1,3),f,1,3),f,2,3),f,3,0),f,3,3),f,3,3 : invariant :=  true);
	I1612 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(H,f,1,0),f,3,1)*f,f,0,1),f,3,0),f,1,1),f,0,2),f,2,1),f,0,3),f,1,3),f,2,1),f,3,3),f,3,3),f,3,3 : invariant :=  true);
	inv161 := [I161, I162, I163, I164, I165, I166, I167, I168, I169, I1610, I1611, I1612];
	
	I181 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(CC408*f,f,1,3),f,0,2),f,0,1),f,0,1),f,3,1),f,0,2),f,3,1),f,0,3),f,3,3),f,3,0),f,3,3),f,2,2),f,3,3 : invariant :=  true);
	I182 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(CC375,f,2,3),f,2,0),f,0,3),f,2,2),f,3,0),f,0,1)*f,f,3,2),f,0,3),f,3,2),f,0,1),f,2,1),f,3,1),f,3,3),f,3,3 : invariant :=  true);
	I183 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(J31,f,0,3),f,0,1),f,1,2),f,3,1),f,1,1)*f,f,1,2),f,2,2),f,3,2),f,0,3),f,2,0),f,1,2),f,3,2),f,2,0),f,2,2),f,3,3 : invariant :=  true);
	I184 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(CC355,f,1,2),f,2,3),f,1,1),f,3,1),f,1,2),f,0,1)*f*f,f,0,1),f,2,3),f,3,1),f,3,3),f,3,3),f,3,1),f,3,3 : invariant :=  true);
	I185 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(J31,f,0,1),f,0,2),f,0,3)*f*f,f,0,1),f,3,3),f,1,1),f,1,0),f,3,1),f,3,2),f,2,3),f,3,1),f,3,3),f,2,2),f,3,3 : invariant :=  true);
	I186 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(J31,f,0,2),f,1,1),f,1,2),f,1,2),f,1,0),f,2,3)*f,f,1,0),f,0,3),f,1,1),f,1,1),f,3,1),f,3,1),f,3,3),f,3,3),f,3,3 : invariant :=  true);
	I187 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(CC373*f,f,3,0),f,1,3)*f,f,0,1),f,2,0),f,3,3),f,3,3),f,3,3),f,0,3),f,3,0),f,0,2),f,3,3),f,2,0),f,3,3 : invariant :=  true);
	I188 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(CC357,f,2,0),f,2,0),f,3,2)*f,f,2,0),f,1,1),f,2,0),f,0,2),f,3,3),f,0,3),f,1,3),f,0,3),f,3,3),f,3,3),f,3,3 : invariant :=  true);
	I189 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(J20,f,0,3),f,1,2),f,0,2),f,3,0),f,0,1),f,0,2),f,2,1),f,0,2),f,1,1),f,1,3),f,2,1),f,3,3),f,3,0),f,3,2),f,3,1),f,3,3 : invariant :=  true);
	inv181 := [I181, I182, I183, I184, I185, I186, I187, I188, I189];

	I20 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(J02,f,2,0),f,1,2)*f,f,3,3),f,3,1),f,2,0),f,1,1),f,3,3)*f,f,3,1),f,0,3),f,0,2),f,3,1)*f,f,3,2),f,2,3),f,1,3),f,3,3 : invariant :=  true);
	
	I22 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(J13*f,f,2,1),f,3,0),f,2,1),f,2,0),f,0,2),f,0,3),f,1,3),f,2,3),f,1,0),f,0,3),f,1,1),f,2,1),f,3,0),f,1,1),f,1,0),f,3,3),f,2,2),f,3,3),f,3,3 : invariant :=  true);

	I24 := Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(Transvectant(C35H,f,3,1)*f*f,f,2,1),f,2,0),f,3,1),f,2,2),f,2,2),f,0,2),f,2,2),f,3,0),f,0,3),f,0,2),f,3,0),f,0,3),f,3,0),f,3,3),f,0,3),f,0,3),f,3,3),f,3,3 : invariant :=  true);

	inv201 := [I20, I22, I24];
	
	return invHSOP, inv6 cat inv8 cat inv10 cat inv12 cat inv14 cat inv16 cat inv18 cat inv61 cat inv81 cat inv101 cat inv121 cat inv141 cat inv161 cat inv181 cat inv201;
end function;


function EvaluationInvariants(forms)
	res_hsop := [];
	res_inv := [];
	c := 0;
	for L in forms do
		c +:= 1;
		c/#forms;
		Hsop1, Inv1 := Invariants(L[1]);
		Hsop2, Inv2 := Invariants(L[2]);
		Append(~res_hsop, [[Hsop1[i], Hsop2[i]] : i in [1..#Hsop1]]);
		Append(~res_inv, [[Inv1[i], Inv2[i]] : i in [1..#Inv1]]);
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


function invariants_secondaires_non_sym(inv_sec, forms, list_valued_hsop, list_valued_others, list_valued_inv_sec, L, n)
	m := L[n+1];
	list_deg := [6,8,8,10,10,10,10,10,10,12,12,12,12,12,12,12,12,12,14,14,14,14,14,14,14,14,14,14,14,14,16,16,16,16,16,16,16,16,16,16,16,16,16,16,18,18,18,18,18,18,18,18,18,18,18,6,8,10,10,10,12,12,12,12,12,14,14,14,14,14,14,14,14,14,16,16,16,16,16,16,16,16,16,16,16,16,18,18,18,18,18,18,18,18,18,20,22,24];
	M_sym, M_non_sym := InvariantsValuedHSOP(list_valued_hsop, forms, n, m+10);
	for d in [6..n-6] do
		if d mod 2 eq 0 then
			M0_sym, M0_non_sym := InvariantsValuedOthers(list_valued_hsop, list_valued_others, inv_sec, forms, d, n, m+10);
			M_sym := HorizontalJoin(M_sym, M0_sym);
			M_non_sym := HorizontalJoin(M_non_sym, M0_non_sym);
		end if;
	end for;
	res_sym := [];
	res_non_sym := [];
	M_sym_ortho := Matrix(Basis(Nullspace(M_sym)));
	M_non_sym_ortho := Matrix(Basis(Nullspace(M_non_sym)));
	deg := [];
	for el in inv_sec do
		s := 0;
		for l in el do
			s := s+list_deg[l];
		end for;
		Append(~deg, s);
	end for;
	nouveaux_sec := Degree_m(deg, n);
	for g in nouveaux_sec do
		V_sym := Matrix(K, [[EvaluationSecondaryInvariantsNormalized(g, j, list_valued_inv_sec)[1] : j in [1..m+10]]]);
		V_non_sym := Matrix(K, [[EvaluationSecondaryInvariantsNormalized(g, j, list_valued_inv_sec)[2] : j in [1..m+10]]]);
		p_sym := Vector(M_sym_ortho*Transpose(V_sym));
		p_non_sym := Vector(M_non_sym_ortho*Transpose(V_non_sym));
		if NNZEntries(p_sym) ne 0 then
			M_sym_ortho := UpdateDual(M_sym_ortho, p_sym);
			Append(~res_sym, ToSec(g, inv_sec));
		end if;
		if NNZEntries(p_non_sym) ne 0 then
			M_non_sym_ortho := UpdateDual(M_non_sym_ortho, p_non_sym);
			Append(~res_non_sym, ToSec(g, inv_sec));
		end if;
		if NumberOfRows(M_sym_ortho)+NumberOfRows(M_non_sym_ortho)-20 le L[n+1] then
			break g;
		end if;
	end for;
	return res_sym, res_non_sym, NumberOfRows(M_sym_ortho)+NumberOfRows(M_non_sym_ortho)-20;
end function;


function invariants_secondaires_non_sym(inv_sec, forms, list_valued_hsop, list_valued_others, list_valued_inv_sec, L, n)
	m := L[n+1];
	list_deg := [6,8,8,10,10,10,10,10,10,12,12,12,12,12,12,12,12,12,14,14,14,14,14,14,14,14,14,14,14,14,16,16,16,16,16,16,16,16,16,16,16,16,16,16,18,18,18,18,18,18,18,18,18,18,18,6,8,10,10,10,12,12,12,12,12,14,14,14,14,14,14,14,14,14,16,16,16,16,16,16,16,16,16,16,16,16,18,18,18,18,18,18,18,18,18,20,22,24];
	M_sym, M_non_sym := InvariantsValuedHSOP(list_valued_hsop, forms, n, m+10);
	for d in [6..n-6] do
		if d mod 2 eq 0 then
			M0_sym, M0_non_sym := InvariantsValuedOthers(list_valued_hsop, list_valued_others, inv_sec, forms, d, n, m+10);
			M_sym := HorizontalJoin(M_sym, M0_sym);
			M_non_sym := HorizontalJoin(M_non_sym, M0_non_sym);
		end if;
	end for;
	res_sym := [];
	res_non_sym := [];
	M_sym_ortho := Matrix(Basis(Nullspace(M_sym)));
	M_non_sym_ortho := Matrix(Basis(Nullspace(M_non_sym)));
	deg := [];
	for el in inv_sec do
		s := 0;
		for l in el do
			s := s+list_deg[l];
		end for;
		Append(~deg, s);
	end for;
	nouveaux_sec := Degree_m(deg, n);
	for g in nouveaux_sec do
		V_sym := Matrix(K, [[EvaluationSecondaryInvariantsNormalized(g, j, list_valued_inv_sec)[1] : j in [1..m+10]]]);
		V_non_sym := Matrix(K, [[EvaluationSecondaryInvariantsNormalized(g, j, list_valued_inv_sec)[2] : j in [1..m+10]]]);
		p_sym := Vector(M_sym_ortho*Transpose(V_sym));
		p_non_sym := Vector(M_non_sym_ortho*Transpose(V_non_sym));
		if NNZEntries(p_sym) ne 0 then
			M_sym_ortho := UpdateDual(M_sym_ortho, p_sym);
			Append(~res_sym, ToSec(g, inv_sec));
		end if;
		if NNZEntries(p_non_sym) ne 0 then
			M_non_sym_ortho := UpdateDual(M_non_sym_ortho, p_non_sym);
			Append(~res_non_sym, ToSec(g, inv_sec));
		end if;
		if NumberOfRows(M_sym_ortho)+NumberOfRows(M_non_sym_ortho)-20 le L[n+1] then
			break g;
		end if;
	end for;
	return res_sym, res_non_sym, NumberOfRows(M_sym_ortho)+NumberOfRows(M_non_sym_ortho)-20;
end function;

L1 := [1, 0, 0, 0, 0, 0, 4, 0, 5, 0, 10, 0, 24, 0, 41, 0, 77, 0, 138, 0, 222, 0, 362, 0, 573, 0, 853, 0, 1262, 0, 1836, 0, 2578, 0, 3578, 0, 4902, 0, 6571, 0, 8718, 0, 11439, 0, 14783, 0, 18948, 0, 24072, 0, 30230, 0, 37702, 0, 46691, 0, 57313, 0, 69929];
L2 := [1, 0, 0, 0, 0, 0, 3, 0, 4, 0, 7, 0, 16, 0, 25, 0, 45, 0, 79, 0, 123, 0, 196, 0, 307, 0, 450, 0, 660, 0, 955, 0, 1331, 0, 1838, 0, 2511, 0, 3353, 0, 4437, 0, 5811, 0, 7493, 0, 9589, 0, 12169, 0, 15261, 0, 19014, 0, 23530, 0, 28858, 0, 35187];

inv_sec := [ [ 1 ], [ 56 ], [ 2 ], [ 3 ], [ 57 ], [ 4 ], [ 5 ], [ 6 ], [ 7 ], [ 8 ], [ 9 ], [ 58 ], [ 59 ], [ 60 ], [ 10 ], [ 11 ], [ 12 ], [ 13 ], [ 14 ], [ 15 ], [ 16 ], [ 17 ], [ 18 ], [ 61 ], [ 62 ], [ 63 ], [ 64 ], [ 65 ], [ 1, 1 ], [ 56, 1 ], [ 19 ], [ 20 ], [ 21 ], [ 22 ], [ 23 ], [ 24 ], [ 25 ], [ 26 ], [ 27 ], [ 28 ], [ 29 ], [ 30 ], [ 66 ], [ 67 ], [ 68 ], [ 69 ], [ 70 ], [ 71 ], [ 72 ], [ 73 ], [ 74 ], [ 2, 1 ], [ 3, 1 ], [ 57, 1 ], [ 2, 56 ], [ 3, 56 ], [ 31 ], [ 32 ], [ 33 ], [ 34 ], [ 35 ], [ 36 ], [ 37 ], [ 38 ], [ 39 ], [ 40 ], [ 41 ], [ 42 ], [ 43 ], [ 44 ], [ 75 ], [ 76 ], [ 77 ], [ 78 ], [ 79 ], [ 80 ], [ 81 ], [ 82 ], [ 83 ], [ 84 ], [ 85 ], [ 86 ], [ 4, 1 ], [ 5, 1 ], [ 6, 1 ], [ 7, 1 ], [ 8, 1 ], [ 9, 1 ], [ 58, 1 ], [ 59, 1 ], [ 60, 1 ], [ 4, 56 ], [ 5, 56 ], [ 6, 56 ], [ 7, 56 ], [ 8, 56 ], [ 9, 56 ], [ 58, 56 ], [ 59, 56 ], [ 60, 56 ], [ 57, 2 ], [ 57, 3 ], [ 45 ], [ 46 ], [ 47 ], [ 48 ], [ 49 ], [ 50 ], [ 51 ], [ 52 ], [ 53 ], [ 54 ], [ 55 ], [ 87 ], [ 88 ], [ 89 ], [ 90 ], [ 91 ], [ 92 ], [ 93 ], [ 94 ], [ 95 ], [ 10, 1 ], [ 11, 1 ], [ 12, 1 ], [ 13, 1 ], [ 14, 1 ], [ 15, 1 ], [ 16, 1 ], [ 17, 1 ], [ 18, 1 ], [ 61, 1 ], [ 62, 1 ], [ 63, 1 ], [ 64, 1 ], [ 65, 1 ], [ 1, 1, 1 ], [ 56, 1, 1 ], [ 10, 56 ], [ 11, 56 ], [ 12, 56 ], [ 13, 56 ], [ 14, 56 ], [ 15, 56 ], [ 16, 56 ], [ 17, 56 ], [ 18, 56 ], [ 61, 56 ], [ 62, 56 ], [ 63, 56 ], [ 64, 56 ], [ 65, 56 ], [ 4, 2 ], [ 5, 2 ], [ 6, 2 ], [ 7, 2 ], [ 8, 2 ], [ 9, 2 ], [ 58, 2 ], [ 59, 2 ], [ 60, 2 ], [ 4, 3 ], [ 58, 3 ], [ 59, 3 ], [ 60, 3 ], [ 4, 57 ], [ 5, 57 ], [ 6, 57 ], [ 7, 57 ], [ 8, 57 ], [ 9, 57 ], [ 96 ], [ 19, 1 ], [ 20, 1 ], [ 21, 1 ], [ 22, 1 ], [ 23, 1 ], [ 24, 1 ], [ 25, 1 ], [ 26, 1 ], [ 27, 1 ], [ 28, 1 ], [ 29, 1 ], [ 30, 1 ], [ 66, 1 ], [ 67, 1 ], [ 68, 1 ], [ 69, 1 ], [ 70, 1 ], [ 71, 1 ], [ 72, 1 ], [ 73, 1 ], [ 74, 1 ], [ 2, 1, 1 ], [ 3, 1, 1 ], [ 57, 1, 1 ], [ 2, 56, 1 ], [ 3, 56, 1 ], [ 19, 56 ], [ 20, 56 ], [ 21, 56 ], [ 22, 56 ], [ 23, 56 ], [ 24, 56 ], [ 25, 56 ], [ 26, 56 ], [ 27, 56 ], [ 28, 56 ], [ 29, 56 ], [ 30, 56 ], [ 66, 56 ], [ 67, 56 ], [ 68, 56 ], [ 69, 56 ], [ 70, 56 ], [ 71, 56 ], [ 72, 56 ], [ 73, 56 ], [ 74, 56 ], [ 2, 56, 56 ], [ 3, 56, 56 ], [ 10, 2 ], [ 11, 2 ], [ 12, 2 ], [ 13, 2 ], [ 14, 2 ], [ 15, 2 ], [ 16, 2 ], [ 17, 2 ], [ 61, 2 ], [ 62, 2 ], [ 63, 2 ], [ 64, 2 ], [ 65, 2 ], [ 10, 3 ], [ 11, 3 ], [ 12, 3 ], [ 13, 3 ], [ 14, 3 ], [ 15, 3 ], [ 16, 3 ], [ 17, 3 ], [ 61, 3 ], [ 62, 3 ], [ 63, 3 ], [ 64, 3 ], [ 65, 3 ], [ 10, 57 ], [ 11, 57 ], [ 12, 57 ], [ 13, 57 ], [ 14, 57 ], [ 15, 57 ], [ 16, 57 ], [ 17, 57 ], [ 61, 57 ], [ 62, 57 ], [ 63, 57 ], [ 64, 57 ], [ 58, 4 ], [ 59, 4 ], [ 60, 4 ], [ 58, 5 ], [ 59, 5 ], [ 60, 5 ], [ 58, 6 ], [ 59, 6 ], [ 97 ], [ 31, 1 ], [ 32, 1 ], [ 33, 1 ], [ 34, 1 ], [ 35, 1 ], [ 36, 1 ], [ 37, 1 ], [ 38, 1 ], [ 39, 1 ], [ 40, 1 ], [ 41, 1 ], [ 42, 1 ], [ 43, 1 ], [ 44, 1 ], [ 75, 1 ], [ 76, 1 ], [ 77, 1 ], [ 78, 1 ], [ 79, 1 ], [ 80, 1 ], [ 81, 1 ], [ 82, 1 ], [ 83, 1 ], [ 84, 1 ], [ 85, 1 ], [ 86, 1 ], [ 4, 1, 1 ], [ 5, 1, 1 ], [ 6, 1, 1 ], [ 7, 1, 1 ], [ 8, 1, 1 ], [ 9, 1, 1 ], [ 58, 1, 1 ], [ 59, 1, 1 ], [ 60, 1, 1 ], [ 4, 56, 1 ], [ 5, 56, 1 ], [ 6, 56, 1 ], [ 7, 56, 1 ], [ 8, 56, 1 ], [ 9, 56, 1 ], [ 58, 56, 1 ], [ 59, 56, 1 ], [ 60, 56, 1 ], [ 57, 2, 1 ], [ 57, 3, 1 ], [ 31, 56 ], [ 32, 56 ], [ 33, 56 ], [ 34, 56 ], [ 35, 56 ], [ 36, 56 ], [ 37, 56 ], [ 38, 56 ], [ 39, 56 ], [ 40, 56 ], [ 41, 56 ], [ 42, 56 ], [ 43, 56 ], [ 44, 56 ], [ 75, 56 ], [ 76, 56 ], [ 77, 56 ], [ 78, 56 ], [ 79, 56 ], [ 80, 56 ], [ 81, 56 ], [ 82, 56 ], [ 83, 56 ], [ 84, 56 ], [ 85, 56 ], [ 86, 56 ], [ 4, 56, 56 ], [ 5, 56, 56 ], [ 6, 56, 56 ], [ 7, 56, 56 ], [ 8, 56, 56 ], [ 9, 56, 56 ], [ 58, 56, 56 ], [ 59, 56, 56 ], [ 60, 56, 56 ], [ 57, 2, 56 ], [ 57, 3, 56 ], [ 19, 2 ], [ 20, 2 ], [ 21, 2 ], [ 22, 2 ], [ 23, 2 ], [ 24, 2 ], [ 25, 2 ], [ 26, 2 ], [ 27, 2 ], [ 28, 2 ], [ 29, 2 ], [ 66, 2 ], [ 67, 2 ], [ 68, 2 ], [ 69, 2 ], [ 70, 2 ], [ 71, 2 ], [ 72, 2 ], [ 73, 2 ], [ 74, 2 ], [ 19, 3 ], [ 20, 3 ], [ 21, 3 ], [ 22, 3 ], [ 23, 3 ], [ 24, 3 ], [ 25, 3 ], [ 66, 3 ], [ 67, 3 ], [ 68, 3 ], [ 69, 3 ], [ 70, 3 ], [ 71, 3 ], [ 72, 3 ], [ 73, 3 ], [ 74, 3 ], [ 19, 57 ], [ 20, 57 ], [ 21, 57 ], [ 22, 57 ], [ 23, 57 ], [ 24, 57 ], [ 25, 57 ], [ 26, 57 ], [ 27, 57 ], [ 98 ], [ 45, 1 ], [ 46, 1 ], [ 47, 1 ], [ 48, 1 ], [ 49, 1 ], [ 50, 1 ], [ 51, 1 ], [ 52, 1 ], [ 53, 1 ], [ 54, 1 ], [ 55, 1 ], [ 87, 1 ], [ 88, 1 ], [ 89, 1 ], [ 90, 1 ], [ 91, 1 ], [ 92, 1 ], [ 93, 1 ], [ 94, 1 ], [ 95, 1 ], [ 10, 1, 1 ], [ 11, 1, 1 ], [ 12, 1, 1 ], [ 13, 1, 1 ], [ 14, 1, 1 ], [ 15, 1, 1 ], [ 16, 1, 1 ], [ 17, 1, 1 ], [ 18, 1, 1 ], [ 61, 1, 1 ], [ 62, 1, 1 ], [ 63, 1, 1 ], [ 64, 1, 1 ], [ 65, 1, 1 ], [ 1, 1, 1, 1 ], [ 56, 1, 1, 1 ], [ 10, 56, 1 ], [ 11, 56, 1 ], [ 12, 56, 1 ], [ 13, 56, 1 ], [ 14, 56, 1 ], [ 15, 56, 1 ], [ 16, 56, 1 ], [ 17, 56, 1 ], [ 18, 56, 1 ], [ 61, 56, 1 ], [ 62, 56, 1 ], [ 63, 56, 1 ], [ 64, 56, 1 ], [ 65, 56, 1 ], [ 4, 2, 1 ], [ 5, 2, 1 ], [ 6, 2, 1 ], [ 7, 2, 1 ], [ 8, 2, 1 ], [ 9, 2, 1 ], [ 58, 2, 1 ], [ 59, 2, 1 ], [ 60, 2, 1 ], [ 4, 3, 1 ], [ 58, 3, 1 ], [ 59, 3, 1 ], [ 60, 3, 1 ], [ 4, 57, 1 ], [ 5, 57, 1 ], [ 6, 57, 1 ], [ 7, 57, 1 ], [ 8, 57, 1 ], [ 9, 57, 1 ], [ 45, 56 ], [ 46, 56 ], [ 47, 56 ], [ 48, 56 ], [ 49, 56 ], [ 50, 56 ], [ 51, 56 ], [ 52, 56 ], [ 53, 56 ], [ 54, 56 ], [ 55, 56 ], [ 87, 56 ], [ 88, 56 ], [ 89, 56 ], [ 90, 56 ], [ 91, 56 ], [ 92, 56 ], [ 93, 56 ], [ 94, 56 ], [ 95, 56 ], [ 10, 56, 56 ], [ 11, 56, 56 ], [ 12, 56, 56 ], [ 13, 56, 56 ], [ 14, 56, 56 ], [ 15, 56, 56 ], [ 16, 56, 56 ], [ 17, 56, 56 ], [ 18, 56, 56 ], [ 61, 56, 56 ], [ 62, 56, 56 ], [ 63, 56, 56 ], [ 64, 56, 56 ], [ 65, 56, 56 ], [ 4, 2, 56 ], [ 5, 2, 56 ], [ 6, 2, 56 ], [ 7, 2, 56 ], [ 8, 2, 56 ], [ 9, 2, 56 ], [ 58, 2, 56 ], [ 59, 2, 56 ], [ 60, 2, 56 ], [ 4, 3, 56 ], [ 58, 3, 56 ], [ 59, 3, 56 ], [ 60, 3, 56 ], [ 4, 57, 56 ], [ 5, 57, 56 ], [ 6, 57, 56 ], [ 7, 57, 56 ], [ 8, 57, 56 ], [ 9, 57, 56 ], [ 31, 2 ], [ 32, 2 ], [ 33, 2 ], [ 34, 2 ], [ 35, 2 ], [ 36, 2 ], [ 37, 2 ], [ 38, 2 ], [ 39, 2 ], [ 40, 2 ], [ 41, 2 ], [ 42, 2 ], [ 75, 2 ], [ 76, 2 ], [ 77, 2 ], [ 78, 2 ], [ 79, 2 ], [ 80, 2 ], [ 81, 2 ], [ 82, 2 ], [ 83, 2 ], [ 84, 2 ], [ 85, 2 ], [ 86, 2 ], [ 57, 2, 2 ], [ 57, 3, 2 ], [ 75, 3 ], [ 76, 3 ], [ 77, 3 ], [ 78, 3 ], [ 79, 3 ], [ 80, 3 ], [ 81, 3 ], [ 82, 3 ], [ 83, 3 ], [ 84, 3 ], [ 96, 1 ], [ 19, 1, 1 ], [ 20, 1, 1 ], [ 21, 1, 1 ], [ 22, 1, 1 ], [ 23, 1, 1 ], [ 24, 1, 1 ], [ 25, 1, 1 ], [ 26, 1, 1 ], [ 27, 1, 1 ], [ 28, 1, 1 ], [ 29, 1, 1 ], [ 30, 1, 1 ], [ 66, 1, 1 ], [ 67, 1, 1 ], [ 68, 1, 1 ], [ 69, 1, 1 ], [ 70, 1, 1 ], [ 71, 1, 1 ], [ 72, 1, 1 ], [ 73, 1, 1 ], [ 74, 1, 1 ], [ 2, 1, 1, 1 ], [ 3, 1, 1, 1 ], [ 57, 1, 1, 1 ], [ 2, 56, 1, 1 ], [ 3, 56, 1, 1 ], [ 19, 56, 1 ], [ 20, 56, 1 ], [ 21, 56, 1 ], [ 22, 56, 1 ], [ 23, 56, 1 ], [ 24, 56, 1 ], [ 25, 56, 1 ], [ 26, 56, 1 ], [ 27, 56, 1 ], [ 28, 56, 1 ], [ 29, 56, 1 ], [ 30, 56, 1 ], [ 66, 56, 1 ], [ 67, 56, 1 ], [ 68, 56, 1 ], [ 69, 56, 1 ], [ 70, 56, 1 ], [ 71, 56, 1 ], [ 72, 56, 1 ], [ 73, 56, 1 ], [ 74, 56, 1 ], [ 2, 56, 56, 1 ], [ 3, 56, 56, 1 ], [ 10, 2, 1 ], [ 11, 2, 1 ], [ 12, 2, 1 ], [ 13, 2, 1 ], [ 14, 2, 1 ], [ 15, 2, 1 ], [ 16, 2, 1 ], [ 17, 2, 1 ], [ 61, 2, 1 ], [ 62, 2, 1 ], [ 63, 2, 1 ], [ 64, 2, 1 ], [ 65, 2, 1 ], [ 10, 3, 1 ], [ 11, 3, 1 ], [ 12, 3, 1 ], [ 13, 3, 1 ], [ 14, 3, 1 ], [ 15, 3, 1 ], [ 16, 3, 1 ], [ 17, 3, 1 ], [ 61, 3, 1 ], [ 62, 3, 1 ], [ 63, 3, 1 ], [ 64, 3, 1 ], [ 65, 3, 1 ], [ 10, 57, 1 ], [ 11, 57, 1 ], [ 12, 57, 1 ], [ 13, 57, 1 ], [ 14, 57, 1 ], [ 15, 57, 1 ], [ 16, 57, 1 ], [ 17, 57, 1 ], [ 61, 57, 1 ], [ 62, 57, 1 ], [ 63, 57, 1 ], [ 64, 57, 1 ], [ 58, 4, 1 ], [ 59, 4, 1 ], [ 60, 4, 1 ], [ 58, 5, 1 ], [ 59, 5, 1 ], [ 60, 5, 1 ], [ 58, 6, 1 ], [ 59, 6, 1 ], [ 96, 56 ], [ 19, 56, 56 ], [ 20, 56, 56 ], [ 21, 56, 56 ], [ 22, 56, 56 ], [ 23, 56, 56 ], [ 24, 56, 56 ], [ 25, 56, 56 ], [ 26, 56, 56 ], [ 27, 56, 56 ], [ 28, 56, 56 ], [ 29, 56, 56 ], [ 30, 56, 56 ], [ 66, 56, 56 ], [ 67, 56, 56 ], [ 68, 56, 56 ], [ 69, 56, 56 ], [ 70, 56, 56 ], [ 71, 56, 56 ], [ 72, 56, 56 ], [ 73, 56, 56 ], [ 74, 56, 56 ], [ 2, 56, 56, 56 ], [ 3, 56, 56, 56 ], [ 10, 2, 56 ], [ 11, 2, 56 ], [ 12, 2, 56 ], [ 13, 2, 56 ], [ 14, 2, 56 ], [ 15, 2, 56 ], [ 16, 2, 56 ], [ 17, 2, 56 ], [ 61, 2, 56 ], [ 62, 2, 56 ], [ 63, 2, 56 ], [ 64, 2, 56 ], [ 65, 2, 56 ], [ 10, 3, 56 ], [ 11, 3, 56 ], [ 12, 3, 56 ], [ 13, 3, 56 ], [ 14, 3, 56 ], [ 15, 3, 56 ], [ 16, 3, 56 ], [ 17, 3, 56 ], [ 61, 3, 56 ], [ 62, 3, 56 ], [ 63, 3, 56 ], [ 64, 3, 56 ], [ 65, 3, 56 ], [ 10, 57, 56 ], [ 11, 57, 56 ], [ 12, 57, 56 ], [ 13, 57, 56 ], [ 14, 57, 56 ], [ 15, 57, 56 ], [ 16, 57, 56 ], [ 17, 57, 56 ], [ 61, 57, 56 ], [ 62, 57, 56 ], [ 63, 57, 56 ], [ 64, 57, 56 ], [ 58, 4, 56 ], [ 59, 4, 56 ], [ 60, 4, 56 ], [ 58, 5, 56 ], [ 59, 5, 56 ], [ 60, 5, 56 ], [ 58, 6, 56 ], [ 59, 6, 56 ], [ 45, 2 ], [ 46, 2 ], [ 47, 2 ], [ 87, 2 ], [ 88, 2 ], [ 89, 2 ], [ 90, 2 ], [ 91, 2 ], [ 92, 2 ], [ 93, 2 ], [ 94, 2 ], [ 95, 2 ], [ 58, 2, 2 ], [ 59, 2, 2 ], [ 60, 2, 2 ], [ 97, 1 ], [ 31, 1, 1 ], [ 32, 1, 1 ], [ 33, 1, 1 ], [ 34, 1, 1 ], [ 35, 1, 1 ], [ 36, 1, 1 ], [ 37, 1, 1 ], [ 38, 1, 1 ], [ 39, 1, 1 ], [ 40, 1, 1 ], [ 41, 1, 1 ], [ 42, 1, 1 ], [ 43, 1, 1 ], [ 44, 1, 1 ], [ 75, 1, 1 ], [ 76, 1, 1 ], [ 77, 1, 1 ], [ 78, 1, 1 ], [ 79, 1, 1 ], [ 80, 1, 1 ], [ 81, 1, 1 ], [ 82, 1, 1 ], [ 83, 1, 1 ], [ 84, 1, 1 ], [ 85, 1, 1 ], [ 86, 1, 1 ], [ 4, 1, 1, 1 ], [ 5, 1, 1, 1 ], [ 6, 1, 1, 1 ], [ 7, 1, 1, 1 ], [ 8, 1, 1, 1 ], [ 9, 1, 1, 1 ], [ 58, 1, 1, 1 ], [ 59, 1, 1, 1 ], [ 60, 1, 1, 1 ], [ 4, 56, 1, 1 ], [ 5, 56, 1, 1 ], [ 6, 56, 1, 1 ], [ 7, 56, 1, 1 ], [ 8, 56, 1, 1 ], [ 9, 56, 1, 1 ], [ 58, 56, 1, 1 ], [ 59, 56, 1, 1 ], [ 60, 56, 1, 1 ], [ 57, 2, 1, 1 ], [ 57, 3, 1, 1 ], [ 31, 56, 1 ], [ 32, 56, 1 ], [ 33, 56, 1 ], [ 34, 56, 1 ], [ 35, 56, 1 ], [ 36, 56, 1 ], [ 37, 56, 1 ], [ 38, 56, 1 ], [ 39, 56, 1 ], [ 40, 56, 1 ], [ 41, 56, 1 ], [ 42, 56, 1 ], [ 43, 56, 1 ], [ 44, 56, 1 ], [ 75, 56, 1 ], [ 76, 56, 1 ], [ 77, 56, 1 ], [ 78, 56, 1 ], [ 79, 56, 1 ], [ 80, 56, 1 ], [ 81, 56, 1 ], [ 82, 56, 1 ], [ 83, 56, 1 ], [ 84, 56, 1 ], [ 85, 56, 1 ], [ 86, 56, 1 ], [ 4, 56, 56, 1 ], [ 5, 56, 56, 1 ], [ 6, 56, 56, 1 ], [ 7, 56, 56, 1 ], [ 8, 56, 56, 1 ], [ 9, 56, 56, 1 ], [ 58, 56, 56, 1 ], [ 59, 56, 56, 1 ], [ 60, 56, 56, 1 ], [ 57, 2, 56, 1 ], [ 57, 3, 56, 1 ], [ 19, 2, 1 ], [ 20, 2, 1 ], [ 21, 2, 1 ], [ 22, 2, 1 ], [ 23, 2, 1 ], [ 24, 2, 1 ], [ 25, 2, 1 ], [ 26, 2, 1 ], [ 27, 2, 1 ], [ 28, 2, 1 ], [ 29, 2, 1 ], [ 66, 2, 1 ], [ 67, 2, 1 ], [ 68, 2, 1 ], [ 69, 2, 1 ], [ 70, 2, 1 ], [ 71, 2, 1 ], [ 72, 2, 1 ], [ 73, 2, 1 ], [ 74, 2, 1 ], [ 19, 3, 1 ], [ 20, 3, 1 ], [ 21, 3, 1 ], [ 22, 3, 1 ], [ 23, 3, 1 ], [ 24, 3, 1 ], [ 25, 3, 1 ], [ 66, 3, 1 ], [ 67, 3, 1 ], [ 68, 3, 1 ], [ 69, 3, 1 ], [ 70, 3, 1 ], [ 71, 3, 1 ], [ 72, 3, 1 ], [ 73, 3, 1 ], [ 74, 3, 1 ], [ 19, 57, 1 ], [ 20, 57, 1 ], [ 21, 57, 1 ], [ 22, 57, 1 ], [ 23, 57, 1 ], [ 24, 57, 1 ], [ 25, 57, 1 ], [ 26, 57, 1 ], [ 27, 57, 1 ], [ 97, 56 ], [ 31, 56, 56 ], [ 32, 56, 56 ], [ 33, 56, 56 ], [ 34, 56, 56 ], [ 35, 56, 56 ], [ 36, 56, 56 ], [ 37, 56, 56 ], [ 38, 56, 56 ], [ 39, 56, 56 ], [ 40, 56, 56 ], [ 41, 56, 56 ], [ 42, 56, 56 ], [ 43, 56, 56 ], [ 44, 56, 56 ], [ 75, 56, 56 ], [ 76, 56, 56 ], [ 77, 56, 56 ], [ 78, 56, 56 ], [ 79, 56, 56 ], [ 80, 56, 56 ], [ 81, 56, 56 ], [ 82, 56, 56 ], [ 83, 56, 56 ], [ 84, 56, 56 ], [ 85, 56, 56 ], [ 86, 56, 56 ], [ 4, 56, 56, 56 ], [ 5, 56, 56, 56 ], [ 6, 56, 56, 56 ], [ 7, 56, 56, 56 ], [ 8, 56, 56, 56 ], [ 9, 56, 56, 56 ], [ 58, 56, 56, 56 ], [ 59, 56, 56, 56 ], [ 60, 56, 56, 56 ], [ 57, 2, 56, 56 ], [ 57, 3, 56, 56 ], [ 19, 2, 56 ], [ 20, 2, 56 ], [ 21, 2, 56 ], [ 22, 2, 56 ], [ 23, 2, 56 ], [ 24, 2, 56 ], [ 25, 2, 56 ], [ 26, 2, 56 ], [ 27, 2, 56 ], [ 28, 2, 56 ], [ 29, 2, 56 ], [ 66, 2, 56 ], [ 67, 2, 56 ], [ 68, 2, 56 ], [ 69, 2, 56 ], [ 70, 2, 56 ], [ 71, 2, 56 ], [ 72, 2, 56 ], [ 73, 2, 56 ], [ 74, 2, 56 ], [ 66, 3, 56 ], [ 67, 3, 56 ], [ 68, 3, 56 ], [ 69, 3, 56 ], [ 70, 3, 56 ], [ 71, 3, 56 ], [ 72, 3, 56 ], [ 73, 3, 56 ], [ 98, 1 ], [ 45, 1, 1 ], [ 46, 1, 1 ], [ 47, 1, 1 ], [ 48, 1, 1 ], [ 49, 1, 1 ], [ 50, 1, 1 ], [ 51, 1, 1 ], [ 52, 1, 1 ], [ 53, 1, 1 ], [ 54, 1, 1 ], [ 55, 1, 1 ], [ 87, 1, 1 ], [ 88, 1, 1 ], [ 89, 1, 1 ], [ 90, 1, 1 ], [ 91, 1, 1 ], [ 92, 1, 1 ], [ 93, 1, 1 ], [ 94, 1, 1 ], [ 95, 1, 1 ], [ 10, 1, 1, 1 ], [ 11, 1, 1, 1 ], [ 12, 1, 1, 1 ], [ 13, 1, 1, 1 ], [ 14, 1, 1, 1 ], [ 15, 1, 1, 1 ], [ 16, 1, 1, 1 ], [ 17, 1, 1, 1 ], [ 18, 1, 1, 1 ], [ 61, 1, 1, 1 ], [ 62, 1, 1, 1 ], [ 63, 1, 1, 1 ], [ 64, 1, 1, 1 ], [ 65, 1, 1, 1 ], [ 1, 1, 1, 1, 1 ], [ 56, 1, 1, 1, 1 ], [ 10, 56, 1, 1 ], [ 11, 56, 1, 1 ], [ 12, 56, 1, 1 ], [ 13, 56, 1, 1 ], [ 14, 56, 1, 1 ], [ 15, 56, 1, 1 ], [ 16, 56, 1, 1 ], [ 17, 56, 1, 1 ], [ 18, 56, 1, 1 ], [ 61, 56, 1, 1 ], [ 62, 56, 1, 1 ], [ 63, 56, 1, 1 ], [ 64, 56, 1, 1 ], [ 65, 56, 1, 1 ], [ 4, 2, 1, 1 ], [ 5, 2, 1, 1 ], [ 6, 2, 1, 1 ], [ 7, 2, 1, 1 ], [ 8, 2, 1, 1 ], [ 9, 2, 1, 1 ], [ 58, 2, 1, 1 ], [ 59, 2, 1, 1 ], [ 60, 2, 1, 1 ], [ 4, 3, 1, 1 ], [ 58, 3, 1, 1 ], [ 59, 3, 1, 1 ], [ 60, 3, 1, 1 ], [ 4, 57, 1, 1 ], [ 5, 57, 1, 1 ], [ 6, 57, 1, 1 ], [ 7, 57, 1, 1 ], [ 8, 57, 1, 1 ], [ 9, 57, 1, 1 ], [ 45, 56, 1 ], [ 46, 56, 1 ], [ 47, 56, 1 ], [ 48, 56, 1 ], [ 49, 56, 1 ], [ 50, 56, 1 ], [ 51, 56, 1 ], [ 52, 56, 1 ], [ 53, 56, 1 ], [ 54, 56, 1 ], [ 55, 56, 1 ], [ 87, 56, 1 ], [ 88, 56, 1 ], [ 89, 56, 1 ], [ 90, 56, 1 ], [ 91, 56, 1 ], [ 92, 56, 1 ], [ 93, 56, 1 ], [ 94, 56, 1 ], [ 95, 56, 1 ], [ 10, 56, 56, 1 ], [ 11, 56, 56, 1 ], [ 12, 56, 56, 1 ], [ 13, 56, 56, 1 ], [ 14, 56, 56, 1 ], [ 15, 56, 56, 1 ], [ 16, 56, 56, 1 ], [ 17, 56, 56, 1 ], [ 18, 56, 56, 1 ], [ 61, 56, 56, 1 ], [ 62, 56, 56, 1 ], [ 63, 56, 56, 1 ], [ 64, 56, 56, 1 ], [ 65, 56, 56, 1 ], [ 4, 2, 56, 1 ], [ 5, 2, 56, 1 ], [ 6, 2, 56, 1 ], [ 7, 2, 56, 1 ], [ 8, 2, 56, 1 ], [ 9, 2, 56, 1 ], [ 58, 2, 56, 1 ], [ 59, 2, 56, 1 ], [ 60, 2, 56, 1 ], [ 4, 3, 56, 1 ], [ 58, 3, 56, 1 ], [ 59, 3, 56, 1 ], [ 60, 3, 56, 1 ], [ 4, 57, 56, 1 ], [ 5, 57, 56, 1 ], [ 6, 57, 56, 1 ], [ 7, 57, 56, 1 ], [ 8, 57, 56, 1 ], [ 9, 57, 56, 1 ], [ 31, 2, 1 ], [ 32, 2, 1 ], [ 33, 2, 1 ], [ 34, 2, 1 ], [ 35, 2, 1 ], [ 36, 2, 1 ], [ 37, 2, 1 ], [ 38, 2, 1 ], [ 39, 2, 1 ], [ 40, 2, 1 ], [ 41, 2, 1 ], [ 42, 2, 1 ], [ 75, 2, 1 ], [ 76, 2, 1 ], [ 77, 2, 1 ], [ 78, 2, 1 ], [ 79, 2, 1 ], [ 80, 2, 1 ], [ 81, 2, 1 ], [ 82, 2, 1 ], [ 83, 2, 1 ], [ 84, 2, 1 ], [ 85, 2, 1 ], [ 86, 2, 1 ], [ 57, 2, 2, 1 ], [ 57, 3, 2, 1 ], [ 75, 3, 1 ], [ 76, 3, 1 ], [ 77, 3, 1 ], [ 78, 3, 1 ], [ 79, 3, 1 ], [ 80, 3, 1 ], [ 81, 3, 1 ], [ 82, 3, 1 ], [ 83, 3, 1 ], [ 84, 3, 1 ], [ 98, 56 ], [ 45, 56, 56 ], [ 46, 56, 56 ], [ 47, 56, 56 ], [ 48, 56, 56 ], [ 49, 56, 56 ], [ 50, 56, 56 ], [ 51, 56, 56 ], [ 52, 56, 56 ], [ 53, 56, 56 ], [ 54, 56, 56 ], [ 55, 56, 56 ], [ 87, 56, 56 ], [ 88, 56, 56 ], [ 89, 56, 56 ], [ 90, 56, 56 ], [ 91, 56, 56 ], [ 92, 56, 56 ], [ 93, 56, 56 ], [ 94, 56, 56 ], [ 95, 56, 56 ], [ 10, 56, 56, 56 ], [ 11, 56, 56, 56 ], [ 12, 56, 56, 56 ], [ 13, 56, 56, 56 ], [ 14, 56, 56, 56 ], [ 15, 56, 56, 56 ], [ 16, 56, 56, 56 ], [ 17, 56, 56, 56 ], [ 18, 56, 56, 56 ], [ 61, 56, 56, 56 ], [ 62, 56, 56, 56 ], [ 63, 56, 56, 56 ], [ 64, 56, 56, 56 ], [ 65, 56, 56, 56 ], [ 4, 2, 56, 56 ], [ 96, 1, 1 ], [ 19, 1, 1, 1 ], [ 20, 1, 1, 1 ], [ 21, 1, 1, 1 ], [ 22, 1, 1, 1 ], [ 23, 1, 1, 1 ], [ 24, 1, 1, 1 ], [ 25, 1, 1, 1 ], [ 26, 1, 1, 1 ], [ 27, 1, 1, 1 ], [ 28, 1, 1, 1 ], [ 29, 1, 1, 1 ], [ 30, 1, 1, 1 ], [ 66, 1, 1, 1 ], [ 67, 1, 1, 1 ], [ 68, 1, 1, 1 ], [ 69, 1, 1, 1 ], [ 70, 1, 1, 1 ], [ 71, 1, 1, 1 ], [ 72, 1, 1, 1 ], [ 73, 1, 1, 1 ], [ 74, 1, 1, 1 ], [ 2, 1, 1, 1, 1 ], [ 3, 1, 1, 1, 1 ], [ 57, 1, 1, 1, 1 ], [ 2, 56, 1, 1, 1 ], [ 3, 56, 1, 1, 1 ], [ 19, 56, 1, 1 ], [ 20, 56, 1, 1 ], [ 21, 56, 1, 1 ], [ 22, 56, 1, 1 ], [ 23, 56, 1, 1 ], [ 24, 56, 1, 1 ], [ 25, 56, 1, 1 ], [ 26, 56, 1, 1 ], [ 27, 56, 1, 1 ], [ 28, 56, 1, 1 ], [ 29, 56, 1, 1 ], [ 30, 56, 1, 1 ], [ 66, 56, 1, 1 ], [ 67, 56, 1, 1 ], [ 68, 56, 1, 1 ], [ 69, 56, 1, 1 ], [ 70, 56, 1, 1 ], [ 71, 56, 1, 1 ], [ 72, 56, 1, 1 ], [ 73, 56, 1, 1 ], [ 74, 56, 1, 1 ], [ 2, 56, 56, 1, 1 ], [ 3, 56, 56, 1, 1 ], [ 10, 2, 1, 1 ], [ 11, 2, 1, 1 ], [ 12, 2, 1, 1 ], [ 13, 2, 1, 1 ], [ 14, 2, 1, 1 ], [ 15, 2, 1, 1 ], [ 16, 2, 1, 1 ], [ 17, 2, 1, 1 ], [ 61, 2, 1, 1 ], [ 62, 2, 1, 1 ], [ 63, 2, 1, 1 ], [ 64, 2, 1, 1 ], [ 65, 2, 1, 1 ], [ 10, 3, 1, 1 ], [ 11, 3, 1, 1 ], [ 12, 3, 1, 1 ], [ 13, 3, 1, 1 ], [ 14, 3, 1, 1 ], [ 15, 3, 1, 1 ], [ 16, 3, 1, 1 ], [ 17, 3, 1, 1 ], [ 61, 3, 1, 1 ], [ 62, 3, 1, 1 ], [ 63, 3, 1, 1 ], [ 64, 3, 1, 1 ], [ 65, 3, 1, 1 ], [ 10, 57, 1, 1 ], [ 11, 57, 1, 1 ], [ 12, 57, 1, 1 ], [ 13, 57, 1, 1 ], [ 14, 57, 1, 1 ], [ 15, 57, 1, 1 ], [ 16, 57, 1, 1 ], [ 17, 57, 1, 1 ], [ 61, 57, 1, 1 ], [ 62, 57, 1, 1 ], [ 63, 57, 1, 1 ], [ 64, 57, 1, 1 ], [ 58, 4, 1, 1 ], [ 59, 4, 1, 1 ], [ 60, 4, 1, 1 ], [ 58, 5, 1, 1 ], [ 59, 5, 1, 1 ], [ 60, 5, 1, 1 ], [ 58, 6, 1, 1 ], [ 59, 6, 1, 1 ], [ 96, 56, 1 ], [ 19, 56, 56, 1 ], [ 20, 56, 56, 1 ], [ 21, 56, 56, 1 ], [ 22, 56, 56, 1 ], [ 23, 56, 56, 1 ], [ 24, 56, 56, 1 ], [ 25, 56, 56, 1 ], [ 26, 56, 56, 1 ], [ 27, 56, 56, 1 ], [ 28, 56, 56, 1 ], [ 29, 56, 56, 1 ], [ 30, 56, 56, 1 ], [ 66, 56, 56, 1 ], [ 67, 56, 56, 1 ], [ 68, 56, 56, 1 ], [ 69, 56, 56, 1 ], [ 70, 56, 56, 1 ], [ 71, 56, 56, 1 ], [ 72, 56, 56, 1 ], [ 73, 56, 56, 1 ], [ 74, 56, 56, 1 ], [ 2, 56, 56, 56, 1 ], [ 3, 56, 56, 56, 1 ], [ 10, 2, 56, 1 ], [ 11, 2, 56, 1 ], [ 12, 2, 56, 1 ], [ 13, 2, 56, 1 ], [ 14, 2, 56, 1 ], [ 15, 2, 56, 1 ], [ 16, 2, 56, 1 ], [ 17, 2, 56, 1 ], [ 61, 2, 56, 1 ], [ 62, 2, 56, 1 ], [ 63, 2, 56, 1 ], [ 64, 2, 56, 1 ], [ 65, 2, 56, 1 ], [ 10, 3, 56, 1 ], [ 11, 3, 56, 1 ], [ 12, 3, 56, 1 ], [ 13, 3, 56, 1 ], [ 14, 3, 56, 1 ], [ 15, 3, 56, 1 ], [ 16, 3, 56, 1 ], [ 17, 3, 56, 1 ], [ 61, 3, 56, 1 ], [ 62, 3, 56, 1 ], [ 63, 3, 56, 1 ], [ 64, 3, 56, 1 ], [ 65, 3, 56, 1 ], [ 10, 57, 56, 1 ], [ 11, 57, 56, 1 ], [ 12, 57, 56, 1 ], [ 13, 57, 56, 1 ], [ 14, 57, 56, 1 ], [ 15, 57, 56, 1 ], [ 16, 57, 56, 1 ], [ 17, 57, 56, 1 ], [ 61, 57, 56, 1 ], [ 62, 57, 56, 1 ], [ 63, 57, 56, 1 ], [ 64, 57, 56, 1 ], [ 58, 4, 56, 1 ], [ 59, 4, 56, 1 ], [ 60, 4, 56, 1 ], [ 58, 5, 56, 1 ], [ 59, 5, 56, 1 ], [ 60, 5, 56, 1 ], [ 58, 6, 56, 1 ], [ 59, 6, 56, 1 ], [ 45, 2, 1 ], [ 46, 2, 1 ], [ 47, 2, 1 ], [ 87, 2, 1 ], [ 88, 2, 1 ], [ 89, 2, 1 ], [ 90, 2, 1 ], [ 91, 2, 1 ], [ 96, 56, 56 ], [ 66, 56, 56, 56 ], [ 67, 56, 56, 56 ], [ 68, 56, 56, 56 ], [ 69, 56, 56, 56 ], [ 70, 56, 56, 56 ], [ 71, 56, 56, 56 ], [ 97, 1, 1 ], [ 31, 1, 1, 1 ], [ 32, 1, 1, 1 ], [ 33, 1, 1, 1 ], [ 34, 1, 1, 1 ], [ 35, 1, 1, 1 ], [ 36, 1, 1, 1 ], [ 37, 1, 1, 1 ], [ 38, 1, 1, 1 ], [ 39, 1, 1, 1 ], [ 40, 1, 1, 1 ], [ 41, 1, 1, 1 ], [ 42, 1, 1, 1 ], [ 43, 1, 1, 1 ], [ 44, 1, 1, 1 ], [ 75, 1, 1, 1 ], [ 76, 1, 1, 1 ], [ 77, 1, 1, 1 ], [ 78, 1, 1, 1 ], [ 79, 1, 1, 1 ], [ 80, 1, 1, 1 ], [ 81, 1, 1, 1 ], [ 82, 1, 1, 1 ], [ 83, 1, 1, 1 ], [ 84, 1, 1, 1 ], [ 85, 1, 1, 1 ], [ 86, 1, 1, 1 ], [ 4, 1, 1, 1, 1 ], [ 5, 1, 1, 1, 1 ], [ 6, 1, 1, 1, 1 ], [ 7, 1, 1, 1, 1 ], [ 8, 1, 1, 1, 1 ], [ 9, 1, 1, 1, 1 ], [ 58, 1, 1, 1, 1 ], [ 59, 1, 1, 1, 1 ], [ 60, 1, 1, 1, 1 ], [ 4, 56, 1, 1, 1 ], [ 5, 56, 1, 1, 1 ], [ 6, 56, 1, 1, 1 ], [ 7, 56, 1, 1, 1 ], [ 8, 56, 1, 1, 1 ], [ 9, 56, 1, 1, 1 ], [ 58, 56, 1, 1, 1 ], [ 59, 56, 1, 1, 1 ], [ 60, 56, 1, 1, 1 ], [ 57, 2, 1, 1, 1 ], [ 57, 3, 1, 1, 1 ], [ 31, 56, 1, 1 ], [ 32, 56, 1, 1 ], [ 33, 56, 1, 1 ], [ 34, 56, 1, 1 ], [ 35, 56, 1, 1 ], [ 36, 56, 1, 1 ], [ 37, 56, 1, 1 ], [ 38, 56, 1, 1 ], [ 39, 56, 1, 1 ], [ 40, 56, 1, 1 ], [ 41, 56, 1, 1 ], [ 42, 56, 1, 1 ], [ 43, 56, 1, 1 ], [ 44, 56, 1, 1 ], [ 75, 56, 1, 1 ], [ 76, 56, 1, 1 ], [ 77, 56, 1, 1 ], [ 78, 56, 1, 1 ], [ 79, 56, 1, 1 ], [ 80, 56, 1, 1 ], [ 81, 56, 1, 1 ], [ 82, 56, 1, 1 ], [ 83, 56, 1, 1 ], [ 84, 56, 1, 1 ], [ 85, 56, 1, 1 ], [ 86, 56, 1, 1 ], [ 4, 56, 56, 1, 1 ], [ 5, 56, 56, 1, 1 ], [ 6, 56, 56, 1, 1 ], [ 7, 56, 56, 1, 1 ], [ 8, 56, 56, 1, 1 ], [ 9, 56, 56, 1, 1 ], [ 58, 56, 56, 1, 1 ], [ 59, 56, 56, 1, 1 ], [ 60, 56, 56, 1, 1 ], [ 57, 2, 56, 1, 1 ], [ 57, 3, 56, 1, 1 ], [ 19, 2, 1, 1 ], [ 20, 2, 1, 1 ], [ 21, 2, 1, 1 ], [ 22, 2, 1, 1 ], [ 23, 2, 1, 1 ], [ 24, 2, 1, 1 ], [ 25, 2, 1, 1 ], [ 26, 2, 1, 1 ], [ 27, 2, 1, 1 ], [ 28, 2, 1, 1 ], [ 29, 2, 1, 1 ], [ 66, 2, 1, 1 ], [ 67, 2, 1, 1 ], [ 68, 2, 1, 1 ], [ 69, 2, 1, 1 ], [ 70, 2, 1, 1 ], [ 71, 2, 1, 1 ], [ 72, 2, 1, 1 ], [ 73, 2, 1, 1 ], [ 74, 2, 1, 1 ], [ 19, 3, 1, 1 ], [ 20, 3, 1, 1 ], [ 21, 3, 1, 1 ], [ 22, 3, 1, 1 ], [ 23, 3, 1, 1 ], [ 24, 3, 1, 1 ], [ 25, 3, 1, 1 ], [ 66, 3, 1, 1 ], [ 67, 3, 1, 1 ], [ 68, 3, 1, 1 ], [ 69, 3, 1, 1 ], [ 70, 3, 1, 1 ], [ 71, 3, 1, 1 ], [ 72, 3, 1, 1 ], [ 73, 3, 1, 1 ], [ 74, 3, 1, 1 ], [ 19, 57, 1, 1 ], [ 20, 57, 1, 1 ], [ 21, 57, 1, 1 ], [ 22, 57, 1, 1 ], [ 23, 57, 1, 1 ], [ 24, 57, 1, 1 ], [ 25, 57, 1, 1 ], [ 26, 57, 1, 1 ], [ 27, 57, 1, 1 ], [ 97, 56, 1 ], [ 31, 56, 56, 1 ], [ 32, 56, 56, 1 ], [ 33, 56, 56, 1 ], [ 34, 56, 56, 1 ], [ 35, 56, 56, 1 ], [ 36, 56, 56, 1 ], [ 37, 56, 56, 1 ], [ 38, 56, 56, 1 ], [ 39, 56, 56, 1 ], [ 40, 56, 56, 1 ], [ 41, 56, 56, 1 ], [ 42, 56, 56, 1 ], [ 43, 56, 56, 1 ], [ 44, 56, 56, 1 ], [ 75, 56, 56, 1 ], [ 76, 56, 56, 1 ], [ 77, 56, 56, 1 ], [ 78, 56, 56, 1 ], [ 79, 56, 56, 1 ], [ 80, 56, 56, 1 ], [ 81, 56, 56, 1 ], [ 82, 56, 56, 1 ], [ 83, 56, 56, 1 ], [ 84, 56, 56, 1 ], [ 66, 2, 56, 1 ], [ 67, 2, 56, 1 ], [ 68, 2, 56, 1 ], [ 69, 2, 56, 1 ], [ 70, 2, 56, 1 ], [ 98, 1, 1 ], [ 45, 1, 1, 1 ], [ 46, 1, 1, 1 ], [ 47, 1, 1, 1 ], [ 48, 1, 1, 1 ], [ 49, 1, 1, 1 ], [ 50, 1, 1, 1 ], [ 51, 1, 1, 1 ], [ 52, 1, 1, 1 ], [ 53, 1, 1, 1 ], [ 54, 1, 1, 1 ], [ 55, 1, 1, 1 ], [ 87, 1, 1, 1 ], [ 88, 1, 1, 1 ], [ 89, 1, 1, 1 ], [ 90, 1, 1, 1 ], [ 91, 1, 1, 1 ], [ 92, 1, 1, 1 ], [ 93, 1, 1, 1 ], [ 94, 1, 1, 1 ], [ 95, 1, 1, 1 ], [ 10, 1, 1, 1, 1 ], [ 11, 1, 1, 1, 1 ], [ 12, 1, 1, 1, 1 ], [ 13, 1, 1, 1, 1 ], [ 14, 1, 1, 1, 1 ], [ 15, 1, 1, 1, 1 ], [ 16, 1, 1, 1, 1 ], [ 17, 1, 1, 1, 1 ], [ 18, 1, 1, 1, 1 ], [ 61, 1, 1, 1, 1 ], [ 62, 1, 1, 1, 1 ], [ 63, 1, 1, 1, 1 ], [ 64, 1, 1, 1, 1 ], [ 65, 1, 1, 1, 1 ], [ 1, 1, 1, 1, 1, 1 ], [ 56, 1, 1, 1, 1, 1 ], [ 10, 56, 1, 1, 1 ], [ 11, 56, 1, 1, 1 ], [ 12, 56, 1, 1, 1 ], [ 13, 56, 1, 1, 1 ], [ 14, 56, 1, 1, 1 ], [ 15, 56, 1, 1, 1 ], [ 16, 56, 1, 1, 1 ], [ 17, 56, 1, 1, 1 ], [ 18, 56, 1, 1, 1 ], [ 61, 56, 1, 1, 1 ], [ 62, 56, 1, 1, 1 ], [ 63, 56, 1, 1, 1 ], [ 64, 56, 1, 1, 1 ], [ 65, 56, 1, 1, 1 ], [ 4, 2, 1, 1, 1 ], [ 5, 2, 1, 1, 1 ], [ 6, 2, 1, 1, 1 ], [ 7, 2, 1, 1, 1 ], [ 8, 2, 1, 1, 1 ], [ 9, 2, 1, 1, 1 ], [ 58, 2, 1, 1, 1 ], [ 59, 2, 1, 1, 1 ], [ 60, 2, 1, 1, 1 ], [ 4, 3, 1, 1, 1 ], [ 58, 3, 1, 1, 1 ], [ 59, 3, 1, 1, 1 ], [ 60, 3, 1, 1, 1 ], [ 4, 57, 1, 1, 1 ], [ 5, 57, 1, 1, 1 ], [ 6, 57, 1, 1, 1 ], [ 7, 57, 1, 1, 1 ], [ 8, 57, 1, 1, 1 ], [ 9, 57, 1, 1, 1 ], [ 45, 56, 1, 1 ], [ 46, 56, 1, 1 ], [ 47, 56, 1, 1 ], [ 48, 56, 1, 1 ], [ 49, 56, 1, 1 ], [ 50, 56, 1, 1 ], [ 51, 56, 1, 1 ], [ 52, 56, 1, 1 ], [ 53, 56, 1, 1 ], [ 54, 56, 1, 1 ], [ 55, 56, 1, 1 ], [ 87, 56, 1, 1 ], [ 88, 56, 1, 1 ], [ 89, 56, 1, 1 ], [ 90, 56, 1, 1 ], [ 91, 56, 1, 1 ], [ 92, 56, 1, 1 ], [ 93, 56, 1, 1 ], [ 94, 56, 1, 1 ], [ 95, 56, 1, 1 ], [ 10, 56, 56, 1, 1 ], [ 11, 56, 56, 1, 1 ], [ 12, 56, 56, 1, 1 ], [ 13, 56, 56, 1, 1 ], [ 14, 56, 56, 1, 1 ], [ 15, 56, 56, 1, 1 ], [ 16, 56, 56, 1, 1 ], [ 17, 56, 56, 1, 1 ], [ 18, 56, 56, 1, 1 ], [ 61, 56, 56, 1, 1 ], [ 62, 56, 56, 1, 1 ], [ 63, 56, 56, 1, 1 ], [ 64, 56, 56, 1, 1 ], [ 65, 56, 56, 1, 1 ], [ 4, 2, 56, 1, 1 ], [ 5, 2, 56, 1, 1 ], [ 6, 2, 56, 1, 1 ], [ 7, 2, 56, 1, 1 ], [ 8, 2, 56, 1, 1 ], [ 9, 2, 56, 1, 1 ], [ 58, 2, 56, 1, 1 ], [ 59, 2, 56, 1, 1 ], [ 60, 2, 56, 1, 1 ], [ 4, 3, 56, 1, 1 ], [ 58, 3, 56, 1, 1 ], [ 59, 3, 56, 1, 1 ], [ 60, 3, 56, 1, 1 ], [ 4, 57, 56, 1, 1 ], [ 5, 57, 56, 1, 1 ], [ 6, 57, 56, 1, 1 ], [ 7, 57, 56, 1, 1 ], [ 8, 57, 56, 1, 1 ], [ 9, 57, 56, 1, 1 ], [ 31, 2, 1, 1 ], [ 32, 2, 1, 1 ], [ 33, 2, 1, 1 ], [ 34, 2, 1, 1 ], [ 35, 2, 1, 1 ], [ 75, 2, 1, 1 ], [ 96, 1, 1, 1 ], [ 19, 1, 1, 1, 1 ], [ 20, 1, 1, 1, 1 ], [ 21, 1, 1, 1, 1 ], [ 22, 1, 1, 1, 1 ], [ 23, 1, 1, 1, 1 ], [ 24, 1, 1, 1, 1 ], [ 25, 1, 1, 1, 1 ], [ 26, 1, 1, 1, 1 ], [ 27, 1, 1, 1, 1 ], [ 28, 1, 1, 1, 1 ], [ 29, 1, 1, 1, 1 ], [ 30, 1, 1, 1, 1 ], [ 66, 1, 1, 1, 1 ], [ 67, 1, 1, 1, 1 ], [ 68, 1, 1, 1, 1 ], [ 69, 1, 1, 1, 1 ], [ 70, 1, 1, 1, 1 ], [ 71, 1, 1, 1, 1 ], [ 72, 1, 1, 1, 1 ], [ 73, 1, 1, 1, 1 ], [ 74, 1, 1, 1, 1 ], [ 2, 1, 1, 1, 1, 1 ], [ 3, 1, 1, 1, 1, 1 ], [ 57, 1, 1, 1, 1, 1 ], [ 2, 56, 1, 1, 1, 1 ], [ 3, 56, 1, 1, 1, 1 ], [ 19, 56, 1, 1, 1 ], [ 20, 56, 1, 1, 1 ], [ 21, 56, 1, 1, 1 ], [ 22, 56, 1, 1, 1 ], [ 23, 56, 1, 1, 1 ], [ 24, 56, 1, 1, 1 ], [ 25, 56, 1, 1, 1 ], [ 26, 56, 1, 1, 1 ], [ 27, 56, 1, 1, 1 ], [ 28, 56, 1, 1, 1 ], [ 29, 56, 1, 1, 1 ], [ 30, 56, 1, 1, 1 ], [ 66, 56, 1, 1, 1 ], [ 67, 56, 1, 1, 1 ], [ 68, 56, 1, 1, 1 ], [ 69, 56, 1, 1, 1 ], [ 70, 56, 1, 1, 1 ], [ 71, 56, 1, 1, 1 ], [ 72, 56, 1, 1, 1 ], [ 73, 56, 1, 1, 1 ], [ 74, 56, 1, 1, 1 ], [ 2, 56, 56, 1, 1, 1 ], [ 3, 56, 56, 1, 1, 1 ], [ 10, 2, 1, 1, 1 ], [ 11, 2, 1, 1, 1 ], [ 12, 2, 1, 1, 1 ], [ 13, 2, 1, 1, 1 ], [ 14, 2, 1, 1, 1 ], [ 15, 2, 1, 1, 1 ], [ 16, 2, 1, 1, 1 ], [ 17, 2, 1, 1, 1 ], [ 61, 2, 1, 1, 1 ], [ 62, 2, 1, 1, 1 ], [ 63, 2, 1, 1, 1 ], [ 64, 2, 1, 1, 1 ], [ 65, 2, 1, 1, 1 ], [ 10, 3, 1, 1, 1 ], [ 11, 3, 1, 1, 1 ], [ 12, 3, 1, 1, 1 ], [ 13, 3, 1, 1, 1 ], [ 14, 3, 1, 1, 1 ], [ 15, 3, 1, 1, 1 ], [ 16, 3, 1, 1, 1 ], [ 17, 3, 1, 1, 1 ], [ 61, 3, 1, 1, 1 ], [ 62, 3, 1, 1, 1 ], [ 63, 3, 1, 1, 1 ], [ 64, 3, 1, 1, 1 ], [ 65, 3, 1, 1, 1 ], [ 10, 57, 1, 1, 1 ], [ 11, 57, 1, 1, 1 ], [ 12, 57, 1, 1, 1 ], [ 13, 57, 1, 1, 1 ], [ 14, 57, 1, 1, 1 ], [ 15, 57, 1, 1, 1 ], [ 16, 57, 1, 1, 1 ], [ 17, 57, 1, 1, 1 ], [ 61, 57, 1, 1, 1 ], [ 62, 57, 1, 1, 1 ], [ 63, 57, 1, 1, 1 ], [ 64, 57, 1, 1, 1 ], [ 58, 4, 1, 1, 1 ], [ 59, 4, 1, 1, 1 ], [ 96, 56, 1, 1 ], [ 19, 56, 56, 1, 1 ], [ 20, 56, 56, 1, 1 ], [ 21, 56, 56, 1, 1 ], [ 22, 56, 56, 1, 1 ], [ 23, 56, 56, 1, 1 ], [ 97, 1, 1, 1 ], [ 31, 1, 1, 1, 1 ], [ 32, 1, 1, 1, 1 ], [ 33, 1, 1, 1, 1 ], [ 34, 1, 1, 1, 1 ], [ 35, 1, 1, 1, 1 ], [ 36, 1, 1, 1, 1 ], [ 37, 1, 1, 1, 1 ], [ 38, 1, 1, 1, 1 ], [ 39, 1, 1, 1, 1 ], [ 40, 1, 1, 1, 1 ], [ 41, 1, 1, 1, 1 ], [ 42, 1, 1, 1, 1 ], [ 43, 1, 1, 1, 1 ], [ 44, 1, 1, 1, 1 ], [ 75, 1, 1, 1, 1 ], [ 76, 1, 1, 1, 1 ], [ 77, 1, 1, 1, 1 ], [ 78, 1, 1, 1, 1 ], [ 79, 1, 1, 1, 1 ], [ 80, 1, 1, 1, 1 ], [ 81, 1, 1, 1, 1 ], [ 82, 1, 1, 1, 1 ], [ 83, 1, 1, 1, 1 ], [ 84, 1, 1, 1, 1 ], [ 85, 1, 1, 1, 1 ], [ 86, 1, 1, 1, 1 ], [ 4, 1, 1, 1, 1, 1 ], [ 5, 1, 1, 1, 1, 1 ], [ 6, 1, 1, 1, 1, 1 ], [ 7, 1, 1, 1, 1, 1 ], [ 8, 1, 1, 1, 1, 1 ], [ 9, 1, 1, 1, 1, 1 ], [ 58, 1, 1, 1, 1, 1 ], [ 59, 1, 1, 1, 1, 1 ], [ 60, 1, 1, 1, 1, 1 ], [ 4, 56, 1, 1, 1, 1 ], [ 5, 56, 1, 1, 1, 1 ], [ 6, 56, 1, 1, 1, 1 ], [ 7, 56, 1, 1, 1, 1 ], [ 8, 56, 1, 1, 1, 1 ], [ 9, 56, 1, 1, 1, 1 ], [ 58, 56, 1, 1, 1, 1 ], [ 59, 56, 1, 1, 1, 1 ], [ 60, 56, 1, 1, 1, 1 ], [ 57, 2, 1, 1, 1, 1 ], [ 57, 3, 1, 1, 1, 1 ], [ 31, 56, 1, 1, 1 ], [ 32, 56, 1, 1, 1 ], [ 33, 56, 1, 1, 1 ], [ 34, 56, 1, 1, 1 ], [ 35, 56, 1, 1, 1 ], [ 36, 56, 1, 1, 1 ], [ 37, 56, 1, 1, 1 ], [ 38, 56, 1, 1, 1 ], [ 39, 56, 1, 1, 1 ], [ 40, 56, 1, 1, 1 ], [ 75, 56, 1, 1, 1 ], [ 76, 56, 1, 1, 1 ], [ 77, 56, 1, 1, 1 ], [ 78, 56, 1, 1, 1 ], [ 79, 56, 1, 1, 1 ], [ 80, 56, 1, 1, 1 ], [ 81, 56, 1, 1, 1 ], [ 82, 56, 1, 1, 1 ], [ 83, 56, 1, 1, 1 ], [ 84, 56, 1, 1, 1 ], [ 85, 56, 1, 1, 1 ], [ 86, 56, 1, 1, 1 ], [ 98, 1, 1, 1 ], [ 45, 1, 1, 1, 1 ], [ 46, 1, 1, 1, 1 ], [ 47, 1, 1, 1, 1 ], [ 48, 1, 1, 1, 1 ], [ 49, 1, 1, 1, 1 ], [ 50, 1, 1, 1, 1 ], [ 51, 1, 1, 1, 1 ], [ 52, 1, 1, 1, 1 ], [ 53, 1, 1, 1, 1 ], [ 54, 1, 1, 1, 1 ], [ 55, 1, 1, 1, 1 ], [ 87, 1, 1, 1, 1 ], [ 88, 1, 1, 1, 1 ], [ 89, 1, 1, 1, 1 ], [ 90, 1, 1, 1, 1 ], [ 91, 1, 1, 1, 1 ], [ 92, 1, 1, 1, 1 ], [ 93, 1, 1, 1, 1 ], [ 94, 1, 1, 1, 1 ], [ 95, 1, 1, 1, 1 ], [ 10, 1, 1, 1, 1, 1 ], [ 11, 1, 1, 1, 1, 1 ], [ 12, 1, 1, 1, 1, 1 ], [ 13, 1, 1, 1, 1, 1 ], [ 14, 1, 1, 1, 1, 1 ], [ 15, 1, 1, 1, 1, 1 ], [ 16, 1, 1, 1, 1, 1 ], [ 17, 1, 1, 1, 1, 1 ], [ 18, 1, 1, 1, 1, 1 ], [ 61, 1, 1, 1, 1, 1 ], [ 62, 1, 1, 1, 1, 1 ], [ 63, 1, 1, 1, 1, 1 ], [ 64, 1, 1, 1, 1, 1 ], [ 65, 1, 1, 1, 1, 1 ], [ 1, 1, 1, 1, 1, 1, 1 ], [ 56, 1, 1, 1, 1, 1, 1 ], [ 10, 56, 1, 1, 1, 1 ], [ 11, 56, 1, 1, 1, 1 ], [ 12, 56, 1, 1, 1, 1 ], [ 13, 56, 1, 1, 1, 1 ], [ 14, 56, 1, 1, 1, 1 ], [ 15, 56, 1, 1, 1, 1 ], [ 16, 56, 1, 1, 1, 1 ], [ 17, 56, 1, 1, 1, 1 ], [ 18, 56, 1, 1, 1, 1 ], [ 96, 1, 1, 1, 1 ], [ 19, 1, 1, 1, 1, 1 ], [ 20, 1, 1, 1, 1, 1 ], [ 21, 1, 1, 1, 1, 1 ], [ 22, 1, 1, 1, 1, 1 ], [ 23, 1, 1, 1, 1, 1 ], [ 24, 1, 1, 1, 1, 1 ], [ 25, 1, 1, 1, 1, 1 ], [ 26, 1, 1, 1, 1, 1 ], [ 27, 1, 1, 1, 1, 1 ], [ 28, 1, 1, 1, 1, 1 ], [ 29, 1, 1, 1, 1, 1 ], [ 30, 1, 1, 1, 1, 1 ], [ 66, 1, 1, 1, 1, 1 ], [ 67, 1, 1, 1, 1, 1 ], [ 68, 1, 1, 1, 1, 1 ], [ 69, 1, 1, 1, 1, 1 ], [ 70, 1, 1, 1, 1, 1 ], [ 71, 1, 1, 1, 1, 1 ], [ 72, 1, 1, 1, 1, 1 ], [ 73, 1, 1, 1, 1, 1 ], [ 74, 1, 1, 1, 1, 1 ], [ 57, 1, 1, 1, 1, 1, 1 ], [ 2, 56, 1, 1, 1, 1, 1 ], [ 3, 56, 1, 1, 1, 1, 1 ], [ 19, 56, 1, 1, 1, 1 ], [ 97, 1, 1, 1, 1 ], [ 31, 1, 1, 1, 1, 1 ], [ 32, 1, 1, 1, 1, 1 ], [ 33, 1, 1, 1, 1, 1 ], [ 34, 1, 1, 1, 1, 1 ], [ 35, 1, 1, 1, 1, 1 ], [ 36, 1, 1, 1, 1, 1 ], [ 75, 1, 1, 1, 1, 1 ], [ 76, 1, 1, 1, 1, 1 ], [ 77, 1, 1, 1, 1, 1 ], [ 78, 1, 1, 1, 1, 1 ], [ 79, 1, 1, 1, 1, 1 ], [ 80, 1, 1, 1, 1, 1 ], [ 81, 1, 1, 1, 1, 1 ], [ 82, 1, 1, 1, 1, 1 ], [ 83, 1, 1, 1, 1, 1 ], [ 98, 1, 1, 1, 1 ], [ 45, 1, 1, 1, 1, 1 ], [ 46, 1, 1, 1, 1, 1 ], [ 47, 1, 1, 1, 1, 1 ], [ 87, 1, 1, 1, 1, 1 ], [ 88, 1, 1, 1, 1, 1 ], [ 89, 1, 1, 1, 1, 1 ], [ 90, 1, 1, 1, 1, 1 ], [ 91, 1, 1, 1, 1, 1 ], [ 96, 1, 1, 1, 1, 1 ], [ 19, 1, 1, 1, 1, 1, 1 ], [ 66, 1, 1, 1, 1, 1, 1 ], [ 97, 1, 1, 1, 1, 1 ], [ 31, 1, 1, 1, 1, 1, 1 ]];

function CheckSecondaryInvariants(n)
	forms := FormsGenerator(L1[n+1]+10, K);
	time list_valued_hsop, list_valued_others := EvaluationInvariants(forms); 
	time list_valued_inv_sec := [[EvaluationSecondaryInvariants(g, j, list_valued_others) : g in inv_sec] : j in [1..#forms]];

	res_sym := [];
	res_non_sym := [];

	for i in [1..Floor(n/2)] do
		"degre", 2*i;
		time inv_sec_sym_int, inv_sec_non_sym_int, N := invariants_secondaires_non_sym(inv_sec, forms, list_valued_hsop, list_valued_others, list_valued_inv_sec, L1, 2*i);
		"number sym", #inv_sec_sym_int;
		"number not sym", #inv_sec_non_sym_int;
		"expected dimension", L1[2*i+1];
		"dimension found", N;
		" ";
		Append(~res_sym, inv_sec_sym_int);
		Append(~res_non_sym, inv_sec_non_sym_int);
	end for;

	return res_sym, res_non_sym;
end function;



// Proof that the invariants belong to the same field as the field of definition of the non-hyp genus 4 curve in P^3
// To prove that, we check that the first invariant I2 does not depend on the choice of the square root
R<a3000,a2100,a2010,a2001,a1200,a1110,a1101,a1020,a1011,a1002,a0300,a0210,a0201,a0120,a0111,a0102,a0030,a0021,a0012,a0003,A,B,D1,D2> := PolynomialRing(Rationals(), 24);
S<X,Y,Z,T> := PolynomialRing(FieldOfFractions(R), 4);
C := a3000*X^3+a2100*X^2*Y+a2010*X^2*Z+a2001*X^2*T+a1200*X*Y^2+a1110*X*Y*Z+a1101*X*Y*T+a1020*X*Z^2+a1011*X*Z*T+a1002*X*T^2+a0300*Y^3+a0210*Y^2*Z+a0201*Y^2*T+a0120*Y*Z^2+a0111*Y*Z*T+a0102*Y*T^2+a0030*Z^3+a0021*Z^2*T+a0012*Z*T^2+a0003*T^3;
Q := A*X^2-A*D1^2*T^2+B*Y^2-B*D2^2*Z^2;

F0 := Evaluate(C, [1/(2*A)*X+1/2*T, -1/(2*B)*Y+1/2*Z, -1/(2*B*D2)*Y-1/(2*D2)*Z, 1/(2*A*D1)*X-1/(2*D1)*T]);
F1 := Evaluate(C, [1/(2*A)*X+1/2*T, -1/(2*B)*Y+1/2*Z, 1/(2*B*D2)*Y+1/(2*D2)*Z, 1/(2*A*D1)*X-1/(2*D1)*T]); 
F2 := Evaluate(C, [1/(2*A)*X+1/2*T, -1/(2*B)*Y+1/2*Z, -1/(2*B*D2)*Y-1/(2*D2)*Z, -1/(2*A*D1)*X+1/(2*D1)*T]);
F3 := Evaluate(C, [1/(2*A)*X+1/2*T, -1/(2*B)*Y+1/2*Z, 1/(2*B*D2)*Y+1/(2*D2)*Z, -1/(2*A*D1)*X+1/(2*D1)*T]); 

_<x,y,u,v> := PolynomialRing(FieldOfFractions(R), 4);
f0 := Evaluate(F0, [x*u, x*v, y*u, y*v]);
f1 := Evaluate(F1, [x*u, x*v, y*u, y*v]);
f2 := Evaluate(F2, [x*u, x*v, y*u, y*v]);
f3 := Evaluate(F3, [x*u, x*v, y*u, y*v]);

s0 := Transvectant(f0, f0, 3, 3 : invariant := true);
s1 := Transvectant(f1, f1, 3, 3 : invariant := true);
s2 := Transvectant(f2, f2, 3, 3 : invariant := true);
s3 := Transvectant(f3, f3, 3, 3 : invariant := true);

s0 eq s1; s0 eq s2; s0 eq s3;