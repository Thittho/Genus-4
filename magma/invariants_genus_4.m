declare verbose Genus4, 1;

import "tools.m" : QuadraticFormToMatrix, NewBasis, ChangeOfBasis, CubicNewBasis;

function InvariantsGenus4CurvesRank4(f : normalize := false)
	K := BaseRing(Parent(f));

    GCD_hsop := [288, 12288, 746496, 12582912, 1741425868800, 19327352832, 764411904, 144, 570630428688384, 4076863488];
	GCD_others := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 144, 144, 144, 1, 1, 1, 1, 1, 144, 144, 144, 144, 144, 144, 144, 144, 144, 144, 144, 144, 144, 144, 144, 144, 144, 144, 144, 144, 144, 144, 144, 144, 144, 144, 144, 144, 144, 144, 144, 144 ];

	Jac := Transvectant(f, f, 1, 1);
	H := Transvectant(f, f, 2, 2);

	// Covariants
	// Degree 3
	c31 := ExactQuotient(Transvectant(H, f, 2, 2), 1536);

	c331 := Transvectant(Jac, f, 2, 2);
	c332 := Transvectant(H, f, 1, 1);

	// Degree 4
	c421 := Transvectant(H, H, 1, 1);
	c422 := Transvectant(c31, f, 1, 1);
	c423 := Transvectant(c332, f, 2, 2);

	c441 := Transvectant(c332, f, 1, 1);
	c442 := Transvectant(Transvectant(Jac, f, 1, 1), f, 2, 2);

	// Degree 5
	c511 := ExactQuotient(Transvectant(c422, f, 2, 2), 144);
	c512 := ExactQuotient(Transvectant(c441, f, 3, 3), 995328);
	c513 := ExactQuotient(Transvectant(c442, f, 3, 3), 1492992);

	c531 := Transvectant(c422, f, 1, 1);
	c532 := Transvectant(c423, f, 1, 1);
	c533 := Transvectant(Transvectant(f^3, f, 3, 3), f, 3, 3);

	// Degree 6
	c621 := Transvectant(c531, f, 2, 2);
	c622 := Transvectant(c532, f, 2, 2);
	c623 := Transvectant(c511, f, 1, 1);

	// Degree 7
	c711 := ExactQuotient(Transvectant(c621, f, 2, 2), 9216);
	c712 := ExactQuotient(Transvectant(c511, Transvectant(f, f, 2, 2), 1, 1), 32);
	c713 := ExactQuotient(Transvectant(c512, Transvectant(f, f, 2, 2), 1, 1), 96);
    
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
	I2 := Transvectant(f, f, 3, 3 : invariant := true);//288
	I41 := Transvectant(H, H, 2, 2 : invariant := true);//12288
	I42 := Transvectant(c331, f, 3, 3 : invariant := true);//746496
	I61 := Transvectant(H, c421, 2, 2 : invariant := true);//12582912
	I62 := Transvectant(c533, f, 3, 3 : invariant :=  true);//1741425868800
	I81 := Transvectant(c421, c421, 2, 2 : invariant := true);//19327352832
	I82 := Transvectant(c731, f, 3, 3 : invariant := true);//764411904
	I10 := Transvectant(f, c31^3, 3, 3 : invariant := true);//432
	I12 := Transvectant(c113, f, 3, 3 : invariant := true);//570630428688384
	I14 := Transvectant(c111*H, f, 3, 3 : invariant := true);//4076863488
	invHSOP := [K | I2,I41,I42,I61,I62,I81,I82,I10,I12,I14];

	// Degree 6
	j61 := Transvectant(c31, c31, 1, 1 : invariant := true);//2
	inv6 := [K | j61];

	// Degree 8
	j81 := Transvectant(c31, c511, 1, 1 : invariant := true);//2
	j82 := Transvectant(c31, c512, 1, 1 : invariant := true);//2
	inv8 := [K | j81,j82];

	// Degree 10
	j101 := Transvectant(c511, c511, 1, 1 : invariant := true);//2
    j102 := Transvectant(c511, c512, 1, 1 : invariant := true);//2
    j103 := Transvectant(c511, c513, 1, 1 : invariant := true);//2
    j104 := Transvectant(c512, c512, 1, 1 : invariant := true);//2
    j105 := Transvectant(c512, c513, 1, 1 : invariant := true);//2
    j106 := Transvectant(c513, c513, 1, 1 : invariant := true);//2
	inv10 := [K | j101,j102,j103,j104,j105,j106];

	// Degree 12
    j121 := Transvectant(c711, c511, 1, 1 : invariant := true);//1
    j122 := Transvectant(c711, c512, 1, 1 : invariant := true);//2
    j123 := Transvectant(c711, c513, 1, 1 : invariant := true);//1
    j124 := Transvectant(c712, c511, 1, 1 : invariant := true);//2
    j125 := Transvectant(c712, c512, 1, 1 : invariant := true);//6
    j126 := Transvectant(c712, c513, 1, 1 : invariant := true);//2
    j127 := Transvectant(f, c511*c31^2, 3, 3 : invariant := true);//432
    j128 := Transvectant(f, c512*c31^2, 3, 3 : invariant := true);//432
    j129 := Transvectant(f, c513*c31^2, 3, 3 : invariant := true);//432
	inv12 := [K | j121,j122,j123,j124,j125,j126,j127,j128,j129];

	// Degree 14
	j141 := Transvectant(c711, c711, 1, 1 : invariant := true);//2
    j142 := Transvectant(c711, c712, 1, 1 : invariant := true);//1
	j143 := Transvectant(c711, c713, 1, 1 : invariant := true);//2
    j144 := Transvectant(c712, c713, 1, 1 : invariant := true);//2
	j145 := Transvectant(c713, c713, 1, 1 : invariant := true);//2
    j146 := Transvectant(f, c511*c511*c31, 3, 3 : invariant := true);//144
    j147 := Transvectant(f, c511*c512*c31, 3, 3 : invariant := true);//432
    j148 := Transvectant(f, c511*c513*c31, 3, 3 : invariant := true);//144
    j149 := Transvectant(f, c512*c512*c31, 3, 3 : invariant := true);//432
    j1410 := Transvectant(f, c512*c513*c31, 3, 3 : invariant := true);//432
    j1411 := Transvectant(f, c513*c513*c31, 3, 3 : invariant := true);//144
    j1412 := Transvectant(f, c711*c31*c31, 3, 3 : invariant := true);//432
	inv14 := [K | j141,j142,j143,j144,j145,j146,j147,j148,j149,j1410,j1411,j1412];

	// Degree 16
	j161 := Transvectant(f, c711*c511*c31, 3, 3 : invariant := true);//144
    j162 := Transvectant(f, c711*c512*c31, 3, 3 : invariant := true);//432
    j163 := Transvectant(f, c711*c513*c31, 3, 3 : invariant := true);//144
    j164 := Transvectant(f, c712*c511*c31, 3, 3 : invariant := true);//144
    j165 := Transvectant(f, c511*c511*c511, 3, 3 : invariant := true);//432
    j166 := Transvectant(f, c511*c511*c512, 3, 3 : invariant := true);//144
    j167 := Transvectant(f, c511*c511*c513, 3, 3 : invariant := true);//144
    j168 := Transvectant(f, c511*c512*c512, 3, 3 : invariant := true);//432
    j169 := Transvectant(f, c511*c512*c513, 3, 3 : invariant := true);//144
    j1610 := Transvectant(f, c511*c513*c513, 3, 3 : invariant := true);//144
    j1611 := Transvectant(f, c512*c512*c512, 3, 3 : invariant := true);//432
    j1612 := Transvectant(f, c512*c512*c513, 3, 3 : invariant := true);//432
    j1613 := Transvectant(f, c512*c513*c513, 3, 3 : invariant := true);//144
    j1614 := Transvectant(f, c513*c513*c513, 3, 3 : invariant := true);//432
    inv16 := [K | j161,j162,j163,j164,j165,j166,j167,j168,j169,j1610,j1611,j1612,j1613,j1614];


	// Degree 18
	j181 := Transvectant(f, c711*c711*c31, 3, 3 : invariant := true);//144
	j182 := Transvectant(f, c711*c511*c511, 3, 3 : invariant := true);//144
	j183 := Transvectant(f, c711*c511*c512, 3, 3 : invariant := true);//144
	j184 := Transvectant(f, c711*c511*c513, 3, 3 : invariant := true);//144
	j185 := Transvectant(f, c711*c512*c512, 3, 3 : invariant := true);//432
        j186 := Transvectant(f, c711*c512*c513, 3, 3 : invariant := true);//144
	j187 := Transvectant(f, c711*c513*c513, 3, 3 : invariant := true);//144
	j188 := Transvectant(f, c711*c712*c31, 3, 3 : invariant := true);//144
	j189 := Transvectant(f, c712*c712*c31, 3, 3 : invariant := true);//144
	j1810 := Transvectant(f, c712*c511*c512, 3, 3 : invariant := true);//144
	j1811 := Transvectant(f, c712*c512*c512, 3, 3 : invariant := true);//432
	inv18 := [K | j181,j182,j183,j184,j185,j186,j187,j188,j189,j1810,j1811];

	invOthers := inv6 cat inv8 cat inv10 cat inv12 cat inv14 cat inv16 cat inv18;

	if Type(K) eq RngInt then
		Inv := [ExactQuotient(invHSOP[i], GCD_hsop[i]) : i in [1..#invHSOP]] cat [ExactQuotient(invOthers[i], GCD_others[i]) : i in [1..#invOthers]];
	else
		Inv := [invHSOP[i]/GCD_hsop[i] : i in [1..#invHSOP]] cat [invOthers[i]/GCD_others[i] : i in [1..#invOthers]];
	end if;

	Wgt := [2,4,4,6,6,8,8,10,12,14,6,8,8,10,10,10,10,10,10,12,12,12,12,12,12,12,12,12,14,14,14,14,14,14,14,14,14,14,14,14,16,16,16,16,16,16,16,16,16,16,16,16,16,16,18,18,18,18,18,18,18,18,18,18,18];

	if normalize then
		return WPSNormalize(Wgt, Inv), Wgt;
	end if;

	return Inv, Wgt;
end function;


function InvariantsGenus4CurvesRank3(f, v)
	K := BaseRing(Parent(f));

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
	invf := [K | J2f, J4f, J6f, J10f, J15f];

	// Invariants of v
	J2v := Evaluate(Transvectant(v, v, 4), [0,0]);
	J3v := Evaluate(Transvectant(k24, v, 4), [0,0]);
	invv := [K | J2v, J3v];

	//  Joint degree 3
	J3 := Evaluate(Transvectant(h24, v, 4), [0,0]);
	inv3 := [K | J3];

	//  Joint degree 4
	J41 := Evaluate(Transvectant(h28, v^2, 8), [0,0]);
	J42 := Evaluate(Transvectant(h24, k24, 4), [0,0]);
	J43 := Evaluate(Transvectant(k36, f, 6), [0,0]);
	inv4 := [K | J41, J42, J43];

	// Joint degree 5
	J51 := Evaluate(Transvectant(h38, v^2, 8), [0,0]);
	J52 := Evaluate(Transvectant(h44, v, 4), [0,0]);
	J53 := Evaluate(Transvectant(h28, v*k24, 8), [0,0]);
	J54 := Evaluate(Transvectant(f^2, v^3, 12), [0,0]);
	inv5 := [K | J51, J52, J53, J54];

	// Joint degree 6
	J61 := Evaluate(Transvectant(h38, v*k24, 8), [0,0]);
	J62 := Evaluate(Transvectant(f^2, v^2*k24, 12), [0,0]);
	J63 := Evaluate(Transvectant(h28, k24^2, 8), [0,0]);
	J64 := Evaluate(Transvectant(h36, k36, 6), [0,0]);
	J65 := Evaluate(Transvectant(h312, v^3, 12), [0,0]);
	J66 := Evaluate(Transvectant(h54, v, 4), [0,0]);
	J67 := Evaluate(Transvectant(h44, k24, 4), [0,0]);
	J68 := Evaluate(Transvectant(h32*f, v^2, 8), [0,0]);
	inv6 := [K | J61, J62, J63, J64, J65, J66, J67, J68];

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
	inv7 := [K | J71, J72, J73, J74, J75, J76, J77, J78, J79];

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
	inv8 := [K | J81, J82, J83, J84, J85, J86, J87, J88, J89];

	// Joint degree 9
	J91 := Evaluate(Transvectant(h74, k24, 4), [0,0]);
	J92 := Evaluate(Transvectant(h32*h52, v, 4), [0,0]);
	J93 := Evaluate(Transvectant(h52*f, v*k24, 8), [0,0]);
	J94 := Evaluate(Transvectant(h312, k24^3, 12), [0,0]);
	J95 := Evaluate(Transvectant(h32*h28, v*k36, 10), [0,0]);
	J96 := Evaluate(Transvectant(f*h46, v^2*k24, 12), [0,0]);
	J97 := Evaluate(Transvectant(h36^2, v^3, 12), [0,0]);
	J98 := Evaluate(Transvectant(h32*h46, v^2, 8), [0,0]);
	inv9 := [K | J91, J92, J93, J94, J95, J96, J97, J98];

	// Joint degree 10
	J101 := Evaluate(Transvectant(h94, v, 4), [0,0]);
	J102 := Evaluate(Transvectant(h32*h28, k24*k36, 10), [0,0]);
	J103 := Evaluate(Transvectant(h52*h36, v^2, 8), [0,0]);
	J104 := Evaluate(Transvectant(f*h661, v^3, 12), [0,0]);
	inv10 := [K | J101, J102, J103, J104];

	// Joint degree 11
	J111 := Evaluate(Transvectant(h52^2, v, 4), [0,0]);
	J112 := Evaluate(Transvectant(f*h662, v^2*k24, 12), [0,0]);
	J113 := Evaluate(Transvectant(h32*h661, v^2, 8), [0,0]);
	inv11 := [K | J111, J112, J113];

	// Joint degree 12
	J121 := Evaluate(Transvectant(h32*h82, v, 4), [0,0]);
	J122 := Evaluate(Transvectant(h32*h662, v*k24, 8), [0,0]);
	inv12 := [K | J121, J122];

	// Joint degree 13
	J13 := Evaluate(Transvectant(h82*h36, v^2, 8), [0,0]);
	inv13 := [K | J13];

	// Joint degree 14
	J14 := Evaluate(Transvectant(h32*h102, v, 4), [0,0]);
	inv14 := [K | J14];

	return invf cat invv cat inv3 cat inv4 cat inv5 cat inv6 cat inv7 cat inv8 cat inv9 cat inv10 cat inv11 cat inv12 cat inv13 cat inv14, [6,12,18,30,45,4,6,8,10,10,9,13,14,12,12,15,14,14,15,15,17,16,16,20,19,19,18,16,18,18,17,17,21,19,22,22,23,21,20,20,21,25,26,24,21,23,23,24,25,29,25,28,27,32,29,31,35,33,37,41];

end function;


intrinsic InvariantsGenus4Curves(Q::RngMPolElt, C::RngMPolElt : normalize := false) -> SeqEnum, SeqEnum
	{Given a homogeneous quadratic form and a homogeneous cubic form in 4 variables, returns its invariants as a genus 4 curve. The invariants returned depend on the rank of the quadratic form.}

	require (Parent(Q) eq Parent(C)): "Q and C must have the same parent";
	require (Rank(Parent(Q)) eq 4): "Q and C must be polynomials in 4 variables";
	require IsHomogeneous(Q) and IsHomogeneous(C): "Q and C must be homogeneous";
	require (Degree(Q) eq 2) and (Degree(C) eq 3): "Q must be of degree 2 and C of degree 3";

	R0<X,Y,Z,T> := Parent(Q);
	K := BaseRing(R0);

	if Q eq X*T-Y*Z then
		f0 := C;
		P := IdentityMatrix(K, 4);
		t := 4;
	elif Q eq X*Z-Y^2 then
		f0 := C;
		t := 3;
		P := IdentityMatrix(K, 4);
		r := 1;
	else
		P, t, r := NewBasis(Q);
		if t eq 4 then
			vprint Genus4 : "Quadric of rank 4";
			vprint Genus4 : "Computing basis for the canonical form of the quadric...";
			f0 := ChangeOfBasis(C,P);
			ChangeOfBasis(Q,P);
		elif t eq 3 then
			vprint Genus4 : "Quadric of rank 3";
			vprint Genus4 : "Computing basis for the canonical form of the quadric...";
			f0 := ChangeOfBasis(C,P);
			ChangeOfBasis(Q,P);
		end if;
	end if;

	if t eq 4 then

		R<x, y, u, v> := PolynomialRing(BaseRing(Parent(f0)), 4);
		vprint Genus4 : "Computing bicubic form...";
		f_bic := Evaluate(f0, [x*u, y*u, x*v, y*v]);

		vprint Genus4 : "Computing invariants...";
		Inv, Wgt := InvariantsGenus4CurvesRank4(f_bic);
		Inv := WPSMultiply(Wgt, Inv, 1/Determinant(P));
		Inv := ChangeUniverse(Inv, K);

		if normalize then
			return  WPSNormalize(Wgt, Inv), Wgt;
		end if;

		return Inv, Wgt;

	elif t eq 3 then

		R<s, t, w> := PolynomialRing(BaseRing(Parent(f0)), [1,1,2]);
		f_weighted := Evaluate(f0, [s^2, s*t, t^2, w]);
		vprint Genus4 : "Computing normal form of the sextic...";
		require MonomialCoefficient(f_weighted, w^3) ne 0: "The curve is not smooth";

		// we put the curve in normal form
		alpha := MonomialCoefficient(f_weighted, w^3);
		f_weighted /:= alpha;
		f_weighted := Evaluate(f_weighted, [s, t, w-ExactQuotient(Terms(f_weighted, w)[3], 3*w^2)]);

		f_weighted := Evaluate(f_weighted, [s, t, w]);

		S<[x]> := PolynomialRing(BaseRing(Parent(f_weighted)), 2);
		vprint Genus4 : "Computing invariants...";
		Inv, Wgt := InvariantsGenus4CurvesRank3(S!Evaluate(f_weighted, [x[1], x[2], 0]), S!Evaluate(ExactQuotient(Terms(f_weighted, w)[2], w), [x[1], x[2], 0]));
		Inv := WPSMultiply(Wgt, Inv, 1/Determinant(P));
		Inv := ChangeUniverse(Inv, K);

		if normalize then
			return WPSNormalize(Wgt, Inv), Wgt;
		end if;

		return Inv, Wgt;
	end if;

end intrinsic;

intrinsic InvariantsGenus4Curves(C::Crv : normalize := false) -> SeqEnum, SeqEnum
	{Compute the invariants of a non-hyperelliptic genus 4 curve.}

	require Genus(C) eq 4 : "C must be of genus 4.";

	vprint Genus4 : "Checking if the curve is hyperelliptic...";
	if Degree(C) gt 6 then
		t, E := IsHyperelliptic(C);
		if t then
			vprint Genus4 : "The curve is hyperelliptic.";
			return InvariantsGenus4Curves(E : normalize := normalize);
		end if;
	else
		vprint Genus4 : "The curve is non-hyperelliptic, computing equations...";

		Eq := Equations(C);
		if Sort([Degree(l) : l in Eq]) eq [2,3] then
			L := Eq;
		else
			L := Equations(Image(CanonicalEmbedding(C)));
		end if;
		Deg := [Degree(l) : l in L];
		i := Index(Deg, 2);
		j := Index(Deg, 3);
		Q := L[i];
		E := L[j];
	end if;

	return InvariantsGenus4Curves(Q, E : normalize := normalize);
end intrinsic;

import "gordan-10.dat" : FdCov;
import "invS10.m" : GetCovariant;

intrinsic InvariantsGenus4Curves(f::RngMPolElt : normalize := false) -> SeqEnum, SeqEnum
	{Compute the invariants of a multivariate polynomial of degree 10 as a binary form of degree 10.}

	require Rank(Parent(f)) eq 2: "f must be a bivariate polynomial";
        require IsHomogeneous(f): "f must be homogeneous";
        require Degree(f) eq 10: "f must be of degree 10";

	IdxInv := [idx : idx in [1..#FdCov] | FdCov[idx]`order eq 0];
	List_invariants := [GetCovariant(FdCov[IdxInv[i]], FdCov, f) : i in [1..#IdxInv]];
	Inv := [Evaluate(List_invariants[i][1], [0,0]) : i in [1..#IdxInv]];
	Wgt := [Integers()!List_invariants[i][2] : i in [1..#IdxInv]];

	if normalize then
		return WPSNormalize(Wgt, Inv), Wgt;
	end if;

	return Inv, Wgt;
end intrinsic;


intrinsic InvariantsGenus4Curves(f::RngUPolElt : normalize := false) -> SeqEnum, SeqEnum
	{Compute the invariants of a univariate homogeneous polynomial of degree smaller than 10.}

	require Degree(f) le 10: "f must be of degree smaller than 10";

	C<x,y> := PolynomialRing(BaseRing(Parent(f)), 2);
	F := C!(x^10*Evaluate(f, y/x));

	Inv, Wgt := InvariantsGenus4Curves(F : normalize := normalize);

	return Inv, Wgt;
end intrinsic;


intrinsic InvariantsGenus4Curves(C::CrvHyp : normalize := false) -> SeqEnum, SeqEnum
	{Given a hyperelliptic curve of genus 4, return its invariants.}

	require Genus(C) eq 4: "Curve must be of genus 4.";

        K := BaseField(C);
        R := PolynomialRing(K); x := R.1;
        f0, h0 := HyperellipticPolynomials(C);

	require (Degree(h0) le 5) and (Degree(f0) le 10): "The polynomials h and f must have degree at most 5 and 10, respectively.";

	f := (h0/2)^2+f0;

	Inv, Wgt := InvariantsGenus4Curves(f : normalize := normalize);

	return Inv, Wgt;
end intrinsic;

intrinsic IsIsomorphicG4(C1::Crv, C2::Crv : K := BaseRing(CoordinateRing(C1))) -> bool
	{Given two curves of genus 4, check if they are isomorphic over K.}

	I1, wgt := InvariantsGenus4Curves(C1);
	I2 := InvariantsGenus4Curves(C2);

	t := &and[IsCoercible(K, i) : i in I1 cat I2];

	require t : "Not comparable in the ring K.";

	if #I1 eq #I2 then
		if WPSEqual(wgt, ChangeUniverse(I1, K), ChangeUniverse(I2, K)) then
			return true;
		end if;
	end if;
	vprint Genus4 : "Curves are not of the same type (different rank of quadric or hyperelliptic).";
	return false;
end intrinsic;

intrinsic IsIsomorphicG4(Q1::RngMPolElt, E1::RngMPolElt, Q2::RngMPolElt, E2::RngMPolElt : K := BaseRing(Parent(Q1))) -> bool
	{Given two curves of genus 4 as the intersection of a quadric and a cubic in P^3, return if they are isomorphic over K.}

        I1, wgt := InvariantsGenus4Curves(Q1, E1);
        I2 := InvariantsGenus4Curves(Q2, E2);

        t := &and[IsCoercible(K, i) : i in I1 cat I2];

        require t : "Not comparable in the ring K.";

        if #I1 eq #I2 then
                if WPSEqual(wgt, ChangeUniverse(I1, K), ChangeUniverse(I2, K)) then
                        return true;
                end if;
        end if;
        vprint Genus4 : "Curves are not of the same type (different rank of quadric or hyperelliptic).";
        return false;
end intrinsic;

import "decomposition_disc_rk4.m" : DiscriminantRk4;
import "decomposition_disc_rk3.m" : DiscriminantRk3;

intrinsic DiscriminantFromInvariantsGenus4(I::SeqEnum) -> RngInt
	{Given a list of invariants of a non-hyperelliptic genus 4 curve, return its discriminant.}
	if #I eq 60 then 
		return DiscriminantRk3(I);
	elif #I eq 65 then
		return DiscriminantRk4(I);
	else	
		"Not coded for hyperelliptic curves";
	end if;
	return 0;
end intrinsic;


intrinsic Normalize(invs::SeqEnum, wgt::SeqEnum) -> SeqEnum
	{Normalize invariants}
    prec := Precision(Parent(invs[1]));
    _, i0 := Max([Abs(invs[i]^(1/wgt[i])) : i in [1..#invs]]);
    invs0 := WPSMultiply(wgt, invs, invs[i0]^(-1/wgt[i0]));

    invs1 := invs;
    for i in [1..#invs0] do
        if Abs(invs0[i]) le 10^(-prec/3) then
            invs1[i] := 0;
        end if;
    end for;

    i0 := Min([i : i in [1..#invs1] | invs1[i] ne 0]);
    invs_norm := ChangeUniverse(WPSNormalize(wgt, WPSMultiply(wgt, invs1, invs1[i0]^(-1/wgt[i0]))), ComplexFieldExtra(Floor(prec/3)));
    return invs_norm;
end intrinsic;
