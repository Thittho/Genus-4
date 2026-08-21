/*
 *  Genus 4 curves
 *
 *  Thomas Bouchet
 *
 *  See LICENSE.txt for license details.
*/

declare verbose Reconstruction, 1;

function ReconstructionGenus4Rank4(I)
	R<X,Y,Z,T> := PolynomialRing(Parent(I[1]), 4);
	
	c3c3 := I[11];
	c3c51 := I[12];
	c3c52 := I[13];
	c3c53 := -772/9*I[6]-772/27*I[1]*I[4]+965/96*I[1]^4+193/96*I[3]^2+193/72*I[2]*I[3]-193/16*I[1]^2*I[3]-193/72*I[1]^2*I[2]+416/9*I[1]*I[11]+1955/3*I[12]-512/27*I[13];
	c51c51 := I[14];
	c51c52 := I[15];
	c51c53 := I[16];
	c52c52 := I[17];
	c52c53 := I[18];
	c53c53 := I[19];

	M_3_51_52_53 := Matrix(Parent(I[1]), [[c3c3, c3c51, c3c52, c3c53], [c3c51, c51c51, c51c52, c51c53], [c3c52, c51c52, c52c52, c52c53], [c3c53, c51c53, c52c53, c53c53]]);

	if Determinant(M_3_51_52_53) ne 0 then
		vprint Reconstruction : "Found working set of covariants (1), computing model...";
		fc3c3c3 := I[8];
		fc3c3c51 := I[26];
		fc3c3c52 := I[27];
		fc3c3c53 := I[28];
		fc3c51c51 := I[34];
		fc3c51c52 := I[35];
		fc3c51c53 := I[36];
		fc3c52c52 := I[37];
		fc3c52c53 := I[38];
		fc3c53c53 := I[39];
		fc51c51c51 := I[45];
		fc51c51c52 := I[46];
		fc51c51c53 := I[47];
		fc51c52c52 := I[48];
		fc51c52c53 := I[49];
		fc51c53c53 := I[50];
		fc52c52c52 := I[51];
		fc52c52c53 := I[52];
		fc52c53c53 := I[53];
		fc53c53c53 := I[54];
		
		Q := c3c3*X^2+2*c3c51*X*Y+2*c3c52*X*Z+2*c3c53*X*T+c51c51*Y^2+2*c51c52*Y*Z+2*c51c53*Y*T+c52c52*Z^2+2*c52c53*Z*T+c53c53*T^2;
		E := fc3c3c3*X^3+3*fc3c3c51*X^2*Y+3*fc3c3c52*X^2*Z+3*fc3c3c53*X^2*T+3*fc3c51c51*X*Y^2+6*fc3c51c52*X*Y*Z+6*fc3c51c53*X*Y*T+3*fc3c52c52*X*Z^2+6*fc3c52c53*X*Z*T+3*fc3c53c53*X*T^2+fc51c51c51*Y^3+3*fc51c51c52*Y^2*Z+3*fc51c51c53*Y^2*T+3*fc51c52c52*Y*Z^2+6*fc51c52c53*Y*Z*T+3*fc51c53c53*Y*T^2+fc52c52c52*Z^3+3*fc52c52c53*Z^2*T+3*fc52c53c53*Z*T^2+fc53c53c53*T^3; 

		return Q, E;
	end if;
	vprint Reconstruction : "No basis of covariants found.";
    error("Not implemented in that case yet.");
end function;

function ReconstructionGenus4Rank3(I)
    a11 := I[3];
	a12 := 1/3*(-1/3*I[1]^2*I[2] + I[1]*I[3] + 2*I[2]^2);
    a13 := 1/54*I[1]^3*I[2] - 1/18*I[1]^2*I[3] - 1/9*I[1]*I[2]^2 + 1/3*I[2]*I[3] + 1/2*I[4];
    a22 := 1/54*I[1]^3*I[2] - 1/18*I[1]^2*I[3] - 1/9*I[1]*I[2]^2 + 1/3*I[2]*I[3] + 1/2*I[4];
    a23 := 1/3*(-1/6*I[1]^2*I[2]^2 + 1/3*I[1]*I[2]*I[3] + I[2]^3 + 1/2*I[3]^2);
    a33 := 1/2*(5/162*I[1]^3*I[2]^2 - 7/54*I[1]^2*I[2]*I[3] - 5/27*I[1]*I[2]^3 + 1/9*I[1]*I[3]^2 + 5/9*I[2]^2*I[3] + 1/2*I[2]*I[4]);

	if Determinant(Matrix([[a11,a12,a13],[a12,a22,a23],[a13,a23,a33]])) ne 0 then
		vprint Reconstruction : "Found working set of covariants (1), computing model...";
	    v11 := I[24];
	    v12 := I[43];
    	v13 := -1/18*I[1]^2*I[2]*I[8] + 1/12*I[1]*I[3]*I[8] + 1/3*I[2]^2*I[8] + 1/4*I[2]*I[24] + 1/4*I[3]*I[13] - 1/2*I[54];
    	v22 := I[54];
	    v23 := 1/54*I[1]^3*I[2]*I[8] - 1/36*I[1]^2*I[2]*I[13] - 1/18*I[1]^2*I[3]*I[8] -
    		1/9*I[1]*I[2]^2*I[8] + 1/36*I[1]*I[2]*I[24] + 1/12*I[1]*I[3]*I[13] +
    		1/6*I[2]^2*I[13] + 1/6*I[2]*I[3]*I[8] - 1/12*I[3]*I[24] + 1/4*I[4]*I[8];
	    v33 := -1/324*I[1]^4*I[2]*I[8] + 1/108*I[1]^3*I[2]*I[13] + 1/108*I[1]^3*I[3]*I[8] -
    		1/27*I[1]^2*I[2]^2*I[8] - 1/36*I[1]^2*I[3]*I[13] - 1/18*I[1]*I[2]^2*I[13] +
    		1/18*I[1]*I[2]*I[3]*I[8] + 1/9*I[1]*I[2]*I[43] - 1/12*I[1]*I[4]*I[8] +
    		1/3*I[2]^3*I[8] + 1/6*I[2]*I[3]*I[13] - 1/2*I[2]*I[54] + 1/6*I[3]^2*I[8] -
    		1/3*I[3]*I[43] + 1/4*I[4]*I[13];

	    f111 := I[4];
	    f112 := 1/3*(1/54*I[1]^4*I[2] - 1/18*I[1]^3*I[3] - 2/9*I[1]^2*I[2]^2 + 1/3*I[1]*I[2]*I[3] + 1/2*I[1]*I[4] + 2/3*I[2]^3 + I[3]^2);
    	f113 := 1/3*(-1/6*I[1]^2*I[2]*I[3] + 1/2*I[1]*I[3]^2 + I[2]^2*I[3] + 1/2*I[2]*I[4]);
    	f122 := 1/3*(-1/6*I[1]^2*I[2]*I[3] + 1/2*I[1]*I[3]^2 + I[2]^2*I[3] + 1/2*I[2]*I[4]);
	    f123 := 1/3*(1/108*I[1]^4*I[2]^2 - 1/36*I[1]^3*I[2]*I[3] - 1/9*I[1]^2*I[2]^3 + 1/6*I[1]*I[2]^2*I[3] + 1/12*I[1]*I[2]*I[4] +
    		1/3*I[2]^4 + 1/2*I[2]*I[3]^2 + 1/2*I[3]*I[4]);
    	f133 := 1/3*(-1/972*I[1]^5*I[2]^2 + 1/162*I[1]^4*I[2]*I[3] + 1/81*I[1]^3*I[2]^3 - 1/108*I[1]^3*I[3]^2 - 5/36*I[1]^2*I[2]^2*I[3]
	        - 1/36*I[1]^2*I[2]*I[4] - 1/27*I[1]*I[2]^4 + 1/4*I[1]*I[2]*I[3]^2 + 1/12*I[1]*I[3]*I[4] + 11/18*I[2]^3*I[3] +
    		1/4*I[2]^2*I[4] + 1/6*I[3]^3);
    	f222 := 1/3*(1/36*I[1]^4*I[2]^2 - 1/6*I[1]^3*I[2]*I[3] - 1/3*I[1]^2*I[2]^3 + 1/4*I[1]^2*I[3]^2 + I[1]*I[2]^2*I[3] +
	        1/12*I[1]*I[2]*I[4] + I[2]^4 - 1/4*I[3]*I[4]);
        f223 := -1/729*I[1]^5*I[2]^2 + 2/243*I[1]^4*I[2]*I[3] + 4/243*I[1]^3*I[2]^3 - 1/81*I[1]^3*I[3]^2 - 2/27*I[1]^2*I[2]^2*I[3]
    		- 1/27*I[1]^2*I[2]*I[4] - 4/81*I[1]*I[2]^4 + 1/12*I[1]*I[2]*I[3]^2 + 1/9*I[1]*I[3]*I[4] + 4/27*I[2]^3*I[3] +
    		1/4*I[2]^2*I[4] - 1/36*I[3]^3;
    	f233 := 1/5832*I[1]^6*I[2]^2 - 1/972*I[1]^5*I[2]*I[3] - 1/1944*I[1]^4*I[2]^3 + 1/648*I[1]^4*I[3]^2 +
	    	1/324*I[1]^3*I[2]^2*I[3] + 1/108*I[1]^3*I[2]*I[4] - 1/81*I[1]^2*I[2]^4 - 1/216*I[1]^2*I[2]*I[3]^2 -
    		1/36*I[1]^2*I[3]*I[4] + 1/54*I[1]*I[2]^3*I[3] - 11/216*I[1]*I[2]^2*I[4] + 1/18*I[2]^5 + 1/18*I[2]^2*I[3]^2 +
    		11/72*I[2]*I[3]*I[4] + 1/8*I[4]^2;
    	f333 := -1/1944*I[1]^5*I[2]^3 + 1/648*I[1]^4*I[2]^2*I[3] + 1/162*I[1]^3*I[2]^4 + 1/216*I[1]^3*I[2]*I[3]^2 -
	    	1/54*I[1]^2*I[2]^3*I[3] - 13/648*I[1]^2*I[2]^2*I[4] - 1/72*I[1]^2*I[3]^3 - 1/54*I[1]*I[2]^5 -
    		1/72*I[1]*I[2]^2*I[3]^2 + 1/27*I[1]*I[2]*I[3]*I[4] + 1/18*I[2]^4*I[3] + 1/8*I[2]^3*I[4] + 1/24*I[2]*I[3]^3 +
    		5/72*I[3]^2*I[4];		
	else
		a11 := 1/5*I[1]*I[6] + I[9] + 12/7*I[10];
		a12 := I[13];
		a13 := -I[12];
		a22 := I[3];
		a23 := -I[21];
		a33 := 1/2*(-1/2*I[1]*I[10] + 1/2*I[2]*I[6] - I[8]^2 + 3/2*I[22]);

		if Determinant(Matrix([[a11,a12,a13],[a12,a22,a23],[a13,a23,a33]])) ne 0 then
			vprint Reconstruction : "Found working set of covariants (2), computing model...";
			v11 := 2/35*I[1]*I[7] + 1/7*I[6]*I[8] + 16/11*I[14] + I[15];
			v12 := 2/7*I[22] + I[23];
			v13 := I[16] - 3/2*I[19];
			v22 := I[24];
			v23 := I[25];
			v33 := 1/2*(1/12*I[1]*I[6]*I[8] - 1/2*I[2]*I[7] - 1/4*I[6]*I[13] + I[8]*I[10]);

			f111 := 2/35*I[1]^2*I[7] - 23/1155*I[1]*I[6]*I[8] + 6/11*I[1]*I[14] +
				2/9*I[1]*I[15] - 16/77*I[2]*I[7] + 6/11*I[6]*I[13] - 1/2*I[8]*I[9] -
				52/77*I[8]*I[10] + 5/3*I[27] + 14/11*I[29] - 2*I[30];
			f112 := 1/7*I[1]^2*I[10] - 1/30*I[1]*I[2]*I[6] + 1/6*I[1]*I[8]^2 - 1/7*I[1]*I[22]
				+ 2/9*I[1]*I[23] - I[2]*I[9] - 4/7*I[2]*I[10] + 1/5*I[3]*I[6] + 8/3*I[35] +
				6/7*I[36];
			f113 := 1/2*I[1]*I[16] - 2/3*I[1]*I[19] - 1/12*I[2]*I[11] - 3/14*I[6]*I[21] +
				1/2*I[8]*I[12] + 5/4*I[33] - 3/2*I[41];
			f122 := -1/54*I[1]^3*I[8] + 1/18*I[1]^2*I[13] + 1/9*I[1]*I[2]*I[8] +
				1/6*I[1]*I[24] - 1/3*I[2]*I[13] - 1/3*I[3]*I[8] + 2*I[43];
			f123 := -1/18*I[1]^2*I[12] + 10/21*I[1]*I[25] + 1/6*I[1]*I[26] + 1/3*I[2]*I[12] +
				1/3*I[8]*I[21] - I[42];
			f133 := -19/6160*I[1]^2*I[6]*I[8] - 27/220*I[1]*I[2]*I[7] +
				57/6160*I[1]*I[6]*I[13] - 1/8*I[1]*I[8]*I[9] + 123/308*I[1]*I[8]*I[10] -
				3/308*I[2]*I[6]*I[8] + 3/44*I[2]*I[14] + 5/24*I[2]*I[15] + 24/77*I[3]*I[7] -
				3/112*I[6]*I[24] + 3/8*I[8]^3 - 295/308*I[8]*I[22] - 1/4*I[8]*I[23] +
				3/8*I[9]*I[13] - 38/77*I[10]*I[13] + 6/11*I[44] - 5/4*I[48];
			f222 := I[4];
			f223 := -1/12*I[1]^2*I[21] + 1/4*I[1]*I[37] + 1/2*I[2]*I[21] - I[50];
			f233 := 1/72*I[1]^2*I[2]*I[6] - 1/18*I[1]^2*I[8]^2 - 1/24*I[1]*I[3]*I[6] + 1/4*I[1]*I[8]*I[13] - 1/12*I[2]^2*I[6] +
				1/3*I[2]*I[8]^2 - 3/4*I[2]*I[22] + 1/2*I[3]*I[10] - 1/4*I[13]^2;
			f333 := 1/2*(1/6*I[1]*I[2]*I[11] + 1/24*I[1]*I[6]*I[21] - 1/2*I[1]*I[8]*I[12] + 3/2*I[2]*I[16] + 5/4*I[2]*I[19] -
				1/2*I[3]*I[11] - 1/8*I[6]*I[37] - 9/14*I[8]*I[25] + I[8]*I[26] - 1/2*I[10]*I[21] + 1/2*I[12]*I[13]);
		else
			vprint Reconstruction : "No basis of covariants found.";
			error("Not implemented in that case yet.");
	    end if;
    end if;

    _<X,Y,Z,T> := PolynomialRing(Parent(I[1]), 4);
    Q := a11*X^2+2*a12*X*Y+2*a13*X*Z+a22*Y^2+2*a23*Y*Z+a33*Z^2;
    V := v11*X^2+2*v12*X*Y+2*v13*X*Z+v22*Y^2+2*v23*Y*Z+v33*Z^2;
    F := f111*X^3+3*f112*X^2*Y+3*f113*X^2*Z+3*f122*X*Y^2+6*f123*X*Y*Z+3*f133*X*Z^2+f222*Y^3+3*f223*Y^2*Z+3*f233*Y*Z^2+f333*Z^3;

    E := T^3+T*V+F;

    return Q, E;
end function;


import "rec_hyp_g4.m" : a11,a12,a13,a22,a23,a33,f11111,f11112,f11113,f11122,f11123,f11133,f11222,f11223,f11233,f11333,f12222,f12223,f12233,f12333,f13333,f22222,f22223,f22233,f22333,f23333,f33333;

intrinsic HyperellipticCurveFromBrouwerPopoviciuInvariants(I::SeqEnum : 
    minimize := true) -> RngMPolElt

	{
        Given a generic tuple of invariants for hyperelliptic curves of genus 4, returns a homogeneous degree 10 polynomial f(x,z)
        such that y^2 = f(x) is a genus 4 curve with said invariants (up to scaling). 
        If minimize is set to true, the returned binary form f is transformed so as to have smaller coefficients.
    }

    inv := [I[ind] : ind in [ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 17, 18, 19, 20, 21, 22, 23, 24, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 92, 93, 94, 95, 96, 102 ]];

    M := Matrix([[a11(inv), a12(inv), a13(inv)],
                 [a12(inv), a22(inv), a23(inv)],
                 [a13(inv), a23(inv), a33(inv)]]);

    if Rank(M) ne 3 then
        vprint Reconstruction : "The covariants chosen for the reconstruction do not form a basis.";
        error("Not implemented in that case yet.");
    end if;

    
    R0<X,Y,Z> := PolynomialRing(FieldOfFractions(Universe(inv)), 3);
    
    Q := (Matrix([[X,Y,Z]])*ChangeRing(M, R0)*Transpose(Matrix([[X,Y,Z]])))[1][1];

    Con := Conic(Proj(Parent(Q)), Q);
    param := Parametrization(Con);

    E := f11111(inv)*X^5+
        5*f11112(inv)*X^4*Y+
        5*f11113(inv)*X^4*Z+
        10*f11122(inv)*X^3*Y^2+
        20*f11123(inv)*X^3*Y*Z+
        10*f11133(inv)*X^3*Z^2+
        10*f11222(inv)*X^2*Y^3+
        30*f11223(inv)*X^2*Y^2*Z+
        30*f11233(inv)*X^2*Y*Z^2+
        10*f11333(inv)*X^2*Z^3+
        5*f12222(inv)*X*Y^4+
        20*f12223(inv)*X*Y^3*Z+
        30*f12233(inv)*X*Y^2*Z^2+
        20*f12333(inv)*X*Y*Z^3+
        5*f13333(inv)*X*Z^4+
        f22222(inv)*Y^5+
        5*f22223(inv)*Y^4*Z+
        10*f22233(inv)*Y^3*Z^2+
        10*f22333(inv)*Y^2*Z^3+
        5*f23333(inv)*Y*Z^4+
        f33333(inv)*Z^5;
    
    f := E @@ param;

    if minimize and Type(Universe(I)) eq FldRat then
        vprint Reconstruction : "Minimizing model...";
        f := MinRedBinaryForm(f);
    end if;
    return f;

end intrinsic;

intrinsic Genus4FromInvariants(I::SeqEnum : minimize := true) -> RngMPolElt, RngMPolElt
    {
        Given a generic tuple of invariants for curves of genus 4, returns either:
		- a degree 2 polynomial Q and a degree 3 polynomial E in 4 variables such that V(Q,E) is a non-hyp genus 4 curve with said invariants (up to scaling). Both cases (rank 3 and 4) are covered. 
		- a homogeneous degree 10 polynomial f(x,z) such that y^2 = f(x) is a genus 4 curve with said invariants (up to scaling). 
		If minimize is set to true, the returned polynomial(s) is transformed so as to have smaller coefficients.
    }
    
	if #I eq 60 then
		vprint Reconstruction : "The canonical model of the curve lies on a quadric of rank 3";
		Q, E := ReconstructionGenus4Rank3(I : minimize := minimize);
        if minimize and Type(Universe(I)) eq FldRat then
            vprint Reconstruction : "Minimizing model...";
            Q, E := MinimizeGenus4(Q, E);
        end if;
		return Q, E;
	elif #I eq 65 then 
		vprint Reconstruction : "The canonical model of the curve lies on a quadric of rank 4";
		Q, E := ReconstructionGenus4Rank4(I : minimize := minimize);
        if minimize and Type(Universe(I)) eq FldRat then
            vprint Reconstruction : "Minimizing model...";
            Q, E := MinimizeGenus4(Q, E);
        end if;
		return Q, E;
	elif #I eq 106 then 
		return HyperellipticCurveFromBrouwerPopoviciuInvariants(I : minimize := minimize);
	else 
		error("Number of invariants is not right.");
    end if;
end intrinsic;


