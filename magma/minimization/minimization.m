/* 
* Developped with Andreas Pieper (https://andreas-pieper.github.io/)
*/

//
// Some technical functions for the normalization in the rank 3 case
//

function Transfo(lin)
    R := Parent(lin);
    K := BaseRing(R);
    n := Rank(R);
    perm := [1..n];
    basis := [MonomialCoefficient(lin, R.i) : i in [1..n]];
    for i in [0..n-1] do
        if basis[n-i] ne 0 then
            perm[n] := n-i;
            perm[n-i] := n;
            temp := basis[n];
            basis[n] := basis[n-i];
            basis[n-i] := temp;
            break;
        end if;
    end for;
    return PermutationMatrix(K, perm)*Matrix(K, [[i eq j select 1 else 0 : j in [1..n]] : i in [1..n-1]] cat [[-basis[i]/basis[n] : i in [1..n-1]] cat [1/basis[n]]]);
end function;

function ApplyTransfo(T, Q, E, l, lin)
    return Q^T, E^T, l^T, lin^Transpose(T^(-1));
end function;

//
// Normalization functions
//

function NormalizeRk4(Q, E)
    alpha := TransvectantGeneral([Q, Q, Q, Q], 2);
    
    beta := 2/3*TransvectantGeneral([Q, Q, Q, E], 2);

    cub := alpha*E-beta*Q;
    return cub;
end function;

function NormalizeRk3(Q, E)
    R<x,y,z,w> := Parent(Q);
    K := BaseRing(R);

    l := TransvectantGeneral([Q, Q, Q, E], 2);
    basis := Eltseq(Basis(Kernel(Matrix([[Derivative(Derivative(Q, i), j) : i in [1..4]] : j in [1..4]])))[1]);
    lin := &+[R.i*basis[i] : i in [1..#basis]];

    T := Transpose(Transfo(lin)^(-1));

    Q_t, E_t, l_t, lin_t := ApplyTransfo(T, Q, E, l, lin);
    
    T_t := Transfo(l_t);

    Q_tt, E_tt, l_tt, lin_tt := ApplyTransfo(T_t, Q_t, E_t, l_t, lin_t);
    
    E_tt /:= MonomialCoefficient(E_tt, w^3);
    // only action is GL3 now

    S<X,Y,Z> := PolynomialRing(K, 3);
    Q_new := Evaluate(Q_tt, [X, Y, Z, 0]);
    f2_new := Evaluate(Terms(E_tt, w)[2] div w, [X, Y, Z, 0]);
    f3_new := Evaluate(Terms(E_tt, w)[1], [X, Y, Z, 0]);
    
    inv_Q := K!TransvectantGeneral([Q_new, Q_new, Q_new], 2);
    
    f2_inv := inv_Q*(f2_new)-TransvectantGeneral([Q_new, Q_new, f2_new], 2)*Q_new;
    
    f3_inv := inv_Q*(f3_new)-3/5*TransvectantGeneral([Q_new, Q_new, f3_new], 2)*Q_new;

    Q_new := Evaluate(Q_new, [x, y, z]);

    E_new := inv_Q*w^3 + w*Evaluate(f2_inv, [x, y, z]) + Evaluate(f3_inv, [x, y, z]);

    return Q_new, E_new, T*T_t;
end function;

//
// minimization functions
//

function MinimizeReduceQuadric(Q0)
	R := Parent(Q0);
	Q := QuadraticFormToMatrix(Q0);
	Q *:= LCM([Denominator(q): q in Eltseq(Q)])/GCD([Numerator(e) : e in Eltseq(Q)]);
	Q := ChangeRing(Q, Integers());
	if Rank(Q) eq 4 then
		det := Determinant(Q);
	elif Rank(Q) eq 3 then // assuming that it has been put in only the first 3 variables
		Q := Submatrix(Q, [1..3], [1..3]);
		det := Determinant(Q);
	else
		error("Q is not irreducible");
	end if;
	g := Nrows(Q);
	S := IdentityMatrix(Rationals(), g);
	vprint Genus4 : "Factorization of discriminant";
	_, sq := SquarefreeFactorization(det);
	numbers := [];
	while sq gt 1 do
		nsq, sq := SquarefreeFactorization(sq);
		Append(~numbers, nsq);
	end while;
	fac := [Factorization(nb) : nb in numbers];
	fac := &cat[[f[1] : f in fact] : fact in fac];
	primes := [<p, Valuation(det, p)> : p in Sort(Setseq(Set(fac)))];
	for pri in primes do
		vprint Genus4 : "Minimization at ", pri[1];
		p := pri[1];
		ei := pri[2];
		while ei gt 1 do
			Qred := ChangeRing(Q, GF(p));
			ker := KernelMatrix(Qred);
			nro := Nrows(ker);
			if nro ge ei then
				continue pri;
			end if;
			kerZ := ChangeRing(ker, Integers());
			D, U, V := SmithForm(kerZ);
			SNF := V^-1;
			S := SNF * S;
			Q := SNF * Q * Transpose(SNF);
			j := [i: i in [1..nro]| Valuation(Q[i,i],p) gt 1];
			if j ne [] then
				j := j[1];
			else
				Qsub := Submatrix(Q, 1, 1, nro, nro) div p;
				Qsub := ChangeRing(Qsub, GF(p));
				kersub := KernelMatrix(Qsub);
				kersubZ := ChangeRing(kersub, Integers());
				D, U, V := SmithForm(kersubZ);
				SNF := V^-1;
				Stra := Matrix(BlockDiagMat(<SNF, IdentityMatrix(Integers(), g-nro)>));
				S := Stra * S;
				Q := Stra * Q * Transpose(Stra);
				j := 1;
			end if;
			Dia := DiagonalMatrix([1: i in [1..j-1]] cat [1/p] cat [1: i in [1..g-j]]);
			S := Dia * S;
			Q := Dia * ChangeRing(Q, Rationals()) * Dia;
			Q := ChangeRing(Q, Integers());
			ei -:= 2;
		end while;
	end for;
	vprint Genus4 : "Doing LLL";
	_, S1 := LLLGram(Q);
	Q := S1 * Q * Transpose(S1);
	Q1 := &+[Q[i,j]*R.i*R.j : i,j in [1..g]];
	if g eq 3 then
		return Q1, DiagonalJoin(S1*S, IdentityMatrix(Rationals(), 1));
	end if;
	return Q1, S1*S;
end function;

intrinsic MinimizeGenus4OneStep(Q::RngMPolElt, Gamma::RngMPolElt) -> RngMPolElt, RngMPolElt
{Given a non-hyperelliptic genus 4 curve given as the locus of a homogeneous quadratic form Q and a homogeneous cubic form Gamma in 4 variables over Q or Z, returns a model with smaller coefficients}
	P3 := ProjectiveSpace(Rationals(), 3);
	R4<X,Y,Z,T> := CoordinateRing(P3);
	Q := R4!Q;
	Gamma := R4!Gamma;	
	rk := Rank(QuadraticFormToMatrix(Q));
	vprint Genus4 : "Normalization";
	if rk eq 3 then
		Q1, Gamma1, S := NormalizeRk3(Q, Gamma);
	elif rk eq 4 then
		Gamma1 := Gamma;
		Q1 := Q;
		S := IdentityMatrix(Rationals(), 4);
	else 
		error("Q is not irreducible");
	end if;
	
	vprint Genus4 : "Minimizing Q...";
	Q1, S_Q := MinimizeReduceQuadric(Q1);
    Q1 *:= LCM([Denominator(q): q in Coefficients(Q1)])/GCD([Numerator(q): q in Coefficients(Q1)]);
    Gamma1 := Gamma1^Transpose(S_Q);
	Gamma1 *:= LCM([Denominator(q): q in Coefficients(Gamma1)])/GCD([Numerator(q): q in Coefficients(Gamma1)]);
	vprint Genus4 : "Computing invariants of Gamma...";
	inv := Integers()!DiscriminantGenus4(Q1, Gamma1);
	vprint Genus4 : "Factorization...";
	_, sq := SquarefreeFactorization(inv);
	numbers := [];
	while sq gt 1 do
		nsq, sq := SquarefreeFactorization(sq);
		Append(~numbers, nsq);
	end while;
	fac := [Factorization(nb) : nb in numbers];
	fac := &cat[[f[1] : f in fact] : fact in fac];
	l_p := Sort(Setseq(Set(fac)));
	S_M := IdentityMatrix(Rationals(), 4);
	for p in l_p do
		vprint Genus4 : "Minimization at ", p;
		Gamma1, S_Mp := MinimizeCubicSurface(Gamma1, p);
		S_M := S_M * S_Mp;
	end for;
	Q1 := Q1^S_M;	
	Q1 := R4!Q1;
	Gamma1 := R4!Gamma1;
	if rk eq 4 then
		H := TransvectantGeneral([Q1, Q1, Gamma1, Gamma1], 2);
		
		// Reduction of Q and C using the covariant H
		vprint Genus4 : "Reducing cluster...";
		Clust := Cluster(P3, [Q1, H, Gamma1]);
		_, S_red := ReduceCluster(Clust : eps := 10^-30);

		Q1 := Q1^ChangeRing(S_red, Rationals());
		Gamma1 := Gamma1^ChangeRing(S_red, Rationals());
		S_norm := IdentityMatrix(Rationals(), 4);
	else 
		P2 := ProjectiveSpace(Rationals(), 2);
		R3 := CoordinateRing(P2);
		Q1, Gamma1, S_norm := NormalizeRk3(Q1, Gamma1);

		// Reduction of Q and C using the covariant H
		vprint Genus4 : "Reducing cluster...";
		Q_new := Evaluate(Q1, [R3.1, R3.2, R3.3, 0]);
		Gamma_new := Evaluate(Gamma1, [R3.1, R3.2, R3.3, 0]);
		Clust := Cluster(P2, [Gamma_new, TransvectantGeneral([Gamma_new, Gamma_new, Gamma_new], 2)]);
		_, S_red := ReduceCluster(Clust : eps := 10^-100);

		S_red := DiagonalJoin(ChangeRing(S_red, Rationals()), IdentityMatrix(Rationals(), 1));
		Q1 := Q1^S_red;
		Gamma1 := Gamma1^S_red;
	end if;

	Q1 /:= GCD([Numerator(c) : c in Coefficients(Q1)]);
	Gamma1 /:= GCD([Numerator(c) : c in Coefficients(Gamma1)]);

	mons3 := MonomialsOfDegree(R4, 3);
	LMat := Matrix([[MonomialCoefficient(pos, m): m in mons3] : pos in [Gamma1] cat [Q1*R4.i: i in [1..4]]]);
	A, B := LLL(LMat);
	j := Max([j : j in [1..5] | B[j][1] ne 0]);
	vecopt := [A[j][i] : i in [1..20]];	

	Gamma1 := &+[vecopt[i]*mons3[i] : i in [1..20]];
	Gamma1 /:= GCD([Numerator(c) : c in Coefficients(Gamma1)]);
	return Q1, Gamma1, S*Transpose(S_Q)*S_M*S_norm*S_red, inv;
end intrinsic;


intrinsic MinimizeGenus4(Q::RngMPolElt, Gamma::RngMPolElt) -> RngMPolElt, RngMPolElt
{Given a non-hyperelliptic genus 4 curve given as the locus of a homogeneous quadratic form Q and a homogeneous cubic form Gamma in 4 variables over Q or Z, returns a model with smaller coefficients}
	count := 0;
	count_error := 0;
	Q_min, Gamma_min, S, inv := MinimizeGenus4OneStep(Q, Gamma);
	while count lt 3 and count_error lt 3 do
		try 
			Q_min, Gamma_min, S1, inv1 := MinimizeGenus4OneStep(Q_min, Gamma_min);
			S := S*S1;
			if inv1 ge inv then 
				count +:= 1;
			else 
				inv := inv1;
				count := 0;
			end if;
			count_error := 0;
		catch e 
			count_error +:= 1;
		end try;
	end while;
	return Q_min, Gamma_min, S;
end intrinsic;