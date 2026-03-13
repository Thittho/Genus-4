/*
 *  Genus 4 curves
 *
 *  Thomas Bouchet
 *
 *  See LICENSE.txt for license details.
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

function NormalizeRk4(Q, E, Q1, E1)
    alpha := TransvectantGeneral([Q, Q, Q, Q], 2);
    alpha1 := TransvectantGeneral([Q1, Q1, Q1, Q1], 2);
    
    beta := 2/3*TransvectantGeneral([Q, Q, Q, E], 2);
    beta1 := 2/3*TransvectantGeneral([Q1, Q1, Q1, E1], 2);

    cub := alpha*E-beta*Q;
    cub1 := alpha1*E1-beta1*Q1;
    return cub, cub1;
end function;

function NormalizeRk3(Q, E, Q1, E1)
    R<x,y,z,w> := Parent(Q);
    K := BaseRing(R);

    E, Q1, E1 := Explode([R!E, R!Q1, R!E1]);

    l := TransvectantGeneral([Q, Q, Q, E], 2);
    l1 := TransvectantGeneral([Q1, Q1, Q1, E1], 2);

    basis := Eltseq(Basis(Kernel(Matrix([[K!Derivative(Derivative(Q, i), j) : i in [1..4]] : j in [1..4]])))[1]);
    lin := &+[R.i*basis[i] : i in [1..#basis]];

    basis1 := Eltseq(Basis(Kernel(Matrix([[K!Derivative(Derivative(Q1, i), j) : i in [1..4]] : j in [1..4]])))[1]);
    lin1 := &+[R.i*basis1[i] : i in [1..#basis1]];
    
    T := Transpose(Transfo(lin)^(-1));
    T1 := Transpose(Transfo(lin1)^(-1));


    Q_t, E_t, l_t, lin_t := ApplyTransfo(T, Q, E, l, lin);
    Q1_t, E1_t, l1_t, lin1_t := ApplyTransfo(T1, Q1, E1, l1, lin1);
    
    T_t := Transfo(l_t);
    T1_t := Transfo(l1_t);

    Q_tt, E_tt, l_tt, lin_tt := ApplyTransfo(T_t, Q_t, E_t, l_t, lin_t);
    Q1_tt, E1_tt, l1_tt, lin1_tt := ApplyTransfo(T1_t, Q1_t, E1_t, l1_t, lin1_t);
    
    E_tt /:= MonomialCoefficient(E_tt, w^3);
    E1_tt /:= MonomialCoefficient(E1_tt, w^3);
    // only action is GL3 now

    S<X,Y,Z> := PolynomialRing(K, 3);
    Q_new := Evaluate(Q_tt, [X, Y, Z, 0]);
    f2_new := Evaluate(Terms(E_tt, w)[2] div w, [X, Y, Z, 0]);
    f3_new := Evaluate(Terms(E_tt, w)[1], [X, Y, Z, 0]);
    
    Q1_new := Evaluate(Q1_tt, [X, Y, Z, 0]);
    f2_1_new := Evaluate(Terms(E1_tt, w)[2] div w, [X, Y, Z, 0]);
    f3_1_new := Evaluate(Terms(E1_tt, w)[1], [X, Y, Z, 0]);

    inv_Q := K!TransvectantGeneral([Q_new, Q_new, Q_new], 2);
    inv_Q1 := K!TransvectantGeneral([Q1_new, Q1_new, Q1_new], 2);
    
    f2_inv := inv_Q*(f2_new)-TransvectantGeneral([Q_new, Q_new, f2_new], 2)*Q_new;
    f2_1_inv := inv_Q1*(f2_1_new)-TransvectantGeneral([Q1_new, Q1_new, f2_1_new], 2)*Q1_new;
    
    f3_inv := inv_Q*(f3_new)-3/5*TransvectantGeneral([Q_new, Q_new, f3_new], 2)*Q_new;
    f3_1_inv := inv_Q1*(f3_1_new)-3/5*TransvectantGeneral([Q1_new, Q1_new, f3_1_new], 2)*Q1_new;

    Q_new := Evaluate(Q_new, [x, y, z]);
    Q1_new := Evaluate(Q1_new, [x, y, z]);

    E_new := inv_Q*w^3 + w*Evaluate(f2_inv, [x, y, z]) + Evaluate(f3_inv, [x, y, z]);
    E1_new := inv_Q1*w^3 + w*Evaluate(f2_1_inv, [x, y, z]) + Evaluate(f3_1_inv, [x, y, z]);

    return Q_new, E_new, Q1_new, E1_new, T*T_t, T1*T1_t;
end function;

function NormalizeMatrix(M)
    idx := Min([ i : i in [1..Ncols(M)] | M[1][i] ne 0 ]);
    return M / M[1][idx];
end function;

//
// Functions checking for isomorphisms using Gröbner bases
//

function IsIsomorphicGenus4GrobnerRk3(Q, E, Q1, E1 : geometric := false)
    R := Parent(Q);
    K := BaseRing(R);
    n := 3;
    S<[a]> := PolynomialRing(K, n^2+3);
    Rtilde := PolynomialRing(S, n+1);

    Change := [ &+[ a[i + n*(j-1)] * Rtilde.i : i in [1..n] ] : j in [1..n] ] cat [ a[n^2+1] * Rtilde.(n+1) ];

    lambda := a[n^2+2];
    mu := a[n^2+3];

    Q_trans := lambda * Evaluate(Rtilde!Q, Change);
    E_trans := mu * Evaluate(Rtilde!E, Change);

    relations := [ MonomialCoefficient(Q_trans, m)-MonomialCoefficient(Rtilde!Q1, m) : m in MonomialsOfDegree(Rtilde, 2) ]
                cat [ MonomialCoefficient(E_trans, m)-MonomialCoefficient(Rtilde!E1, m) : m in MonomialsOfDegree(Rtilde, 3) ];

    geom_eq := false;

    vprint Genus4, 1 : "Checking from less generic to most generic case...";    
    for i in [1..n] do 
        I := Ideal(relations cat [a[j] : j in [1..n-i]] cat [a[n-i+1]-1]);
    
        vprint Genus4, 1 : "Computing Gröbner basis " cat Sprint(i) cat "/" cat Sprint(n) cat "...";
        G := GroebnerBasis(I);
        G_list := Eltseq(G);

        if G_list ne [1] then
            geom := [el : el in G_list | Degree(Monomials(el)[1]) gt 1];
            if geom ne [] then
                vars := [i : i in [1..n^2+3] | Max([Degree(el, i) : el in geom]) ge 1];
                S0 := PolynomialRing(K, #vars);
                new_vars := [];
                current := 1;
                for i in [1..n^2+3] do
                    if i in vars then
                        Append(~new_vars, S0.current);
                        current +:= 1;
                    else    
                        Append(~new_vars, S0!0);
                    end if;
                end for;
                Var := Variety(Ideal([Evaluate(el, new_vars) : el in geom]));
                if Var ne [] then    
                    vprint Genus4, 1 : "Matrix found over the base field";
                    L := K;
                elif geometric then
                    vprint Genus4, 1 : "Matrix found over an extension";
                    I := Ideal([Evaluate(el, new_vars) : el in geom]);
                    Var := PointsOverSplittingField(Scheme(Spec(S0), I));
                    Var := [v : v in Var];
                    L := Parent(Var[1][1]);
                    S := ChangeRing(S, L);
                    G_list := ChangeUniverse(G_list, S);
                else 
                    geom_eq := true;
                    break i;
                end if;
                res := [* *];
                for rat_pt in Var do
                    current := 1;
                    evaluation := [];
                    for i in [1..n^2+3] do
                        if i in vars then
                            Append(~evaluation, rat_pt[current]);
                            current +:= 1;
                        else    
                            Append(~evaluation, S.i);
                        end if;
                    end for;
                    G_list_eval := [Evaluate(g, evaluation) : g in G_list];
                    [NormalForm(evaluation[i], G_list_eval) : i in [1..n^2]];
                    Append(~res, DiagonalJoin(Matrix(L, n, n, [NormalForm(evaluation[i], G_list_eval) : i in [1..n^2]]), Matrix(L, [[NormalForm(evaluation[n^2+1], G_list_eval)]])));
                end for;
                return true, res;       
            else
                L := K;
                return true, [* DiagonalJoin(Matrix(K, n, n, [NormalForm(a[i], G) : i in [1..n^2]]), Matrix(K, [[NormalForm(a[n^2+1], G)]])) *];
            end if;      
        else 
            vprint Genus4, 1 : "No matrix found, continuing...";
        end if;
    end for;

    if geom_eq then 
        vprint Genus4, 1 : "Polynomials are geometrically equivalent, but not over the base field.";
    end if;

    return false;
end function;

function IsIsomorphicGenus4GrobnerRk4(Q, E, Q1, E1 : geometric := false)
    R := Parent(Q);
    K := BaseRing(R);
    n := 4;
    S<[a]> := PolynomialRing(K, n^2+2);
    Rtilde := PolynomialRing(S, n);

    Change := [ &+[ a[i + n*(j-1)] * Rtilde.i : i in [1..n] ] : j in [1..n] ];

    lambda := a[n^2+1];
    mu := a[n^2+2];

    Q_trans := lambda * Evaluate(Rtilde!Q, Change);
    E_trans := mu * Evaluate(Rtilde!E, Change);

    relations := [ MonomialCoefficient(Q_trans, m)-MonomialCoefficient(Rtilde!Q1, m) : m in MonomialsOfDegree(Rtilde, Degree(Q)) ]
                cat [ MonomialCoefficient(E_trans, m)-MonomialCoefficient(Rtilde!E1, m) : m in MonomialsOfDegree(Rtilde, Degree(E)) ];

    geom_eq := false;

    vprint Genus4, 1 : "Checking from less generic to most generic case...";    
    for i in [1..n] do 
        I := Ideal(relations cat [a[j] : j in [1..n-i]] cat [a[n-i+1]-1]);
    
        vprint Genus4, 1 : "Computing Gröbner basis " cat Sprint(i) cat "/" cat Sprint(n) cat "...";
        G := GroebnerBasis(I);
        G_list := Eltseq(G);

        if G_list ne [1] then
            geom := [el : el in G_list | Degree(Monomials(el)[1]) gt 1];
            if geom ne [] then
                vars := [i : i in [1..n^2+2] | Max([Degree(el, i) : el in geom]) ge 1];
                S0 := PolynomialRing(K, #vars);
                new_vars := [];
                current := 1;
                for i in [1..n^2+2] do
                    if i in vars then
                        Append(~new_vars, S0.current);
                        current +:= 1;
                    else    
                        Append(~new_vars, S0!0);
                    end if;
                end for;
                Var := Variety(Ideal([Evaluate(el, new_vars) : el in geom]));
                if Var ne [] then    
                    vprint Genus4, 1 : "Matrix found over the base field";
                    L := K;
                elif geometric then
                    vprint Genus4, 1 : "Matrix found over an extension";
                    I := Ideal([Evaluate(el, new_vars) : el in geom]);
                    Var := PointsOverSplittingField(Scheme(Spec(S0), I));
                    Var := [v : v in Var];
                    L := Parent(Var[1][1]);
                    S := ChangeRing(S, L);
                    G_list := ChangeUniverse(G_list, S);
                else 
                    geom_eq := true;
                    break i;
                end if;
                res := [* *];
                for rat_pt in Var do
                    current := 1;
                    evaluation := [];
                    for i in [1..n^2+1] do
                        if i in vars then
                            Append(~evaluation, rat_pt[current]);
                            current +:= 1;
                        else    
                            Append(~evaluation, S.i);
                        end if;
                    end for;
                    G_list_eval := [Evaluate(g, evaluation) : g in G_list];
                    Append(~res, Matrix(L, n, n, [NormalForm(evaluation[i], G_list_eval) : i in [1..n^2]]));
                end for;
                return true, res;       
            else
                return true, [* Matrix(K, n, n, [NormalForm(a[i], G) : i in [1..n^2]]) *];
            end if;      
        else 
            vprint Genus4, 1 : "No matrix found, continuing...";
        end if;
    end for;

    if geom_eq then 
        vprint Genus4, 1 : "Polynomials are geometrically equivalent, but not over the base field.";
    end if;

    return false;
end function;

//
// Functions checking for isomorphisms between curves of genus 4 (all cases covered)
//

intrinsic IsIsomorphicGenus4(Q::RngMPolElt, E::RngMPolElt, Q1::RngMPolElt, E1::RngMPolElt : geometric := false) -> .
    {
        Given two genus 4 curves defined by (Q, E) and (Q1, E1) respectively, return true (and M), when there exists a matrix M
        such that the ideal defined by (Q^M, E^M) is the same as the ideal defined by (Q1, E1), and false otherwise.        
    }

    R<x,y,z,w> := Parent(Q);
    K := BaseRing(R);

    alpha := TransvectantGeneral([Q, Q, Q, Q], 2);
    alpha1 := TransvectantGeneral([Q1, Q1, Q1, Q1], 2);

    if alpha eq 0 and alpha1 ne 0 then
        return false;
    elif alpha eq 0 then
        Q_new, E_new, Q1_new, E1_new, T, T1 := NormalizeRk3(Q, E, Q1, E1);
        try 
            vprint Genus4 : "Checking isomorphisms using covariants...";
            test, M := IsGL4EquivalentFast(E_new, E1_new);
            if test then
                return true, [* NormalizeMatrix(T*M[1]*T1^(-1)) *];
            else
                return false;
            end if;
        catch e 
            vprint Genus4 : "Checking that invariants are equal...";
            invs, wgt := InvariantsGenus4Curves(Q_new, E_new);
            invs1 := InvariantsGenus4Curves(Q1_new, E1_new);
            if not WPSEqual(wgt, invs, invs1) then
                return false;
            end if;
            test, Mats := IsIsomorphicGenus4GrobnerRk3(Q_new, E_new, Q1_new, E1_new);
            if test then    
                return true, [* NormalizeMatrix(T*Mat*T1^(-1)) : Mat in Mats *];                
            end if;
            return false;
        end try;
    else
        E_new, E1_new := NormalizeRk4(Q, E, Q1, E1);
        Q_new, Q1_new := Explode(<Q, Q1>);
        try 
            vprint Genus4 : "Checking isomorphisms using covariants...";
            test, M := IsGL4EquivalentFast(E_new, E1_new);
            if not test then
                return false;
            end if;
            return true, M;
        catch e 
            vprint Genus4 : "Checking that invariants are equal...";
            invs, wgt := InvariantsGenus4Curves(Q_new, E_new);
            invs1 := InvariantsGenus4Curves(Q1_new, E1_new);
            if not WPSEqual(wgt, invs, invs1) then
                return false;
            end if;
            test, Mats := IsIsomorphicGenus4GrobnerRk4(Q_new, E_new, Q1_new, E1_new);
            if not test then
                return false;
            end if;
            return true, [* NormalizeMatrix(Mat) : Mat in Mats *];
        end try;
    end if;
end intrinsic;

intrinsic IsIsomorphicGenus4(C::Crv, C1::Crv : geometric := false) -> .
    {
        Given two genus 4 curves C and C1, canonically embedded in P^3, return true (and the linear transformation), if there exists a 
        linear transformation which transforms the coordinate ring of C into that of C1, and false otherwise.        
    }

    require Genus(C) eq 4 and Genus(C1) eq 4: "C and C1 must be of genus 4.";

	vprint Genus4 : "Checking if the curves are hyperelliptic...";
	if Degree(C) gt 6 then
		t, E := IsHyperelliptic(C);
        t1, E1 := IsHyperelliptic(C1);
		if t and t1 then
			vprint Genus4 : "The curve are hyperelliptic.";
			return IsIsomorphicHyperellipticCurves(E, E1 : geometric := geometric);
		end if; 
	else
		vprint Genus4 : "The curves are non-hyperelliptic, computing equations...";

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

		Eq1 := Equations(C1);
		if Sort([Degree(l) : l in Eq1]) eq [2,3] then
			L1 := Eq1;
		else
			L1 := Equations(Image(CanonicalEmbedding(C1)));
		end if;
		Deg1 := [Degree(l) : l in L1];
		i1 := Index(Deg1, 2);
		j1 := Index(Deg1, 3);
		Q1 := L1[i1];
		E1 := L1[j1];

        return IsIsomorphicGenus4(Q, E, Q1, E1 : geometric := geometric);
    end if;

    error("The curves are not in the right format");
end intrinsic;

intrinsic IsIsomorphicGenus4(C::HypCrv, C1::HypCrv : geometric := false) -> .
    {
        Given two hyperelliptic genus 4 curves C and C1, return true (and M), if there exists a matrix M in GL2
        which transforms the coordinate ring of C into that of C1, and false otherwise.        
    }

    require Genus(C) eq 4 and Genus(C1) eq 4: "C and C1 must be of genus 4.";

	return IsIsomorphicHyperellipticCurves(C, C1 : geometric := geometric);
end intrinsic;
