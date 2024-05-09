/* Entries, mainly the degree of the binary forms */

/* A covariant (U, V)^level */
COV_t :=  recformat<
    type,               // 0 (multiplitive) or 1 (additive)
    U, 			// Covariants in U
    V, 			// Covariants in V
    level,		// Transvectant order
    degree,             // Covariant degree
    order,              // Covariant order
    InNullCone,
    Primary             // 0 no idea ?, 1 Primary, 2 Secondary
    >;

function MultivariateTransvectant(F, G, r)

    Q, Qdeg, n := Explode(F);
    R, Rdeg, m := Explode(G);

    n := IntegerRing()!n;
    m := IntegerRing()!m;

    K := BaseRing(Parent(Q));
    
    h := Transvectant(Q, R, r);

    return [* h, Qdeg+Rdeg, n+m-2*r *];

end function;

forward GetCovariant;
function GetCovariant(Cov, FdCov, form)

    if Cov`type eq 0 then

	/* Is Cov equal to the initial form ? */
	if (Cov`U eq {* *}  and Cov`V eq {* 0 *}) or
	    (Cov`U eq {* 0 *}  and Cov`V eq {* *}) then
	    return [form, 1];
	end if;

	/* First, let us obtain the covariant U_cov */
	U_cov := 0*form + 1; U_deg := 0; U_ord := 0;
	for cov_idx in MultisetToSet(Cov`U) do

	    cov, _ := Explode(GetCovariant(FdCov[cov_idx], FdCov, form));

	    U_cov *:= cov ^ Multiplicity(Cov`U, cov_idx);
	    U_deg +:= FdCov[cov_idx]`degree * Multiplicity(Cov`U, cov_idx);
	    U_ord +:= FdCov[cov_idx]`order * Multiplicity(Cov`U, cov_idx);

	end for;

	/* Then, let us obtain the covariant V_cov */
	V_cov := 0*form + 1; V_deg := 0; V_ord := 0;
	for cov_idx in MultisetToSet(Cov`V) do

	    cov, _ := Explode(GetCovariant(FdCov[cov_idx], FdCov, form));

	    V_cov *:= cov ^ Multiplicity(Cov`V, cov_idx);
	    V_deg +:= FdCov[cov_idx]`degree * Multiplicity(Cov`V, cov_idx);
	    V_ord +:= FdCov[cov_idx]`order * Multiplicity(Cov`V, cov_idx);

	end for;

	/* Output the transvectant */
	return MultivariateTransvectant([U_cov, U_deg, U_ord], [V_cov, V_deg, V_ord], Cov`level);
    end if;

    /* First, let us obtain the covariant U_cov */
    U_cov := 0*form; U_deg := 0; U_ord := 0;
    for cov_idx in MultisetToSet(Cov`U) do

	cov, _ := Explode(GetCovariant(FdCov[cov_idx], FdCov, form));

	U_cov +:= cov * Multiplicity(Cov`U, cov_idx);
	U_deg := Max(U_deg, FdCov[cov_idx]`degree);
	U_ord := Max(U_ord, FdCov[cov_idx]`order);

    end for;

    return [*U_cov, U_deg, U_ord*];

end function;
