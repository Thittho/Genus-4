
S<x,y> := PolynomialRing(QQ, 2);
a := 2;
F := (a*a+a)*x^9*y+(a*a+2*a^2+1)*x^7*y^3+(a^2+1+a)*x^6*y^4+a*x^5*y^5+(a^2-2)*x^4*y^6+a*a*x^3*y^7+(a^2+a)*x*y^9+a*y^10;

invs := InvariantsGenus4Curves(F);

import "rec_hyp_g4.m" : a11,a12,a13,a22,a23,a33,f11111,f11112,f11113,f11122,f11123,f11133,f11222,f11223,f11233,f11333,f12222,f12223,f12233,f12333,f13333,f22222,f22223,f22233,f22333,f23333,f33333;

function HyperellipticCurveFromBrouwerPopoviciuInvariants(I : 
    minimize := false) 
    
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

    if minimize then
        return MinRedBinForm(f);
    end if;
    return f;

end function;


S<[I]> := PolynomialRing(QQ, 50);
R0<X,Y,Z> := PolynomialRing(FieldOfFractions(S), 3);
inv := I;
    M := Matrix([[a11(inv), a12(inv), a13(inv)],
                 [a12(inv), a22(inv), a23(inv)],
                 [a13(inv), a23(inv), a33(inv)]]);
Q := (Matrix([[X,Y,Z]])*ChangeRing(M, R0)*Transpose(Matrix([[X,Y,Z]])))[1][1];
Q := 2459*59^3*Q;

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

LCM(&cat[[Denominator(c) : c in Coefficients(S!coef)] : coef in Coefficients(E)]);
[Factorization(LCM([Denominator(c) : c in Coefficients(S!coef)])) : coef in Coefficients(Q)];
