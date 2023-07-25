Exported intrinsics
--

### Transvectant of biforms

```
intrinsic Transvectant(f::RngMPolElt, g::RngMPolElt, r::RngIntElt, s::RngIntElt : 
    invariant := false) -> RngMPolElt
```

#### Invariants of genus 4 curves

```
>>>>>>> 17cfc1237a795d2814e7e88b29381dbba3e6cab5
intrinsic InvariantsGenus4Curves(Q::RngMPolElt, C::RngMPolElt : 
    normalize := false) -> SeqEnum, SeqEnum
intrinsic InvariantsGenus4Curves(f::RngUPolElt : 
    normalize := false) -> SeqEnum, SeqEnum
intrinsic InvariantsGenus4Curves(f::RngMPolElt : 
    normalize := false) -> SeqEnum, SeqEnum
intrinsic InvariantsGenus4Curves(C::CrvHyp :
    normalize := false) -> SeqEnum, SeqEnum
<<<<<<< HEAD


intrinsic IsIsomorphic(Q1::RngMPolElt, C1::RngMPolElt, Q2::RngMPolElt, C2::RngMPolElt : 
    epsilon := 0) -> Bool

intrinsic IsIsomorphic(Q1::RngMPolElt, C1::RngMPolElt, Q2::RngMPolElt, C2::RngMPolElt, K::Rng : 
    epsilon := 0) -> Bool


intrinsic ProofHsop() -> Str
intrinsic ProofLemma() -> Str
=======
intrinsic IsIsomorphic(Q1::RngMPolElt, C1::RngMPolElt, Q2::RngMPolElt, C2::RngMPolElt : 
    epsilon := 0) -> Bool
intrinsic IsIsomorphic(Q1::RngMPolElt, C1::RngMPolElt, Q2::RngMPolElt, C2::RngMPolElt, K::Rng : 
    epsilon := 0) -> Bool
```

### Verifications

```
intrinsic ProofHsop() -> Str
intrinsic ProofHsopW2() -> Str
intrinsic ProofLemma() -> Str
intrinsic CheckSecondaryInvariants(n::RngIntElt) -> SeqEnum, SeqEnum
```

