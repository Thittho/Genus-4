Exported intrinsics
--

### Auxiliary intrinsics

```
intrinsic QuadraticFormToMatrix(Q::RngMPolElt) -> AlgMatElt
intrinsic Transvectant(f::RngMPolElt, g::RngMPolElt, r::RngIntElt, s::RngIntElt : invariant := false) -> RngMPolElt
```

### Invariants of genus 4 curves

```
intrinsic InvariantsGenus4Curves(Q::RngMPolElt, Gamma::RngMPolElt : normalize := false) -> SeqEnum, SeqEnum, RngInt
intrinsic InvariantsGenus4Curves(C::Crv : normalize := false) -> SeqEnum, SeqEnum, RngInt
intrinsic InvariantsGenus4Curves(f::RngMPolElt : normalize := false) -> SeqEnum, SeqEnum
intrinsic InvariantsGenus4Curves(f::RngUPolElt : normalize := false) -> SeqEnum, SeqEnum
intrinsic InvariantsGenus4Curves(C::CrvHyp : normalize := false) -> SeqEnum, SeqEnum
```

### Reconstruction of genus 4 curves from their invariants

```
intrinsic ReconstructionGenus4(I::SeqEnum : minimize := true) -> .
```

### Isomorphisms between genus 4 curves 

```
intrinsic IsIsomorphicGenus4(Q::RngMPolElt, E::RngMPolElt, Q1::RngMPolElt, E1::RngMPolElt : geometric := false) -> .
intrinsic IsIsomorphicGenus4(C::Crv, C1::Crv : geometric := false) -> .
intrinsic IsIsomorphicGenus4(C::HypCrv, C1::HypCrv : geometric := false) -> .
```

### Discriminants of genus 4 curves

```
intrinsic DiscriminantFromInvariantsGenus4(I::SeqEnum : norm := 1) -> RngInt
intrinsic DiscriminantGenus4(Q::RngMPolElt, E::RngMPolElt) -> RngInt
intrinsic DiscriminantGenus4(f::RngUPolElt) -> RngInt
intrinsic DiscriminantGenus4(C::CrvHyp) -> RngInt
```

### Minimization of genus 4 curves over QQ

```
intrinsic MinimizeGenus4OneStep(Q::RngMPolElt, Gamma::RngMPolElt) -> RngMPolElt, RngMPolElt
intrinsic MinimizeGenus4(Q::RngMPolElt, Gamma::RngMPolElt) -> RngMPolElt, RngMPolElt
```