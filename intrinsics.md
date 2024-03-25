Exported intrinsics
--

### Transvectant of biforms

```
intrinsic Transvectant(f::RngMPolElt, g::RngMPolElt, r::RngIntElt, s::RngIntElt : 
    invariant := false) -> RngMPolElt
```

### Invariants of genus 4 curves

```
intrinsic InvariantsGenus4Curves(Q::RngMPolElt, C::RngMPolElt : 
    normalize := false) -> SeqEnum, SeqEnum
intrinsic InvariantsGenus4Curves(f::RngUPolElt : 
    normalize := false) -> SeqEnum, SeqEnum
intrinsic InvariantsGenus4Curves(f::RngMPolElt : 
    normalize := false) -> SeqEnum, SeqEnum
intrinsic InvariantsGenus4Curves(C::CrvHyp :
    normalize := false) -> SeqEnum, SeqEnum

intrinsic IsIsomorphic(Q1::RngMPolElt, C1::RngMPolElt, Q2::RngMPolElt, C2::RngMPolElt) -> Bool
```


