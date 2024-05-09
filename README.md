Description
--

This Magma repository computes invariants of genus 4 curves.
 
Prerequisites
--

You need an installation of Magma on your machine.

Installation
--

You can enable the functionality of this package in Magma by attaching the Genus-4/magma/spec file with AttachSpec. To make this independent of the directory in which you find yourself, and to active this on startup by default, you may want to indicate the relative path in your `~/.magmarc file`, by adding a line like
```
AttachSpec("~/Genus-4/magma/spec");
```

Usage
--

Examples that test the routines in this package can be found in the directory
[`Examples`](Examples) (a full list of intrinsics is [here](intrinsics.md)).

Basic use of the package is as follows.

* Compute invariants of smooth non-hyperelliptic genus 4 curves, given as the intersection of a quadric and a cubic, or as a curve directly.

```
P3 := ProjectiveSpace(Rationals(), 3);
R<x,y,z,w> := CoordinateRing(P3);
Q1 := -10*x^2 - x*y + 8*x*z + 9*w*z - 6*z^2;
E1 := -x^2*y - x^2*z - 5*x^2*w - 6*x*y^2 - 2*x*y*z - 9*x*y*w + 7*x*z^2 + 3*x*z*w -
    8*x*w^2 - 10*y^3 + 3*y^2*z - y^2*w - 3*y*z^2 - 7*y*w^2 - z^3 + z^2*w -
    10*z*w^2 + 3*w^3;
J1, Wgt := InvariantsGenus4Curves(Q1, E1);
// or alternatively, 
C := Curve(P3, [Q1, E1]);
J1, Wgt := InvariantsGenus4Curves(C);
```

* Compute invariants of hyperelliptic genus 4 curves, given as a curve or a polynomial.
```
_<X> := PolynomialRing(Rationals());   
I := InvariantsGenus4Curves(X^10+5*X^8-7*X+1);
```

* Check if two curves of genus 4 are isomorphic.
```
P3 := ProjectiveSpace(Rationals(), 3);
R<x,y,z,w> := CoordinateRing(P3);
Q1 := -10*x^2 - x*y + 8*x*z + 9*y*z - 6*z^2;
E1 := 4*x^3-x^2*y - x^2*z - 5*x^2*w - 6*x*y^2 - 2*x*y*z - 9*x*y*w + 7*x*z^2 + 3*x*z*w - 8*x*w^2 - 10*y^3 + 3*y^2*z - y^2*w - 3*y*z^2 - 7*y*w^2 - z^3 + z^2*w - 10*z*w^2 + 3*w^3;

Q2 := Evaluate(R!Q1, [2*y+3*x, x-2*y, 3*z, -3*w]);
E2 := Evaluate(R!E1, [2*y+3*x, x-2*y, 3*z, -3*w]);

// Check that they are isomorphic
IsIsomorphicG4(Q1, E1, Q2, E2);
// or alternatively,
C1 := Curve(P3, [Q1, E1]);
C2 := Curve(P3, [Q2, E2]);
IsIsomorphicG4(C1, C2);
```
Citing this work
--

If this repository was helpful to your research, please cite the following preprint:
Thomas Bouchet, _Invariants of genus 4 curves, 2023_, [arxiv:2310.01158](https://arxiv.org/abs/2310.01158)

Credit
--
The skeleton of this README file was copied from [https://github.com/JRSijsling/quartic/blob/main/README.md](https://github.com/JRSijsling/quartic/blob/main/README.md)
