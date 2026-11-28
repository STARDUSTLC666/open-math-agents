# Reciprocal Cayley coefficients for Dedekind zeta

The reduction in [PR #32173](https://github.com/lefttosolve2/open-math-agents/pull/32173) asks for uniform bounds on the Taylor coefficients of one arithmetic germ at zero. The coordinate sends the half-plane Re(s) > 31/32 to the unit disk and sends s = 2 to zero.

For every number field, there is a radius r strictly between 16/17 and 1 such that |a_n| r^n is bounded over all n. More precisely, a zero-height exclusion through H in the open critical strip suffices at any radius satisfying 0 < r < 1 and r² ((17/16)² + H²) ≤ 1 + H². The bounds include the stated radius.

| Field | Verified radius |
| --- | --- |
| Degree one | 499/500 |
| Gaussian rationals | 993/1000 |
| Cubic fields of absolute discriminant at most 23 | 123/125 |
| Fifth cyclotomic field | 39/40 |

The general estimate is in `CayleyBounds.lean`. Its arithmetic applications are in `CayleyFields.lean`. The package includes the transitive local dependencies and the upstream reductions. The arithmetic coefficient bound required for all radii below 1 is open.

## Computing the coefficients

Write U(s) = (s − 1) ζ_K(s) near s = 2 and Df(s) = (16/33)(s + 1/16)² f′(s). The forward coefficients are b_n = (DⁿU)(2)/n!. The reciprocal coefficients satisfy a_0 = 1/b_0 and

$$
a_{n+1}=-\frac{1}{b_0}\sum_{j=0}^{n} b_{j+1}a_{n-j}.
$$

For a given r ≥ 0, if every finite sum of |b_j| r^j for 1 ≤ j ≤ N is at most |b_0|, this recursion gives |a_n| r^n ≤ |a_0| for every n. The derivation and weighted estimate are in `CayleyRecurrence.lean`.

For every number field some 0 < r < 1 and some finite N violate this sufficient condition. The prefix inequality at r would bound the forward function throughout the circle of radius r by 2|b_0|. On the positive real ray, |ζ_K(x)| ≥ 1 and the forward value at the inverse image of x has modulus at least x − 1. Taking x = 2|b_0| + 3 gives a witness. `CayleyObstruction.lean` verifies the Taylor sum, the pointwise bound and this obstruction. The signed inverse recurrence retains the cancellation discarded by the absolute estimate.

## First differences and boundary values

Let F(w) = W(T(w)), where W is the entire regularization, and let C(w) = (1−w)F(w). The positive-order Taylor coefficients c_n of C are b_n−b_{n−1}. The Taylor coefficients of the reciprocal germ of C are the partial sums of the original reciprocal coefficients. For every fixed 0 ≤ r < 1, the two reciprocal coefficient bounds are equivalent. At any radius where every weighted absolute prefix starting at c_1 is at most |c_0|, the reciprocal bound follows. [Coefficient identities](CayleyDifference.lean)

On the real radius, C(w) tends to 33/16 as w tends to 1. An increasing sequence of integer heights u_n, common to all fields and all real σ > 1, also gives ζ_K(σ+i u_n) → ζ_K(σ). Its construction uses recurrence in the compact product of unit circles indexed by positive integer norms, followed by dominated convergence in the absolutely convergent series. [Vertical returns and real-axis limits](CayleyReturn.lean)

The disk points corresponding to σ+i u_n approach 1, and their C-values tend to (33/16)ζ_K(σ). The pole at σ=1 makes these limit values unbounded as σ ranges over (1,∞). For every field, every neighborhood of 1 within the disk therefore contains points with arbitrarily large |C|. The series of absolute values of the c_n diverges. The weighted prefix criterion fails on some subdisk even after the linear normalization. Growth of the signed reciprocal coefficients at unrestricted radii remains open. [Boundary limits and coefficient obstruction](CayleyBoundaryValues.lean)

## Taylor sections on the critical half-plane

For a number field of degree d, put T(w)=(2+w)/(1−w). This map takes the open unit disk onto Re(s)>1/2. Near the origin take the Taylor coefficients of (1−w)^(d+5) (T(w)−1) ζ_K(T(w)). This uses the absolutely convergent ideal Dirichlet series near s=2. A bound on the second derivative gives |a_(j+2)| ≤ M/((j+1)(j+2)) for every j and a single field-dependent M. The error after the first N+2 terms is at most M/(N+1) throughout the open disk. [Smoothing estimate](CayleySmoothing.lean) · [Uniform truncation](CayleySections.lean) · [Full critical half-plane](CayleyCritical.lean)

For parameter n, form the polynomial P from its first l=(n+1)^2+2 coefficients. On the lattice (j+ik)/D test the nodes inside the chosen closed disk. The strict lower threshold for |P| is 1/(n+1)+2B/D, where B is the finite sum of j|a_j| for 0 ≤ j < l. The margin accounts for the displacement to a lattice node. The field constant M does not appear in the test. The formal reduction uses an arbitrary mesh denominator D. [Inward rounding and bounds](CayleyFiniteGrid.lean) · [Submitted reduction](https://github.com/lefttosolve2/open-math-agents/pull/35967)

One can fix D=l(n+1) in advance. On a closed disk of radius r<1, the regularized function is zero-free exactly when all sufficiently late tests with this fixed mesh pass. On the disks r=m/(m+1) for all fields and all m this condition is equivalent to ERH. The all-fields, all-disks assertion is open. The proofs do not compute an onset n or certified numerical coefficient values. [Fixed-mesh equivalence](CayleyCertificates.lean)

| Field | Closed-disk radius for eventual passing |
| --- | --- |
| Every number field | 1/2 |
| Degree one | 25/26 |
| Gaussian rationals | 6/7 |
| Cubic fields of absolute discriminant at most 23 | 3/4 |
| Fifth cyclotomic field | 2/3 |

These radii follow from nonvanishing on Re(s) ≥ 1 and the respective low-height exclusions. For a strip free of zeros up to absolute height A, any 0 ≤ r < 1 satisfying r²(4+A²) ≤ 1+A² qualifies. [Height transfer and field specializations](CayleyCertificates.lean)

The positive real endpoint of disk m is sent to s=3m+2. At this endpoint (m+1)^(d+4) times the modulus of the damped function tends to 3. For every C>3 there are field-dependent cutoffs such that every passing grid beyond both cutoffs must satisfy (m+1)^(d+4)<C(n+1), for every choice of D. [Lean theorem](CayleyCost.lean)

For the rational field on the disk of radius 1/2, a separate rigorous interval computation finds the first passing n. It is 15 with an arbitrary denominator (258 polynomial terms, D=262144) and 22 with the fixed rule (531 terms, D=12213). [Derivation and reproducible interval certificate](rational_grid.md)

Use PowerShell 7 with Lean 4.33.1 on PATH and the FormalConjectures and Mathlib revisions recorded in `build-order.json`. From this directory run the following command with the path to that FormalConjectures checkout and its existing Mathlib cache.

```powershell
./Rebuild.ps1 -FormalConjectures /path/to/formal-conjectures
```

The script checks all source hashes, compiles the files in dependency order and verifies the axiom reports listed in the manifest. Use `./Rebuild.ps1 -CheckSourcesOnly` to check the source manifest.
