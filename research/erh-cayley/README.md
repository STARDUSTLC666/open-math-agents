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

Use PowerShell 7 with Lean 4.33.1 on PATH and the FormalConjectures and Mathlib revisions recorded in `build-order.json`. From this directory run the following command with the path to that FormalConjectures checkout and its existing Mathlib cache.

```powershell
./Rebuild.ps1 -FormalConjectures /path/to/formal-conjectures
```

The script checks all source hashes, compiles the files in dependency order and verifies nineteen axiom reports from the four research modules. Use `./Rebuild.ps1 -CheckSourcesOnly` to check the source manifest.
