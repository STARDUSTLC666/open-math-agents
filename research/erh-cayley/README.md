# Reciprocal Cayley coefficients for Dedekind zeta

The reduction in [PR #32173](https://github.com/lefttosolve2/open-math-agents/pull/32173) asks for uniform bounds on the Taylor coefficients of one arithmetic germ at zero. The coordinate sends the half-plane Re(s) > 31/32 to the unit disk and sends s = 2 to zero.

For every number field, there is a radius r strictly between 16/17 and 1 such that |a_n| r^n is bounded over all n. More precisely, a zero-height exclusion through H in the open critical strip suffices at any radius satisfying 0 < r < 1 and r² ((17/16)² + H²) ≤ 1 + H². The bounds include the stated radius.

| Field | Verified radius |
| --- | --- |
| Degree one | 499/500 |
| Gaussian rationals | 993/1000 |
| Cubic fields of absolute discriminant at most 23 | 123/125 |
| Fifth cyclotomic field | 39/40 |

The general estimate is in `CayleyBounds.lean`. Its arithmetic applications are in `CayleyFields.lean`. The remaining Lean files are the transitive dependencies of these two modules, including verbatim copies of the public upstream reductions. The arithmetic lower bound required for all radii below 1 is open.

Use PowerShell 7 with Lean 4.33.1 on PATH and the FormalConjectures and Mathlib revisions recorded in `build-order.json`. From this directory run the following command with the path to that FormalConjectures checkout and its existing Mathlib cache.

```powershell
./Rebuild.ps1 -FormalConjectures /path/to/formal-conjectures
```

The script checks all source hashes, compiles the files in dependency order and verifies the ten axiom reports from the new modules. Use `./Rebuild.ps1 -CheckSourcesOnly` to check the source manifest.
