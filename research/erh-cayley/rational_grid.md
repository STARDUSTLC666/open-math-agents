# A finite grid for the rational field

For the rational field and the closed disk |w| ≤ 1/2, the least truncation parameter admitting any denominator is n=15. One witness has 258 terms and D=262144. For the prescribed denominator D=((n+1)²+2)(n+1), the first witness has n=22, 531 terms and D=12213. Every n≥15 admits a denominator. These figures apply to the inequalities in [PR #35967](https://github.com/lefttosolve2/open-math-agents/pull/35967).

These results combine the analytic estimates below with rigorous real and complex ball arithmetic. The accompanying Lean package proves the general grid criterion. The field-specific coefficient enclosures and the numerical witnesses were checked by FLINT. [Verification program](rational_grid.py) · [Output](rational-grid.json)

## Arithmetic germ

Write T(w)=(2+w)/(1−w) and H(w)=(1−w)⁶ (T(w)−1) ζ(T(w)). At real part greater than one, the Dedekind zeta function of the rational field is the classical Riemann zeta function. The product (s−1)ζ(s) extends across s=1. The program uses the expansion of ζ(s)−1/(s−1) about s=2, multiplies it by s−1 and adds one. Substituting s−2=3w/(1−w) and multiplying by (1−w)⁶ gives enclosures for the first 578 coefficients of H. The substituted series has zero constant term, so formal truncation at this stage preserves all 578 coefficients.

Let P_l be the first l terms and B_l the sum of j|a_j| over 0≤j<l. The output bounds B_578 by 120. It covers the closed radius-1/2 disk by dyadic squares. On a square centered at c with half-width h, the distance to c is at most 2h. The program evaluates the first 20 terms and their derivative at c. The second derivative of those terms has modulus bounded on the unit disk by the sum of j(j−1)|a_j|. Taylor's formula along the segment from c to w and the finite sum of |a_j|2^(−j) for 20≤j<578 enclose P_578 on the part of the square inside the disk. Every box center and the disk lie in the unit disk. Subdivision terminates with |P_578(w)|>65/1024 throughout the closed disk. Boxes discarded by the distance test have empty intersection with it.

## All longer sections

For σ=Re(s)>0, Abel summation and analytic continuation give

$$
(s-1)\zeta(s)=s-s(s-1)\int_1^\infty \{x\}x^{-s-1}\,dx.
$$

Indeed, for σ>1 the identity follows by integrating the counting function floor(x)=x−{x}. The integral with {x} converges locally uniformly for σ>0 and has modulus at most 1/σ. On |w|≤R=3/5 one has Re(T(w))≥(2−R)/(1+R)=7/8, using Re(T(w))=1/2+(3/2)(1−|w|²)/|1−w|². Also |T(w)|≤(2+R)/(1−R)=13/2. Consequently |H(w)| is at most

$$
(1+R)^6\frac{13}{2}\left(1+\frac{15/2}{7/8}\right)<2048.
$$

Cauchy's coefficient estimate gives |a_j|≤2048(5/3)^j. For any l≥258, the difference between P_l and P_578 on |w|≤1/2 has modulus at most 2048(5/6)^258/(1−5/6)<1/65536. Thus every such section has modulus greater than 4159/65536. These comparisons use exact rational arithmetic in the program.

For any n≥15, take l=(n+1)²+2 and D=1+ceil(4096 B_l). Then 2B_l/D<1/2048, and 1/(n+1)+1/2048≤1/16+1/2048<4159/65536. For the displayed witnesses with l≤578, the estimate B_l≤B_578<120 also certifies the smaller listed denominators.

## Minimality

For n=0 the program checks |P_l(1/4)|<1. For 1≤n≤14 it checks |P_l(1/2)|<1/(n+1). The inward-rounding lemma proves that a passing grid with any denominator would give the strict inequality 1/(n+1)<|P_l| at every point of the disk. Each check therefore excludes every denominator for that parameter. For 15≤n≤21 the program also checks failure of the prescribed fixed mesh directly at the real lattice node floor(D/2)/D. [Inward rounding](CayleyFiniteGrid.lean)

## Reproduction

With Python and python-flint 0.9.0 installed, run `python rational_grid.py`. The recorded run used FLINT 3.6.0, 1536-bit series calculations and 112-bit box calculations. Each comparison requires separated enclosures. [Recorded checks](rational-grid.json)
