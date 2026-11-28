import ReciprocalRadius
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-! The 3-4-1 inequality for the Dedekind ideal series, obtained from the
finite prime-ideal sieve. The local log calculation adapts Mathlib's
`LSeries/Nonvanishing.lean` (Apache-2.0); the limiting sieve is over ideals. -/

noncomputable section
namespace OMA.EulerBoundary

open Complex NumberField Filter OMA.ReciprocalRadius
open scoped NumberField Topology

abbrev pt (x y : ℝ) : ℂ := ⟨x,y⟩

private theorem log341 {a : ℝ} (ha : 0 ≤ a) (ha' : a < 1) {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ 3 * (-log (1 - a)).re + 4 * (-log (1 - a * z)).re + (-log (1 - a * z^2)).re := by
  have h0 : ‖(a : ℂ)‖ < 1 := by simpa only [Complex.norm_of_nonneg ha] using ha'
  have h1 : ‖a * z‖ < 1 := by rwa [norm_mul, hz, mul_one]
  have h2 : ‖a * z^2‖ < 1 := by rwa [norm_mul, norm_pow, hz, one_pow, mul_one]
  rw [← ((hasSum_re <| hasSum_taylorSeries_neg_log h0).mul_left 3).add
    ((hasSum_re <| hasSum_taylorSeries_neg_log h1).mul_left 4) |>.add
    (hasSum_re <| hasSum_taylorSeries_neg_log h2) |>.tsum_eq]
  refine tsum_nonneg fun n => ?_
  simp only [← ofReal_pow, div_natCast_re, ofReal_re, mul_pow, mul_re, ofReal_im, zero_mul, sub_zero]
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · simp only [← mul_div_assoc, ← add_div]
    refine div_nonneg ?_ n.cast_nonneg
    rw [← pow_mul, pow_mul', sq, mul_re, ← sq, ← sq, ← sq_norm_sub_sq_re, norm_pow, hz]
    convert! (show 0 ≤ 2 * a ^ n * ((z ^ n).re + 1) ^ 2 by positivity) using 1
    ring

private theorem factor341 {a : ℝ} (ha : 0 ≤ a) (ha' : a < 1) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖(1 - (a:ℂ))^3 * (1 - a*z)^4 * (1 - a*z^2)‖ ≤ 1 := by
  have hl := log341 ha ha' hz
  simp only [neg_re, log_re] at hl
  rw [norm_mul, norm_mul, norm_pow, norm_pow]
  by_cases h0 : ‖1 - (a : ℂ)‖ = 0
  · simp [h0]
  by_cases h1 : ‖1 - a*z‖ = 0
  · simp [h1]
  by_cases h2 : ‖1 - a*z^2‖ = 0
  · simp [h2]
  apply (Real.log_nonpos_iff (by positivity)).mp
  rw [Real.log_mul (mul_ne_zero (pow_ne_zero _ h0) (pow_ne_zero _ h1)) h2,
    Real.log_mul (pow_ne_zero _ h0) (pow_ne_zero _ h1), Real.log_pow, Real.log_pow]
  push_cast
  linarith

private theorem norm_factor341 (n : ℕ) (hn : 2 ≤ n) (x t : ℝ) (hx : 1 < x) :
    ‖(1 - (n:ℂ)^(-pt x 0))^3 * (1 - (n:ℂ)^(-pt x t))^4 * (1 - (n:ℂ)^(-pt x (2*t)))‖ ≤ 1 := by
  let a := (n : ℝ)^(-x)
  let w := (n : ℂ)^(-(I * t))
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have ha : (a : ℂ) = (n : ℂ)^(-(x:ℂ)) := by
    simp only [a, ofReal_cpow n.cast_nonneg, ofReal_neg, ofReal_natCast]
  have hw : ‖w‖ = 1 := by
    rw [show w = ((n:ℝ):ℂ)^(-(I * t)) by simp [w], norm_cpow_eq_rpow_re_of_pos (by positivity : 0 < (n:ℝ))]
    simp
  have ha' : a < 1 := by
    rw [show a = (n:ℝ)^(-x) from rfl, Real.rpow_neg n.cast_nonneg, inv_lt_one_iff₀]
    exact .inr (Real.one_lt_rpow (mod_cast one_lt_two.trans_le hn) (zero_lt_one.trans hx))
  have e0 : -pt x 0 = -(x:ℂ) := by apply Complex.ext <;> simp [pt]
  have e1 : -pt x t = -(x:ℂ) + -(I*t) := by apply Complex.ext <;> simp [pt]
  have e2 : -pt x (2*t) = -(x:ℂ) + (2:ℕ)* -(I*t) := by apply Complex.ext <;> simp [pt]
  rw [e0, e1, e2, cpow_add _ _ hn0, cpow_add _ _ hn0, cpow_nat_mul, ← ha]
  exact factor341 (Real.rpow_nonneg n.cast_nonneg _) ha' hw

variable (K : Type*) [Field K] [NumberField K]

private theorem prime_norm (p : primeIdeals K) : 2 ≤ Ideal.absNorm p.val := by
  have h0 : Ideal.absNorm p.val ≠ 0 := by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff]
    exact p.property.ne_zero
  have h1 : Ideal.absNorm p.val ≠ 1 := fun h => p.property.not_isUnit (Ideal.isUnit_iff.mpr (Ideal.absNorm_eq_one_iff.mp h))
  omega

/-- The three shifted values are taken only where the ideal series converges. -/
theorem zeta341 (x t : ℝ) (hx : 1 < x) :
    1 ≤ ‖dedekindZeta K (pt x 0)^3 * dedekindZeta K (pt x t)^4 * dedekindZeta K (pt x (2*t))‖ := by
  classical
  let V (y : ℝ) (S : Finset (primeIdeals K)) := ∑' J, sift K (pt x y) S J
  let Z (y : ℝ) := dedekindZeta K (pt x y)
  let D (y : ℝ) (p : primeIdeals K) := 1 - weight K (pt x y) p.val
  have empty (y : ℝ) : V y ∅ = Z y := by simpa [V,Z,sift] using sum_eq_zeta K (s := pt x y) hx
  have step (y : ℝ) (S : Finset (primeIdeals K)) (p : primeIdeals K) (hp : p ∉ S) :
      V y (insert p S) = D y p * V y S := sift_insert K (s := pt x y) hx S p hp
  have h (S : Finset (primeIdeals K)) :
      ‖V 0 S^3 * V t S^4 * V (2*t) S‖ ≤ ‖Z 0^3 * Z t^4 * Z (2*t)‖ := by
    induction S using Finset.induction_on with
    | empty => simp only [empty, le_refl]
    | @insert p S hp ih =>
      rw [step _ _ _ hp, step _ _ _ hp, step _ _ _ hp,
        show (D 0 p * V 0 S)^3 * (D t p * V t S)^4 * (D (2*t) p * V (2*t) S) =
          (D 0 p^3 * D t p^4 * D (2*t) p) * (V 0 S^3 * V t S^4 * V (2*t) S) by ring, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (norm_factor341 _ (prime_norm K p) x t hx)).trans ih
  have lim (y : ℝ) : Tendsto (V y) atTop (𝓝 1) := sift_limit K (s := pt x y) hx
  have lim' := ((((lim 0).pow 3).mul ((lim t).pow 4)).mul (lim (2*t))).norm
  simpa using le_of_tendsto lim' (Eventually.of_forall h)

#print axioms OMA.EulerBoundary.zeta341
end OMA.EulerBoundary
