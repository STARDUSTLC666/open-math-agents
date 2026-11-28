import SelfDualHeat
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Fold the norm integral at x=1 using the self-dual theta equation.
On the critical strip both resulting powers are bounded by one. -/
noncomputable section
namespace OMA.StripHeat

open Complex NumberField NumberField.InfinitePlace MeasureTheory Set
open ThetaContinuation HeatDecay ExactRadius
variable (K : Type*) [Field K] [NumberField K]

private def integrand (s : ℂ) (x : ℝ) := (x:ℂ)^(s-1) * (pair K).f_modif x
private def weight (s : ℂ) (x : ℝ) := ‖integrand K s x‖

private theorem integrand_int (s : ℂ) : IntegrableOn (integrand K s) (Ioi 0) :=
  ((pair K).isStrongFEPair_toStrongFEPair.hasMellin s).1

private theorem weight_eq (s : ℂ) {x : ℝ} (hx : 0 < x) :
    weight K s x = x^(s.re-1) * ‖(pair K).f_modif x‖ := by
  rw [weight, integrand, norm_mul, norm_cpow_eq_rpow_re_of_pos hx]; simp

private theorem inverse_weight (s : ℂ) {x : ℝ} (hx : 0 < x) :
    |-(x^2)⁻¹| • weight K s x⁻¹ = weight K (1-s) x := by
  have hsym : (pair K).g_modif = (pair K).f_modif := by
    simp [WeakFEPair.g_modif, WeakFEPair.f_modif, pair]
  have hf := (pair K).hf_modif_FE x hx
  rw [hsym, one_div] at hf
  change (pair K).f_modif x⁻¹ = (1*((x^(1:ℝ):ℝ):ℂ)) • (pair K).f_modif x at hf
  rw [Real.rpow_one, one_mul, smul_eq_mul] at hf
  rw [smul_eq_mul, abs_neg, abs_of_nonneg (by positivity), weight_eq K s (inv_pos.mpr hx),
    weight_eq K (1-s) hx, hf, norm_mul, Complex.norm_of_nonneg hx.le, Real.inv_rpow hx.le,
    ← Real.rpow_neg hx.le]
  simp only [sub_re, one_re]
  have hinv : (x^2)⁻¹ = x^(-(2:ℝ)) := by rw [Real.rpow_neg hx.le, Real.rpow_two]
  rw [hinv]
  calc _ = (x^(-(2:ℝ)) * x^(-(s.re-1)) * x^(1:ℝ)) * ‖(pair K).f_modif x‖ := by
              rw [Real.rpow_one]; ring
       _ = _ := by rw [← Real.rpow_add hx, ← Real.rpow_add hx]; congr 2; ring

private theorem folded_integral (s : ℂ) :
    (∫ x in Ioi 0, weight K s x) =
      ∫ x in Ioi 1, weight K s x + weight K (1-s) x := by
  have himage : (fun x : ℝ => x⁻¹) '' Ioi 1 = Ioo 0 1 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨inv_pos.mpr (zero_lt_one.trans hx), inv_lt_one_of_one_lt₀ hx⟩
    · intro hy
      exact ⟨y⁻¹, (one_lt_inv₀ hy.1).mpr hy.2, inv_inv y⟩
  have hsub := integral_image_eq_integral_abs_deriv_smul (measurableSet_Ioi (a := (1:ℝ)))
    (fun x hx => (hasDerivAt_inv (zero_lt_one.trans hx).ne').hasDerivWithinAt)
    inv_injective.injOn (weight K s)
  rw [himage] at hsub
  have hsmall : (∫ x in Ioc 0 1, weight K s x) = ∫ x in Ioi 1, weight K (1-s) x := by
    rw [integral_Ioc_eq_integral_Ioo, hsub]
    exact setIntegral_congr_fun measurableSet_Ioi (fun x hx => inverse_weight K s (zero_lt_one.trans hx))
  have hi : ∀ w, IntegrableOn (weight K w) (Ioi 0) := fun w => (integrand_int K w).norm
  have hbig (w : ℂ) := (hi w).mono_set (Ioi_subset_Ioi (zero_le_one : (0:ℝ) ≤ 1))
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0:ℝ) ≤ 1),
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi ((hi s).mono_set Ioc_subset_Ioi_self)
      (hbig s), hsmall, integral_add (hbig s) (hbig (1-s)), add_comm]

private theorem weight_large (hr : nrRealPlaces K = 0) (hc : nrComplexPlaces K = 1)
    (s : ℂ) {x : ℝ} (hx : 1 < x) : weight K s x = x^(s.re-1) * heat K x := by
  rw [weight_eq K s (zero_lt_one.trans hx)]
  simp [WeakFEPair.f_modif, hx, hx.not_gt, pair, kernel_eq K hr hc (zero_lt_one.trans hx),
    heat_nonneg K x]

theorem strip_majorant (hr : nrRealPlaces K = 0) (hc : nrComplexPlaces K = 1)
    {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1) {g : ℝ → ℝ} (hg : IntegrableOn g (Ioi 1))
    (hbound : ∀ x, 1 < x → (1+x⁻¹)*heat K x ≤ g x) :
    ‖(pair K).Λ₀ s‖ ≤ ∫ x in Ioi 1, g x := by
  have hW : ‖(pair K).Λ₀ s‖ ≤ ∫ x in Ioi 0, weight K s x :=
    norm_integral_le_integral_norm (μ := volume.restrict (Ioi 0)) (integrand K s)
  rw [folded_integral K s] at hW
  have hi (w : ℂ) : IntegrableOn (weight K w) (Ioi 1) := by
    have hall : IntegrableOn (weight K w) (Ioi 0) := (integrand_int K w).norm
    exact hall.mono_set (Ioi_subset_Ioi (zero_le_one : (0:ℝ) ≤ 1))
  apply hW.trans (setIntegral_mono_on ((hi s).add (hi (1-s))) hg measurableSet_Ioi ?_)
  intro x hx
  change 1 < x at hx
  change weight K s x + weight K (1-s) x ≤ g x
  rw [weight_large K hr hc s hx, weight_large K hr hc (1-s) hx, ← add_mul]
  apply le_trans (mul_le_mul_of_nonneg_right _ (heat_nonneg K _)) (hbound x hx)
  have hx0 := zero_lt_one.trans hx
  have hpow (e : ℝ) (he : e ≤ 0) : x^e ≤ 1 := by
    simpa using (Real.rpow_le_rpow_of_exponent_le hx.le he)
  have h2 : (1-s).re-1 ≤ 0 := by rw [sub_re, one_re]; linarith
  have hprod : x^(s.re-1)*x^((1-s).re-1)=x⁻¹ := by
    rw [← Real.rpow_add hx0, sub_re, one_re, show s.re-1+(1-s.re-1)= -1 by ring, Real.rpow_neg_one]
  nlinarith [mul_nonneg (sub_nonneg.mpr (hpow _ (sub_nonpos.mpr h1))) (sub_nonneg.mpr (hpow _ h2))]

/-- Actual critical-strip bound via exponential decay from the self-dual point. -/
theorem strip_norm (hr : nrRealPlaces K = 0) (hc : nrComplexPlaces K = 1)
    {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1) :
    ‖(pair K).Λ₀ s‖ ≤ 2 * heat K 1 / rate K := by
  have hq := rate_pos K
  let a := 2 * heat K 1 * Real.exp (rate K)
  have hb : IntegrableOn (fun x : ℝ => a * Real.exp (-(rate K)*x)) (Ioi 1) :=
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos hq) 1).const_mul a
  have hbnd := strip_majorant K hr hc h0 h1 hb (fun x hx => by
    calc (1+x⁻¹)*heat K x ≤ 2*heat K x := by
           apply mul_le_mul_of_nonneg_right _ (heat_nonneg K _)
           linarith [inv_lt_one_of_one_lt₀ hx]
         _ ≤ 2*(Real.exp (-(rate K*(x-1))) * heat K 1) :=
           mul_le_mul_of_nonneg_left (contraction K zero_lt_one hx.le) (by norm_num)
         _ = a * Real.exp (-(rate K)*x) := by
           dsimp [a]
           rw [show -(rate K*(x-1)) = rate K + (-(rate K)*x) by ring, Real.exp_add]
           ring)
  rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos hq), mul_one, Real.exp_neg] at hbnd
  have hval : a * (-(Real.exp (rate K))⁻¹ / -rate K) = 2*heat K 1 / rate K := by
    dsimp [a]; field_simp [(Real.exp_pos (rate K)).ne']
  rw [hval] at hbnd
  exact hbnd

theorem zero_height_rate (hr : nrRealPlaces K = 0) (hc : nrComplexPlaces K = 1)
    {s : ℂ} (hz : s ∈ zeros K) (h0 : 0 < s.re) :
    (rate K - 1) * (rate K + 1/2) < s.im^2 := by
  have h1 := zeros_left K hz
  have hs : s ≠ 0 := by rintro rfl; norm_num at h0
  have e := (entireReg_eq_reg K hs).symm.trans (show entireReg K s = 0 from hz)
  rw [reg] at e
  have he := (div_eq_zero_iff.mp ((mul_eq_zero.mp e).resolve_right
    (inv_ne_zero (arch_ne K h0)))).resolve_right hs
  have hn := congrArg (fun z : ℂ => ‖z‖)
    (eq_neg_of_add_eq_zero_left he : s*(s-1)*(pair K).Λ₀ s = -cst K)
  simp only [norm_mul, norm_neg] at hn
  have hC := norm_pos_iff.mpr (cst_ne K)
  have hmul := mul_le_mul_of_nonneg_left (strip_norm K hr hc h0.le h1.le)
    (mul_nonneg (norm_nonneg s) (norm_nonneg (s-1)))
  rw [hn] at hmul
  have hq := rate_pos K
  have hheat : 0 < heat K 1 := by
    by_contra! h
    rw [le_antisymm h (heat_nonneg K 1)] at hmul
    simp only [mul_zero, zero_div] at hmul
    linarith
  have hl := (SelfDualHeat.self_dual_residue K hr hc).trans hmul
  rw [← mul_div_assoc, le_div_iff₀ hq] at hl
  have hprod : (2*rate K-1)*rate K ≤ 2*(‖s‖*‖s-1‖) := by
    apply (mul_le_mul_iff_left₀ hheat).mp
    linarith only [hl, show (2*rate K-1)*heat K 1*rate K =
      ((2*rate K-1)*rate K)*heat K 1 by ring,
      show ‖s‖*‖s-1‖*(2*heat K 1) = (2*(‖s‖*‖s-1‖))*heat K 1 by ring]
  have hA : ‖s‖^2 = s.re^2 + s.im^2 := by rw [Complex.sq_norm, normSq_apply]; ring
  have hB : ‖s-1‖^2 = (s.re-1)^2 + s.im^2 := by rw [Complex.sq_norm, normSq_apply]; simp [sq]
  nlinarith [sq_nonneg (‖s‖-‖s-1‖), mul_pos h0 (sub_pos.mpr h1)]

#print axioms strip_majorant
#print axioms strip_norm
#print axioms zero_height_rate
end OMA.StripHeat
