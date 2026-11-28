import HeatDecay

/-! Comparing the theta equation at x and 1/x as x decreases to one gives
a bound with its full discriminant dependence. Only elementary rational
envelopes are differentiated implicitly by taking a continuous limit. -/
noncomputable section
namespace OMA.SelfDualHeat
open Complex NumberField NumberField.InfinitePlace Filter Set
open ThetaContinuation HeatDecay
open scoped Topology
variable (K : Type*) [Field K] [NumberField K]

private theorem inversion (hr : nrRealPlaces K = 0) (hc : nrComplexPlaces K = 1)
    {x : ℝ} (hx : 0 < x) :
    heat K x⁻¹ = x * heat K x + (x-1) * (cst K).re := by
  have fe := (pair K).h_feq x hx
  change DedekindMellin.kernel K (1/x) + cst K = (1*(((x:ℝ)^(1:ℝ):ℝ):ℂ)) •
    (DedekindMellin.kernel K x + cst K) at fe
  rw [one_div, kernel_eq K hr hc (inv_pos.mpr hx), kernel_eq K hr hc hx,
    Real.rpow_one, one_mul, smul_eq_mul] at fe
  have h := congrArg Complex.re fe
  simp only [add_re, ofReal_re, mul_re, ofReal_im, zero_mul, sub_zero] at h
  linarith

private theorem quotient_bound (hr : nrRealPlaces K = 0) (hc : nrComplexPlaces K = 1)
    {h : ℝ} (hh : 0 < h) :
    (rate K / (1+h) + (rate K-1)/(1+rate K*h)) * heat K 1 ≤ (cst K).re := by
  let q := rate K
  let x := 1+h
  have hq : 0 < q := rate_pos K
  have hx1 : 1 < x := by dsimp [x]; linarith
  have hx : 0 < x := zero_lt_one.trans hx1
  have hden : 0 < 1+q*h := by positivity
  have hleft := contraction K (x := x⁻¹) (y := 1) (inv_pos.mpr hx)
    ((inv_le_one₀ hx).mpr hx1.le)
  rw [Real.exp_neg, ← div_eq_inv_mul, le_div_iff₀ (Real.exp_pos _)] at hleft
  have hsmall : (1+q*(1-x⁻¹)) * heat K 1 ≤ heat K x⁻¹ := by
    calc _ ≤ Real.exp (q*(1-x⁻¹)) * heat K 1 := by
               apply mul_le_mul_of_nonneg_right _ (heat_nonneg K _)
               linarith [Real.add_one_le_exp (q*(1-x⁻¹))]
         _ ≤ _ := by simpa [q, mul_comm] using hleft
  have hright := contraction K (x := 1) (y := x) zero_lt_one hx1.le
  have hdiff : x-1 = h := by dsimp [x]; ring
  rw [hdiff, Real.exp_neg, ← div_eq_inv_mul] at hright
  have hlarge : heat K x ≤ heat K 1 / (1+q*h) :=
    hright.trans (div_le_div_of_nonneg_left (heat_nonneg K _) hden
      (by linarith [Real.add_one_le_exp (q*h)]))
  have hid := inversion K hr hc hx
  rw [hdiff] at hid
  have hprod := mul_le_mul_of_nonneg_left hlarge hx.le
  have hcmp : ((1+q*(1-x⁻¹))-x/(1+q*h)) * heat K 1 ≤ h*(cst K).re := by
    linarith only [hsmall, hid, hprod, show x*(heat K 1/(1+q*h)) =
      (x/(1+q*h))*heat K 1 by ring,
      show ((1+q*(1-x⁻¹))-x/(1+q*h))*heat K 1 =
        (1+q*(1-x⁻¹))*heat K 1 - (x/(1+q*h))*heat K 1 by ring]
  have hid' : (1+q*(1-x⁻¹))-x/(1+q*h) = h*(q/x+(q-1)/(1+q*h)) := by
    field_simp [hx.ne', hden.ne']; dsimp [x]; ring
  rw [hid', mul_assoc] at hcmp
  exact (mul_le_mul_iff_right₀ hh).mp hcmp

theorem self_dual_residue (hr : nrRealPlaces K = 0) (hc : nrComplexPlaces K = 1) :
    (2*rate K-1) * heat K 1 ≤ ‖cst K‖ := by
  have ht : ContinuousAt (fun h : ℝ =>
      (rate K/(1+h)+(rate K-1)/(1+rate K*h))*heat K 1) 0 := by
    fun_prop (disch := norm_num)
  have hb : (rate K/(1+0)+(rate K-1)/(1+rate K*0))*heat K 1 ≤ (cst K).re := by
    apply le_of_tendsto (ht.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0))
    filter_upwards [self_mem_nhdsWithin (s := Ioi (0:ℝ))] with h hh
    exact quotient_bound K hr hc hh
  simp at hb
  linarith [re_le_norm (cst K)]

#print axioms self_dual_residue
end OMA.SelfDualHeat
