import GeneralSlope
import DiskGeometry

/-! Critical-strip estimates for all signatures. The factor 1+1/x results
from folding the Mellin integral using the theta functional equation. -/
noncomputable section
namespace OMA.GeneralStrip
open Complex NumberField MeasureTheory Set Metric
open GeneralHeat GeneralSlope RadialProfile ExactRadius ThetaContinuation
variable (K : Type*) [Field K] [NumberField K]

private def weight (s : ℂ) (x : ℝ) := ‖(x:ℂ)^(s-1) * (pair K).f_modif x‖

private theorem weight_int (s : ℂ) : IntegrableOn (weight K s) (Ioi 0) := by
  have h : IntegrableOn (fun x : ℝ => (x:ℂ)^(s-1)*(pair K).f_modif x) (Ioi 0) :=
    ((pair K).isStrongFEPair_toStrongFEPair.hasMellin s).1
  exact h.norm

private theorem weight_eq (s : ℂ) {x : ℝ} (hx : 0 < x) :
    weight K s x = x^(s.re-1) * ‖(pair K).f_modif x‖ := by
  rw [weight, norm_mul, norm_cpow_eq_rpow_re_of_pos hx]; simp

private theorem inverse_weight (s : ℂ) {x : ℝ} (hx : 0 < x) :
    |-(x^2)⁻¹| • weight K s x⁻¹ = weight K (1-s) x := by
  have hsym : (pair K).g_modif = (pair K).f_modif := by simp [WeakFEPair.g_modif, WeakFEPair.f_modif, pair]
  have hf := (pair K).hf_modif_FE x hx
  rw [hsym, one_div] at hf
  change (pair K).f_modif x⁻¹ = (1*((x^(1:ℝ):ℝ):ℂ)) • (pair K).f_modif x at hf
  rw [Real.rpow_one, one_mul, smul_eq_mul] at hf
  rw [smul_eq_mul, abs_neg, abs_of_nonneg (by positivity), weight_eq K s (inv_pos.mpr hx),
    weight_eq K (1-s) hx, hf, norm_mul, Complex.norm_of_nonneg hx.le, Real.inv_rpow hx.le,
    ← Real.rpow_neg hx.le]
  simp only [sub_re, one_re]
  rw [show (x^2)⁻¹ = x^(-(2:ℝ)) by rw [Real.rpow_neg hx.le, Real.rpow_two]]
  calc _ = (x^(-(2:ℝ))*x^(-(s.re-1))*x^(1:ℝ))*‖(pair K).f_modif x‖ := by rw [Real.rpow_one]; ring
       _ = _ := by rw [← Real.rpow_add hx, ← Real.rpow_add hx]; congr 2; ring

private theorem fold (s : ℂ) :
    (∫ x in Ioi 0, weight K s x) = ∫ x in Ioi 1, weight K s x + weight K (1-s) x := by
  have himage : (fun x : ℝ => x⁻¹) '' Ioi 1 = Ioo 0 1 := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩; exact ⟨inv_pos.mpr (zero_lt_one.trans hx), inv_lt_one_of_one_lt₀ hx⟩
    · intro hy; exact ⟨y⁻¹, (one_lt_inv₀ hy.1).mpr hy.2, inv_inv y⟩
  have hsub := integral_image_eq_integral_abs_deriv_smul (measurableSet_Ioi (a := (1:ℝ)))
    (fun x hx => (hasDerivAt_inv (zero_lt_one.trans hx).ne').hasDerivWithinAt)
    inv_injective.injOn (weight K s)
  rw [himage] at hsub
  have hsmall : (∫ x in Ioc 0 1, weight K s x) = ∫ x in Ioi 1, weight K (1-s) x := by
    rw [integral_Ioc_eq_integral_Ioo, hsub]
    exact setIntegral_congr_fun measurableSet_Ioi (fun x hx => inverse_weight K s (zero_lt_one.trans hx))
  have hbig (u : ℂ) := (weight_int K u).mono_set (Ioi_subset_Ioi (zero_le_one : (0:ℝ) ≤ 1))
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0:ℝ) ≤ 1), setIntegral_union Ioc_disjoint_Ioi_same
    measurableSet_Ioi ((weight_int K s).mono_set Ioc_subset_Ioi_self) (hbig s), hsmall,
    integral_add (hbig s) (hbig (1-s)), add_comm]

theorem strip_majorant {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1) {g : ℝ → ℝ}
    (hg : IntegrableOn g (Ioi 1)) (hbound : ∀ x, 1 < x → (1+x⁻¹)*heat K x ≤ g x) :
    ‖(pair K).Λ₀ s‖ ≤ ∫ x in Ioi 1, g x := by
  have hW : ‖(pair K).Λ₀ s‖ ≤ ∫ x in Ioi 0, weight K s x :=
    norm_integral_le_integral_norm (μ := volume.restrict (Ioi 0)) _
  rw [fold K s] at hW
  have hbig (u : ℂ) := (weight_int K u).mono_set (Ioi_subset_Ioi (zero_le_one : (0:ℝ) ≤ 1))
  apply hW.trans (setIntegral_mono_on ((hbig s).add (hbig (1-s))) hg measurableSet_Ioi ?_)
  intro x hx
  change 1 < x at hx
  have hx0 := zero_lt_one.trans hx
  have hval (u : ℂ) : weight K u x = x^(u.re-1)*heat K x := by
    rw [weight_eq K u hx0]
    simp [WeakFEPair.f_modif, hx, hx.not_gt, pair, kernel_eq K hx0, heat_nonneg K x]
  change weight K s x + weight K (1-s) x ≤ _
  rw [hval s, hval (1-s), ← add_mul]
  apply le_trans (mul_le_mul_of_nonneg_right _ (heat_nonneg K _)) (hbound x hx)
  have hpow (e : ℝ) (he : e ≤ 0) : x^e ≤ 1 := by simpa using Real.rpow_le_rpow_of_exponent_le hx.le he
  have h2 : (1-s).re-1 ≤ 0 := by rw [sub_re, one_re]; linarith
  have hprod : x^(s.re-1)*x^((1-s).re-1) = x⁻¹ := by
    rw [← Real.rpow_add hx0, sub_re, one_re, show s.re-1+(1-s.re-1) = -1 by ring, Real.rpow_neg_one]
  nlinarith [mul_nonneg (sub_nonneg.mpr (hpow _ (sub_nonpos.mpr h1))) (sub_nonneg.mpr (hpow _ h2))]

theorem heat_le_power {x : ℝ} (hx : 1 ≤ x) :
    heat K x ≤ heat K 1 * x^(-slopeRate K) := by
  have hx0 := zero_lt_one.trans_le hx
  have h := contraction K zero_lt_one hx
  rw [Real.one_rpow] at h
  rw [mul_comm]
  apply h.trans (mul_le_mul_of_nonneg_right _ (heat_nonneg K _))
  rw [Real.rpow_def_of_pos hx0 (-(slopeRate K)), Real.exp_le_exp, Real.rpow_def_of_pos hx0]
  have hb := Real.add_one_le_exp (Real.log x * exponent K)
  have hh := mul_le_mul_of_nonneg_left hb (GeneralHeat.rate_pos K).le
  unfold slopeRate
  linarith only [hh, show GeneralHeat.rate K * (Real.log x * exponent K+1) =
    Real.log x*(GeneralHeat.rate K*exponent K)+GeneralHeat.rate K by ring,
    show GeneralHeat.rate K*(Real.exp (Real.log x * exponent K)-1) =
    GeneralHeat.rate K*Real.exp (Real.log x * exponent K)-GeneralHeat.rate K by ring]

theorem power_moment (hq : 1 < slopeRate K) {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1) :
    ‖(pair K).Λ₀ s‖ ≤ heat K 1 * (1/(slopeRate K-1) + 1/slopeRate K) := by
  let q := slopeRate K
  have hq' : 1 < q := hq
  have ha : -q < -1 := by linarith
  have hb : -q-1 < -1 := by linarith
  have hi (e : ℝ) (he : e < -1) : IntegrableOn (fun x : ℝ => x^e) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt he zero_lt_one
  let f := fun x : ℝ => x^(-q) + x^(-q-1)
  have hI : IntegrableOn f (Ioi 1) := (hi _ ha).add (hi _ hb)
  have h := strip_majorant K h0 h1 (hI.const_mul (heat K 1)) (fun x hx => by
    have hx0 := zero_lt_one.trans hx
    have hmul := mul_le_mul_of_nonneg_left (heat_le_power K hx.le)
      (show 0 ≤ 1+x⁻¹ by positivity)
    have hprod : x⁻¹*x^(-q) = x^(-q-1) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hx0]; congr 1; ring
    change (1+x⁻¹)*heat K x ≤ heat K 1 * f x
    calc _ ≤ (1+x⁻¹)*(heat K 1*x^(-q)) := hmul
         _ = _ := by dsimp [f]; rw [← hprod]; ring)
  have hval : (∫ x in Ioi 1, f x) = 1/(q-1)+1/q := by
    dsimp [f]; rw [integral_add (hi _ ha) (hi _ hb),
      integral_Ioi_rpow_of_lt ha zero_lt_one, integral_Ioi_rpow_of_lt hb zero_lt_one,
      Real.one_rpow, Real.one_rpow, show -q+1 = -(q-1) by ring,
      show -q-1+1 = -q by ring]; simp
    rw [show 1-q = -(q-1) by ring, neg_div_neg_eq, one_div]
  rwa [integral_const_mul, hval] at h

theorem product_at_zero {s : ℂ} (hz : s ∈ zeros K) (h0 : 0 < s.re) :
    ‖s‖ * ‖s-1‖ * ‖(pair K).Λ₀ s‖ = ‖cst K‖ := by
  have hn : s ≠ 0 := by rintro rfl; norm_num at h0
  have e := (entireReg_eq_reg K hn).symm.trans (show entireReg K s = 0 from hz)
  rw [reg] at e
  have he := (div_eq_zero_iff.mp ((mul_eq_zero.mp e).resolve_right (inv_ne_zero (arch_ne K h0)))).resolve_right hn
  have he' := congrArg (fun z : ℂ => ‖z‖)
    (eq_neg_of_add_eq_zero_left he : s*(s-1)*(pair K).Λ₀ s = -cst K)
  simpa only [norm_mul, norm_neg] using he'

theorem zero_product (hq : 1 < slopeRate K) {s : ℂ} (hz : s ∈ zeros K) (h0 : 0 < s.re) :
    slopeRate K * (slopeRate K - 1) ≤ ‖s‖ * ‖s-1‖ := by
  let q := slopeRate K
  have hq' : 1 < q := hq
  let P := ‖s‖*‖s-1‖
  have hB := power_moment K hq h0.le (zeros_left K hz).le
  have hp := mul_le_mul_of_nonneg_left hB (mul_nonneg (norm_nonneg s) (norm_nonneg (s-1)))
  rw [product_at_zero K hz h0] at hp
  change ‖cst K‖ ≤ P*(heat K 1*(1/(q-1)+1/q)) at hp
  have hheat : 0 < heat K 1 := by
    by_contra! h
    rw [le_antisymm h (heat_nonneg K 1), zero_mul, mul_zero] at hp
    exact (norm_pos_iff.mpr (cst_ne K)).not_ge hp
  have hc := (self_dual_residue K).trans hp
  change (2*q-1)*heat K 1 ≤ P*(heat K 1*(1/(q-1)+1/q)) at hc
  have he : 1/(q-1)+1/q = (2*q-1)/(q*(q-1)) := by
    field_simp [show q ≠ 0 by linarith, show q-1 ≠ 0 by linarith]; ring
  rw [he, show P*(heat K 1*((2*q-1)/(q*(q-1)))) =
    (P*(2*q-1)/(q*(q-1)))*heat K 1 by ring] at hc
  have h := (le_div_iff₀ (mul_pos (by linarith) (by linarith) : 0 < q*(q-1))).mp
    ((mul_le_mul_iff_left₀ hheat).mp hc)
  apply (mul_le_mul_iff_left₀ (by linarith : 0 < 2*q-1)).mp
  change q*(q-1)*(2*q-1) ≤ P*(2*q-1)
  rwa [mul_comm (q*(q-1))]

theorem height_of_product {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    ‖s‖ * ‖s-1‖ < s.im^2 + 1/2 := by
  have hA : ‖s‖^2 = s.re^2+s.im^2 := by rw [Complex.sq_norm, normSq_apply]; ring
  have hB : ‖s-1‖^2 = (s.re-1)^2+s.im^2 := by rw [Complex.sq_norm, normSq_apply]; simp [sq]
  nlinarith [sq_nonneg (‖s‖-‖s-1‖), mul_pos h0 (sub_pos.mpr h1)]

theorem zero_height (hq : 1 < slopeRate K) {s : ℂ} (hz : s ∈ zeros K) (h0 : 0 < s.re) :
    slopeRate K * (slopeRate K-1) - 1/2 < s.im^2 := by
  linarith [zero_product K hq hz h0, height_of_product h0 (zeros_left K hz)]

theorem radius_from_height {T t : ℝ} (hT : 0 ≤ T)
    (hz : ∀ z ∈ zeros K, 0 < z.re → T^2 < z.im^2)
    (ht : |t| ≤ T) (hgap : (3/2:ℝ)^2 ≤ 1+(T-|t|)^2) :
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ, ENNReal.ofReal (3/2) < p.radius ∧
      ReciprocalRadius.InverseGerm K t p := by
  have hv (z : ℂ) (h : z ∈ zeros K) (hp : 0 < z.re) : T < |z.im| := by
    apply (sq_lt_sq₀ hT (abs_nonneg _)).mp
    rw [sq_abs]; exact hz z h hp
  have hd : 3/2 < zeroDistance K t := by
    rcases DiskGeometry.distance_of_zero_height K hv ht with h | h
    · linarith
    · exact (sq_lt_sq₀ (by norm_num) (by linarith [distance_gt_one K t])).mp (hgap.trans_lt h)
  obtain ⟨p, hp, hg⟩ := AllFieldRadius.all_fields_radius_gt_one K t
  refine ⟨p, ?_, hg⟩
  rw [radius_eq_zeroDistance K t (zero_lt_one.trans hp) hg]
  exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hd

/-- A simple uniform window with no restriction on the signature. -/
theorem root_discriminant_three {t : ℝ} (ht : |t| ≤ 1/5)
    (hD : ((discr K).natAbs : ℝ)^(1/(degree K)) ≤ 3) :
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ, ENNReal.ofReal (3/2) < p.radius ∧
      ReciprocalRadius.InverseGerm K t p := by
  have hpos : 0 < ((discr K).natAbs : ℝ)^(1/(degree K)) :=
    Real.rpow_pos_of_pos (by exact_mod_cast Int.natAbs_pos.mpr (discr_ne_zero K)) _
  have hq : 209/100 ≤ slopeRate K := by
    rw [slopeRate_eq, le_div_iff₀ hpos]
    linarith [Real.pi_gt_d2]
  have hr : (209/100)*((209/100)-1) ≤ slopeRate K*(slopeRate K-1) :=
    mul_le_mul hq (by linarith) (by norm_num) (by linarith)
  refine radius_from_height K (T := 4/3) (by norm_num) ?_ (by linarith) ?_
  · intro z hz hp
    linarith [zero_height K (by linarith) hz hp]
  · have hmargin : 17/15 ≤ 4/3-|t| := by linarith
    have := (sq_le_sq₀ (by norm_num) (by linarith : 0 ≤ 4/3-|t|)).mpr hmargin
    linarith

#print axioms strip_majorant
#print axioms heat_le_power
#print axioms power_moment
#print axioms zero_product
#print axioms zero_height
#print axioms radius_from_height
#print axioms root_discriminant_three
end OMA.GeneralStrip
