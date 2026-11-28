import GeneralStrip
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! The folded Mellin integral with its phase. On the right half of the
critical strip the imaginary part has an extra factor 2 Re(s) - 1. -/
noncomputable section
namespace OMA.FoldedPhase

open Complex NumberField MeasureTheory Set
open GeneralHeat ThetaContinuation
variable (K : Type*) [Field K] [NumberField K]

def integrand (s : ℂ) (x : ℝ) := (x:ℂ)^(s-1) * (pair K).f_modif x
theorem integrand_int (s : ℂ) : IntegrableOn (integrand K s) (Ioi 0) :=
  ((pair K).isStrongFEPair_toStrongFEPair.hasMellin s).1

private theorem invert_integrand (s : ℂ) {x : ℝ} (hx : 0 < x) :
    |-(x^2)⁻¹| • integrand K s x⁻¹ = integrand K (1-s) x := by
  have hsym : (pair K).g_modif = (pair K).f_modif := by
    simp [WeakFEPair.g_modif, WeakFEPair.f_modif, pair]
  have hf := (pair K).hf_modif_FE x hx
  rw [hsym, one_div] at hf
  change (pair K).f_modif x⁻¹ = (1*((x^(1:ℝ):ℝ):ℂ)) • (pair K).f_modif x at hf
  rw [Real.rpow_one, one_mul, smul_eq_mul] at hf
  have hxC := ofReal_ne_zero.mpr hx.ne'
  have harg : (x:ℂ).arg ≠ Real.pi := by
    rw [arg_ofReal_of_nonneg hx.le]; exact Real.pi_ne_zero.symm
  rw [integrand, integrand, abs_neg, abs_of_nonneg (by positivity), real_smul,
    ofReal_inv, ofReal_pow, ofReal_inv, inv_cpow _ _ harg, ← cpow_neg, hf]
  calc _ = (x:ℂ)^(-1:ℂ) * (x:ℂ)^(-(s-1)) * (pair K).f_modif x := by
              rw [cpow_neg_one]; field_simp [hxC]
       _ = _ := by rw [← cpow_add _ _ hxC]; congr 2; ring

theorem folded (s : ℂ) : (pair K).Λ₀ s =
    ∫ x in Ioi (1:ℝ), integrand K s x + integrand K (1-s) x := by
  have himage : (fun x : ℝ => x⁻¹) '' Ioi 1 = Ioo 0 1 := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩; exact ⟨inv_pos.mpr (zero_lt_one.trans hx), inv_lt_one_of_one_lt₀ hx⟩
    · intro hy; exact ⟨y⁻¹, (one_lt_inv₀ hy.1).mpr hy.2, inv_inv y⟩
  have hc := integral_image_eq_integral_abs_deriv_smul (measurableSet_Ioi (a := (1:ℝ)))
    (fun x hx => (hasDerivAt_inv (zero_lt_one.trans hx).ne').hasDerivWithinAt)
    inv_injective.injOn (integrand K s)
  rw [himage] at hc
  have hsub : (∫ x in Ioc 0 1, integrand K s x) = ∫ x in Ioi 1, integrand K (1-s) x := by
    rw [integral_Ioc_eq_integral_Ioo, hc]
    exact setIntegral_congr_fun measurableSet_Ioi (fun x hx => invert_integrand K s (zero_lt_one.trans hx))
  have hi (w : ℂ) := (integrand_int K w).mono_set (Ioi_subset_Ioi (zero_le_one : (0:ℝ) ≤ 1))
  change (∫ x in Ioi 0, integrand K s x) = _
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0:ℝ) ≤ 1),
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      ((integrand_int K s).mono_set Ioc_subset_Ioi_self) (hi s), hsub,
    integral_add (hi s) (hi (1-s)), add_comm]

private theorem im_large (s : ℂ) {x : ℝ} (hx : 1 < x) :
    (integrand K s x).im = x^(s.re-1)*Real.sin (Real.log x*s.im)*heat K x := by
  have hx0 := zero_lt_one.trans hx
  have hker : (pair K).f_modif x = (heat K x : ℂ) := by
    simp [WeakFEPair.f_modif, hx, hx.not_gt, pair, kernel_eq K hx0]
  rw [integrand, hker, mul_im, ofReal_im, mul_zero, zero_add, ofReal_re,
    cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx0.ne'), ← ofReal_log hx0.le, exp_im,
    Real.rpow_def_of_pos hx0]
  simp [mul_re, mul_im]

def phaseIntegrand (s : ℂ) (x : ℝ) : ℝ :=
  (x^(s.re-1)-x^(-s.re))*Real.sin (Real.log x*s.im)*heat K x

private theorem phase_eq (s : ℂ) {x : ℝ} (hx : 1 < x) :
    (integrand K s x + integrand K (1-s) x).im = phaseIntegrand K s x := by
  rw [add_im, im_large K s hx, im_large K (1-s) hx, sub_re, sub_im, one_re, one_im,
    zero_sub, mul_neg, Real.sin_neg, show 1-s.re-1 = -s.re by ring, phaseIntegrand]
  ring

theorem imaginary_folded (s : ℂ) : ((pair K).Λ₀ s).im = ∫ x in Ioi 1, phaseIntegrand K s x := by
  have hi (w : ℂ) := (integrand_int K w).mono_set (Ioi_subset_Ioi (zero_le_one : (0:ℝ) ≤ 1))
  rw [folded]
  calc _ = ∫ x in Ioi 1, (integrand K s x+integrand K (1-s) x).im :=
              (integral_im ((hi s).add (hi (1-s)))).symm
       _ = _ := setIntegral_congr_fun measurableSet_Ioi (fun _ hx => phase_eq K s hx)

theorem phase_integrable (s : ℂ) : IntegrableOn (phaseIntegrand K s) (Ioi 1) := by
  have hi (w : ℂ) := (integrand_int K w).mono_set (Ioi_subset_Ioi (zero_le_one : (0:ℝ) ≤ 1))
  have h : IntegrableOn (fun x => (integrand K s x+integrand K (1-s) x).im) (Ioi 1) :=
    ((hi s).add (hi (1-s))).im
  exact h.congr_fun (fun _ hx => phase_eq K s hx) measurableSet_Ioi

private theorem sinh_scale {u b : ℝ} (hu : 0 ≤ u) (hb : 0 ≤ b) (hb' : b ≤ 1) :
    Real.sinh (b*u) ≤ b * Real.sinh u := by
  have hc : ConvexOn ℝ (Ici 0) Real.sinh := by
    apply convexOn_of_deriv2_nonneg' (convex_Ici _) Real.differentiable_sinh.differentiableOn
    · rw [Real.deriv_sinh]; exact Real.differentiable_cosh.differentiableOn
    · intro y hy
      change 0 ≤ deriv (deriv Real.sinh) y
      rw [Real.deriv_sinh, Real.deriv_cosh]
      exact Real.sinh_nonneg_iff.mpr hy
  have h := hc.2 (x := (0:ℝ)) (y := u) (mem_Ici.mpr le_rfl) hu
    (sub_nonneg.mpr hb') hb (sub_add_cancel 1 b)
  simpa only [smul_eq_mul, mul_zero, zero_add, Real.sinh_zero] using h

theorem power_gap {x σ : ℝ} (hx : 1 ≤ x) (hlo : 1/2 ≤ σ) (hhi : σ ≤ 1) :
    0 ≤ x^(σ-1) - x^(-σ) ∧ x^(σ-1)-x^(-σ) ≤ (2*σ-1)*(1-x⁻¹) := by
  have hx0 := zero_lt_one.trans_le hx
  refine ⟨sub_nonneg.mpr (Real.rpow_le_rpow_of_exponent_le hx (by linarith)), ?_⟩
  let u := Real.log x/2
  let b := 2*σ-1
  have hu : 0 ≤ u := div_nonneg (Real.log_nonneg hx) (by norm_num)
  have hb : 0 ≤ b := by dsimp [b]; linarith
  have hb' : b ≤ 1 := by dsimp [b]; linarith
  have he (a : ℝ) : Real.exp (-u) * (2 * Real.sinh (a*u)) =
      Real.exp (-u+a*u)-Real.exp (-u+ -(a*u)) := by
    rw [Real.sinh_eq, mul_div_cancel₀ _ (by norm_num : (2:ℝ) ≠ 0),
      mul_sub, ← Real.exp_add, ← Real.exp_add]
  have heB : Real.exp (-u)*(2*Real.sinh (b*u)) = x^(σ-1)-x^(-σ) := by
    rw [he, Real.rpow_def_of_pos hx0, Real.rpow_def_of_pos hx0]
    dsimp [u,b]; ring_nf
  have he1 : Real.exp (-u)*(2*Real.sinh u) = 1-x⁻¹ := by
    simpa only [one_mul, neg_add_cancel, Real.exp_zero,
      show -u + -u = -(Real.log x) by dsimp [u]; ring, Real.exp_neg, Real.exp_log hx0] using he 1
  rw [← heB, ← he1]
  change _ ≤ b*_
  have h := mul_le_mul_of_nonneg_left (sinh_scale hu hb hb') (mul_nonneg (Real.exp_pos (-u)).le zero_le_two)
  linarith only [h, show (Real.exp (-u)*2)*(b*Real.sinh u) = b*(Real.exp (-u)*(2*Real.sinh u)) by ring,
    show (Real.exp (-u)*2)*Real.sinh (b*u) = Real.exp (-u)*(2*Real.sinh (b*u)) by ring]

#print axioms folded
#print axioms imaginary_folded
#print axioms phase_integrable
#print axioms power_gap
end OMA.FoldedPhase
