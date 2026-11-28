import HeatDecay
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Real.Pi.Bounds

/-! At s=2 the small-x integrand equals H(1/x), by theta inversion.
Compare both halves of the Mellin integral to H(1), then to the residue. -/
noncomputable section
namespace OMA.SmallEndpoint
open Complex NumberField NumberField.InfinitePlace Set MeasureTheory
open ThetaContinuation HeatDecay QuadraticMoment
open scoped ENNReal Topology
variable (K : Type*) [Field K] [NumberField K]

private def w (x : ℝ) := (x:ℂ) * (pair K).f_modif x
private def d (x : ℝ) := (w K x).re

private theorem wi : IntegrableOn (w K) (Ioi 0) := by
  have h := ((pair K).isStrongFEPair_toStrongFEPair.hasMellin 2).1
  change IntegrableOn (fun x : ℝ => (x:ℂ)^((2:ℂ)-1) * (pair K).f_modif x) (Ioi 0) at h
  change IntegrableOn (fun x : ℝ => (x:ℂ) * (pair K).f_modif x) (Ioi 0)
  simpa only [show (2:ℂ)-1 = 1 by norm_num, Complex.cpow_one] using h

private theorem representation : endpoint K = ∫ x in Ioi 0, d K x := by
  have h := completed_agrees K (s := 2) (by norm_num)
  rw [WeakFEPair.Λ] at h
  change (pair K).Λ₀ 2 - (1/2:ℂ)*cst K - (1/(1-2):ℂ)*cst K = _ at h
  have he : (pair K).Λ₀ 2 = arch K 2 * dedekindZeta K 2 - cst K/2 := by
    norm_num at h
    linear_combination h
  have hi : (pair K).Λ₀ 2 = ∫ x in Ioi 0, w K x := by
    simp only [WeakFEPair.Λ₀,mellin,show (2:ℂ)-1 = 1 by norm_num,Complex.cpow_one,smul_eq_mul,w]
  calc endpoint K = ((pair K).Λ₀ 2).re := by rw [he,endpoint,sub_re,div_ofNat_re]
       _ = _ := by rw [hi]; exact (integral_re (wi K)).symm

private theorem small_value (hr : nrRealPlaces K = 0) (hc : nrComplexPlaces K = 1)
    {x : ℝ} (hx : 0 < x) (hx' : x < 1) : d K x = heat K x⁻¹ := by
  have h := (pair K).h_feq x hx
  change DedekindMellin.kernel K (1/x) + cst K = (1*((x^(1:ℝ):ℝ):ℂ)) •
    (DedekindMellin.kernel K x + cst K) at h
  simp only [Real.rpow_one,one_mul,smul_eq_mul,one_div] at h
  have h0 : (x:ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hw : w K x = DedekindMellin.kernel K x⁻¹ := by
    rw [w,WeakFEPair.f_modif,Pi.add_apply,indicator_of_notMem (notMem_Ioi.mpr hx'.le),
      zero_add,indicator_of_mem (mem_Ioo.mpr ⟨hx,hx'⟩)]
    change (x:ℂ)*((DedekindMellin.kernel K x + cst K) -
      (1*((x^(-(1:ℝ)):ℝ):ℂ))*cst K) = _
    rw [Real.rpow_neg_one,ofReal_inv,one_mul,mul_sub,← h,← mul_assoc,mul_inv_cancel₀ h0,one_mul,add_sub_cancel_right]
  rw [d,hw,kernel_eq K hr hc (inv_pos.mpr hx),ofReal_re]

private theorem small_le (hr : nrRealPlaces K = 0) (hc : nrComplexPlaces K = 1)
    (hq : 3 ≤ rate K) {x : ℝ} (hx : x ∈ Ioc (0:ℝ) 1) : d K x ≤ heat K 1 * x^3 := by
  rcases lt_or_eq_of_le hx.2 with hl | rfl
  · rw [small_value K hr hc hx.1 hl,mul_comm]
    have hx1 : 1 ≤ x⁻¹ := (one_le_inv₀ hx.1).mpr hx.2
    refine (contraction K (x := 1) (y := x⁻¹) zero_lt_one hx1).trans
      (mul_le_mul_of_nonneg_right ?_ (heat_nonneg K 1))
    have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hx.1)
    rw [Real.log_inv] at hlog
    rw [show x^3 = Real.exp (Real.log x + Real.log x + Real.log x) by
      rw [Real.exp_add,Real.exp_add,Real.exp_log hx.1]; ring,Real.exp_le_exp]
    linarith [mul_le_mul_of_nonneg_right hq (sub_nonneg.mpr hx1)]
  · simpa [d,w,WeakFEPair.f_modif] using heat_nonneg K 1

private theorem large_le (hr : nrRealPlaces K = 0) (hc : nrComplexPlaces K = 1)
    (hq : 3 ≤ rate K) {x : ℝ} (hx : x ∈ Ioi (1:ℝ)) :
    d K x ≤ (heat K 1 * Real.exp 2) * Real.exp (-2*x) := by
  have hx' : 1 < x := hx
  have hx0 := zero_lt_one.trans hx'
  have hv : d K x = x * heat K x := by
    simp [d,w,WeakFEPair.f_modif,hx',hx'.not_gt,pair,kernel_eq K hr hc hx0]
  rw [hv]
  have hm := contraction K zero_lt_one hx'.le
  have hxexp : x ≤ Real.exp (x-1) := by linarith [Real.add_one_le_exp (x-1)]
  have hf : x * Real.exp (-(rate K*(x-1))) ≤ Real.exp 2 * Real.exp (-2*x) := by
    calc _ ≤ Real.exp (x-1) * Real.exp (-(rate K*(x-1))) :=
               mul_le_mul_of_nonneg_right hxexp (Real.exp_pos _).le
         _ ≤ _ := by rw [← Real.exp_add,← Real.exp_add,Real.exp_le_exp]
                     linarith [mul_le_mul_of_nonneg_right hq (sub_nonneg.mpr hx'.le)]
  calc x*heat K x ≤ x*(Real.exp (-(rate K*(x-1))) * heat K 1) :=
           mul_le_mul_of_nonneg_left hm hx0.le
       _ = heat K 1 * (x*Real.exp (-(rate K*(x-1)))) := by ring
       _ ≤ heat K 1 * (Real.exp 2 * Real.exp (-2*x)) := mul_le_mul_of_nonneg_left hf (heat_nonneg K 1)
       _ = _ := by ring

theorem endpoint_bound (hr : nrRealPlaces K = 0) (hc : nrComplexPlaces K = 1)
    (hq : 3 ≤ rate K) : 16 * endpoint K ≤ 3 * ‖cst K‖ := by
  have hd : IntegrableOn (d K) (Ioi 0) := (wi K).re
  have hsmall : IntegrableOn (d K) (Ioc 0 1) := hd.mono_set Ioc_subset_Ioi_self
  have hlarge := hd.mono_set (Ioi_subset_Ioi (zero_le_one : (0:ℝ) ≤ 1))
  have hpoly : IntegrableOn (fun x : ℝ => heat K 1 * x^3) (Ioc 0 1) :=
    ((show Continuous (fun x : ℝ => heat K 1 * x^3) by fun_prop).continuousOn.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hS := setIntegral_mono_on hsmall hpoly measurableSet_Ioc (fun x hx => small_le K hr hc hq hx)
  have hpow : (∫ x : ℝ in Ioc 0 1, x^3) = 1/4 := by
    rw [← intervalIntegral.integral_of_le (zero_le_one : (0:ℝ) ≤ 1),integral_pow]
    norm_num
  rw [integral_const_mul,hpow] at hS
  have hL := setIntegral_mono_on hlarge
    ((integrableOn_exp_mul_Ioi (by norm_num : (-2:ℝ)<0) 1).const_mul (heat K 1 * Real.exp 2))
    measurableSet_Ioi (fun x hx => large_le K hr hc hq hx)
  rw [integral_const_mul,integral_exp_mul_Ioi (by norm_num : (-2:ℝ)<0),mul_one,
    Real.exp_neg] at hL
  have hE : Real.exp 2 ≠ 0 := (Real.exp_pos _).ne'
  have eq : (heat K 1 * Real.exp 2) * (-(Real.exp 2)⁻¹ / (-2)) = heat K 1 / 2 := by field_simp
  rw [eq] at hL
  rw [representation,← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0:ℝ) ≤ 1),
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hsmall hlarge]
  linarith [four_heat_le_cst K hr hc hq]

theorem small_discriminant_rate (hD : (discr K).natAbs ≤ 4) : 3 ≤ rate K := by
  have hp : 0 < Real.sqrt ((discr K).natAbs : ℝ) := Real.sqrt_pos.mpr
    (by exact_mod_cast Int.natAbs_pos.mpr (discr_ne_zero K))
  have hs : Real.sqrt ((discr K).natAbs : ℝ) ≤ 2 := by
    calc _ ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by exact_mod_cast hD)
         _ = 2 := by norm_num
  rw [rate,le_div_iff₀ hp]
  linarith [Real.pi_gt_three]

theorem small_discriminant_radius (hr : nrRealPlaces K = 0) (hc : nrComplexPlaces K = 1)
    (hD : (discr K).natAbs ≤ 4) {t : ℝ} (ht : |t| ≤ 1/2) :
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ, ENNReal.ofReal (3/2) < p.radius ∧
      ReciprocalRadius.InverseGerm K t p := by
  apply radius_three_halves_of_endpoint K hr hc
  have hm := (norm_nonneg _).trans (moment_bound K hr hc (s := 0) (by norm_num) (by norm_num))
  have hp := norm_pos_iff.mpr (cst_ne K)
  have h := endpoint_bound K hr hc (small_discriminant_rate K hD)
  have hg : 1+(|t|+3/2)^2 ≤ 5 := by
    nlinarith [mul_self_le_mul_self (show (0:ℝ) ≤ |t|+3/2 by positivity) (show |t|+3/2 ≤ 2 by linarith)]
  exact (mul_le_mul_of_nonneg_right hg hm).trans_lt (by linarith)

#print axioms OMA.SmallEndpoint.endpoint_bound
#print axioms OMA.SmallEndpoint.small_discriminant_radius
end OMA.SmallEndpoint
