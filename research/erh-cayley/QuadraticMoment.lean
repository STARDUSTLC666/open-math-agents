import ExactRadius
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Positive Mellin interpolation for imaginary quadratic Dedekind zeta.
The only arithmetic test left by the disk certificate is at s=2. -/
noncomputable section
namespace OMA.QuadraticMoment
open Complex NumberField NumberField.InfinitePlace Set Metric MeasureTheory
open ThetaContinuation ExactRadius
open scoped Topology ENNReal
variable (K : Type*) [Field K] [NumberField K]

private theorem raw_posreal (hr : nrRealPlaces K = 0) (hc : nrComplexPlaces K = 1)
    {x : ℝ} (hx : 0 < x) : ∃ a : ℝ, 0 ≤ a ∧ DedekindMellin.kernel K x = (a:ℂ) := by
  let q := 2 * Real.pi / Real.sqrt ((discr K).natAbs : ℝ)
  let term (n : ℕ) : ℝ := if n=0 then 0 else
    (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) * Real.exp (-(q*x*n))
  have h (n : ℕ) : 0 ≤ term n := by unfold term; split <;> positivity
  refine ⟨2 * ∑' n, term n, mul_nonneg (by norm_num) (tsum_nonneg h), ?_⟩
  rw [ofReal_mul, ofReal_tsum]
  have he := R_ERH_extended_riemann_hypothesis_R1_H1_R1_H2_R1.kernel_expansion_of_signature K hr hc hx
  change DedekindMellin.kernel K x = _ at he
  rw [he,ofReal_ofNat]
  congr 1
  apply tsum_congr
  intro n
  by_cases hn : n=0
  · simp [term,hn]
  · simp only [term,hn,if_false,ofReal_mul,ofReal_natCast,q]

theorem kernel_posreal (hr : nrRealPlaces K = 0) (hc : nrComplexPlaces K = 1)
    {x : ℝ} (hx : 0 < x) : ∃ a : ℝ, 0 ≤ a ∧ (pair K).f_modif x = (a:ℂ) := by
  rcases lt_trichotomy x 1 with h | rfl | h
  · obtain ⟨a,ha,he⟩ := raw_posreal K hr hc (one_div_pos.mpr hx)
    refine ⟨x⁻¹*a,mul_nonneg (inv_nonneg.mpr hx.le) ha,?_⟩
    have hfe := (pair K).h_feq (1/x) (one_div_pos.mpr hx)
    change DedekindMellin.kernel K (1/(1/x)) + cst K =
      (1 * (((1/x) ^ (1:ℝ) : ℝ):ℂ)) • (DedekindMellin.kernel K (1/x) + cst K) at hfe
    rw [one_div] at he
    simp only [one_div,inv_inv,Real.rpow_one,one_mul,smul_eq_mul,ofReal_inv,he] at hfe
    rw [WeakFEPair.f_modif, Pi.add_apply, indicator_of_notMem (notMem_Ioi.mpr h.le), zero_add,
      indicator_of_mem (mem_Ioo.mpr ⟨hx,h⟩)]
    change DedekindMellin.kernel K x + cst K -
      (1 * ((x ^ (-(1:ℝ)) : ℝ):ℂ)) * cst K = _
    rw [hfe,Real.rpow_neg_one,ofReal_inv,ofReal_mul,ofReal_inv]
    ring
  · exact ⟨0,le_rfl,by simp [WeakFEPair.f_modif]⟩
  · obtain ⟨a,ha,he⟩ := raw_posreal K hr hc hx
    refine ⟨a,ha,?_⟩
    simpa [WeakFEPair.f_modif,h,h.not_gt,pair] using he

/-- A real number evaluated using only the absolutely convergent value at 2. -/
def endpoint : ℝ := (arch K 2 * dedekindZeta K 2).re - (cst K).re/2

private theorem ends_two : ((pair K).Λ₀ 2).re = endpoint K := by
  have h := completed_agrees K (s := 2) (by norm_num)
  rw [WeakFEPair.Λ] at h
  change (pair K).Λ₀ 2 - (1/2:ℂ)*cst K - (1/(1-2):ℂ)*cst K = _ at h
  have he : (pair K).Λ₀ 2 = arch K 2 * dedekindZeta K 2 - cst K/2 := by
    norm_num at h
    linear_combination h
  rw [he,endpoint,sub_re,div_ofNat_re]

private theorem ends_neg_one : (pair K).Λ₀ (-1) = (pair K).Λ₀ 2 := by
  have hs : (pair K).symm = pair K := by unfold WeakFEPair.symm pair; congr 1; simp
  have h := (pair K).functional_equation₀ 2
  rw [hs] at h
  change (pair K).Λ₀ ((1:ℂ)-2) = (1:ℂ) • (pair K).Λ₀ 2 at h
  simpa only [show (1:ℂ)-2 = -1 by norm_num,one_smul] using h

private def W (s : ℂ) (x : ℝ) := (x:ℂ) ^ (s-1) * (pair K).f_modif x
private theorem wi (s : ℂ) : IntegrableOn (W K s) (Ioi 0) :=
  ((pair K).isStrongFEPair_toStrongFEPair.hasMellin s).1
private theorem val (s : ℂ) : (pair K).Λ₀ s = ∫ x in Ioi 0, W K s x := rfl
private theorem wn {x : ℝ} (hx : 0 < x) (s : ℂ) :
    ‖W K s x‖ = x^(s.re-1) * ‖(pair K).f_modif x‖ := by
  rw [W,norm_mul,norm_cpow_eq_rpow_re_of_pos hx]; simp

private theorem mass (hr : nrRealPlaces K = 0) (hc : nrComplexPlaces K = 1) (s : ℝ) :
    ∫ x in Ioi 0, ‖W K (s:ℂ) x‖ = ((pair K).Λ₀ (s:ℂ)).re := by
  rw [val]
  refine (setIntegral_congr_fun measurableSet_Ioi (g := fun x => (W K (s:ℂ) x).re) ?_).trans
    (integral_re (wi K (s:ℂ)))
  intro x hx
  obtain ⟨a,ha,he⟩ := kernel_posreal K hr hc hx
  have e : W K (s:ℂ) x = ((x^(s-1) * a : ℝ):ℂ) := by
    simp only [W,he,ofReal_mul,ofReal_cpow hx.le,ofReal_sub,ofReal_one]
  change ‖W K (s:ℂ) x‖ = (W K (s:ℂ) x).re
  rw [e,ofReal_re,Complex.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hx.le _) ha)]

theorem moment_bound (hr : nrRealPlaces K = 0) (hc : nrComplexPlaces K = 1) {s : ℂ}
    (hlo : -1 ≤ s.re) (hhi : s.re ≤ 2) : ‖(pair K).Λ₀ s‖ ≤ endpoint K := by
  let a := (2-s.re)/3
  let b := (s.re+1)/3
  have ha : 0 ≤ a := by unfold a; linarith
  have hb : 0 ≤ b := by unfold b; linarith
  have hab : a+b=1 := by unfold a b; ring
  have hpoint {x : ℝ} (hx : 0 < x) :
      ‖W K s x‖ ≤ a*‖W K (-1) x‖ + b*‖W K 2 x‖ := by
    rw [wn K hx,wn K hx,wn K hx]
    simp only [neg_re,one_re,re_ofNat]
    rw [← mul_assoc,← mul_assoc,← add_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have h := (convexOn_rpow_left hx).2 (x := (-1:ℝ)-1) (y := (2:ℝ)-1)
      (mem_univ _) (mem_univ _) ha hb hab
    simp only [smul_eq_mul] at h
    rwa [show a*(-1-1)+b*(2-1)=s.re-1 by unfold a b;ring] at h
  have h := integral_mono_ae (wi K s).norm (((wi K (-1)).norm.const_mul a).add ((wi K 2).norm.const_mul b))
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall (fun x hx => hpoint hx)))
  change (∫ x in Ioi 0, ‖W K s x‖) ≤ ∫ x in Ioi 0, a*‖W K (-1) x‖+b*‖W K 2 x‖ at h
  rw [integral_add ((wi K (-1)).norm.const_mul _) ((wi K 2).norm.const_mul _),
    integral_const_mul,integral_const_mul] at h
  have hm := mass K hr hc (-1)
  have hp := mass K hr hc 2
  simp only [ofReal_neg,ofReal_one,ofReal_ofNat] at hm hp
  rw [hm,hp,ends_neg_one,← add_mul,hab,one_mul,ends_two] at h
  exact (norm_integral_le_integral_norm (μ := volume.restrict (Ioi 0)) (W K s)).trans h

theorem zero_obstruction (hr : nrRealPlaces K = 0) (hc : nrComplexPlaces K = 1)
    {s : ℂ} (hs : s ∈ zeros K) (hpos : 0 < s.re) :
    ‖cst K‖ ≤ ‖s‖ * ‖s-1‖ * endpoint K := by
  have h1 := zeros_left K hs
  have h0 : s ≠ 0 := by rintro rfl; norm_num at hpos
  have h := (entireReg_eq_reg K h0).symm.trans (show entireReg K s = 0 from hs)
  rw [reg] at h
  have hnum := (div_eq_zero_iff.mp ((mul_eq_zero.mp h).resolve_right (inv_ne_zero (arch_ne K hpos)))).resolve_right h0
  have e : s*(s-1)*(pair K).Λ₀ s = -cst K := eq_neg_of_add_eq_zero_left hnum
  have hn := congrArg (fun z : ℂ => ‖z‖) e
  simp only [norm_mul,norm_neg] at hn
  rw [← hn]
  exact mul_le_mul_of_nonneg_left (moment_bound K hr hc (by linarith) (by linarith))
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- A single inequality at s=2 certifies the full circular disk (not merely
sampled points). No arithmetic verification of this inequality is assumed. -/
theorem radius_three_halves_of_endpoint (hr : nrRealPlaces K = 0) (hc : nrComplexPlaces K = 1)
    (t : ℝ) (test : (1+(|t|+3/2)^2) * endpoint K < ‖cst K‖) :
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ, ENNReal.ofReal (3/2) < p.radius ∧
      ReciprocalRadius.InverseGerm K t p := by
  have md := moment_bound K hr hc (s := 0) (by norm_num) (by norm_num)
  have hM := (norm_nonneg _).trans md
  have hd : 3/2 < zeroDistance K t := by
    obtain ⟨z,hz,he⟩ := nearest K t
    rw [he]
    by_contra! hdist
    rw [dist_eq_norm] at hdist
    have hRe := (re_le_norm (ExactRadius.center t-z)).trans hdist
    change 2-z.re ≤ 3/2 at hRe
    have hpos : 0 < z.re := by linarith
    have h1 := zeros_left K hz
    have him := (abs_im_le_norm (ExactRadius.center t-z)).trans hdist
    change |t-z.im| ≤ 3/2 at him
    have him' : |z.im| ≤ |t|+3/2 := by
      calc |z.im| = |t+(z.im-t)| := by rw [add_sub_cancel]
           _ ≤ |t|+|z.im-t| := abs_add_le _ _
           _ ≤ _ := add_le_add_right (by rwa [abs_sub_comm z.im t]) _
    have hsq := (sq_le_sq₀ (abs_nonneg z.im) (by positivity)).mpr him'
    rw [sq_abs] at hsq
    have hA : ‖z‖^2 ≤ 1+(|t|+3/2)^2 := by
      rw [Complex.sq_norm,normSq_apply]; nlinarith [mul_self_le_mul_self hpos.le h1.le]
    have hB : ‖z-1‖^2 ≤ 1+(|t|+3/2)^2 := by
      rw [Complex.sq_norm,normSq_apply]
      simp only [sub_re,one_re,sub_im,one_im,sub_zero]
      nlinarith [mul_self_le_mul_self (by linarith : 0 ≤ 1-z.re) (by linarith : 1-z.re ≤ 1)]
    have hAB : ‖z‖*‖z-1‖ ≤ 1+(|t|+3/2)^2 := by nlinarith [sq_nonneg (‖z‖-‖z-1‖)]
    exact test.not_ge ((zero_obstruction K hr hc hz hpos).trans (mul_le_mul_of_nonneg_right hAB hM))
  obtain ⟨p,hp,hg⟩ := AllFieldRadius.all_fields_radius_gt_one K t
  refine ⟨p,?_,hg⟩
  rw [radius_eq_zeroDistance K t (zero_lt_one.trans hp) hg]
  exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hd

#print axioms OMA.QuadraticMoment.kernel_posreal
#print axioms OMA.QuadraticMoment.moment_bound
#print axioms OMA.QuadraticMoment.zero_obstruction
#print axioms OMA.QuadraticMoment.radius_three_halves_of_endpoint
end OMA.QuadraticMoment
