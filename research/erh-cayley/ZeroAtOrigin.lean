import ExactRadius

/-! With at least two infinite places, the reciprocal archimedean factor
still vanishes after division by s. Thus zero obstructs every inverse disk. -/
noncomputable section
namespace OMA.ZeroAtOrigin
open Complex NumberField NumberField.InfinitePlace Metric
open ExactRadius ThetaContinuation

private theorem double_zero {f g : ℂ → ℂ} (hf : DifferentiableAt ℂ f 0)
    (hg : DifferentiableAt ℂ g 0) (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (r c : ℕ) (h : 2 ≤ r+c) :
    f 0 ^ r * g 0 ^ c = 0 ∧
      HasDerivAt (fun z => f z ^ r * g z ^ c) 0 0 := by
  have hd := (hf.hasDerivAt.fun_pow r).fun_mul (hg.hasDerivAt.fun_pow c)
  constructor
  · rw [hf0, hg0]
    by_cases hr : r = 0
    · have hc : c ≠ 0 := by omega
      simp [hr, hc]
    · simp [hr]
  · rw [hf0, hg0] at hd
    rcases eq_or_ne r 0 with rfl | hr
    · have hc : c-1 ≠ 0 := by omega
      simpa [hc] using hd
    · rcases eq_or_ne c 0 with rfl | hc
      · have hr' : r-1 ≠ 0 := by omega
        simpa [hr'] using hd
      · simpa [hr, hc] using hd

variable (K : Type*) [Field K] [NumberField K]

theorem origin_mem (h : 2 ≤ nrRealPlaces K + nrComplexPlaces K) : (0:ℂ) ∈ zeros K := by
  let f := fun z : ℂ => (Gammaℝ z)⁻¹
  let g := fun z : ℂ => (Gammaℂ z)⁻¹
  let A := fun z : ℂ => (exp (z*(Real.log (discr K).natAbs/2 : ℝ)))⁻¹
  have hf : f 0 = 0 := by simp [f, Gammaℝ_def, Complex.Gamma_zero]
  have hg : g 0 = 0 := by simp [g, Gammaℂ_def, Complex.Gamma_zero]
  obtain ⟨hv, hd⟩ := double_zero (differentiable_Gammaℝ_inv 0) (differentiable_Gammaℂ_inv 0)
    hf hg (nrRealPlaces K) (nrComplexPlaces K) h
  have hA : DifferentiableAt ℂ A 0 := by dsimp [A]; fun_prop (disch := simp)
  have he : (fun z => (arch K z)⁻¹) = fun z => A z * (f z ^ nrRealPlaces K * g z ^ nrComplexPlaces K) := by
    funext z
    simp only [arch, A, f, g, mul_inv, ← inv_pow]; ring
  have hder : deriv (fun z => (arch K z)⁻¹) 0 = 0 := by
    rw [he]
    have hh := (hA.hasDerivAt.fun_mul hd).deriv
    simpa only [hv, mul_zero, add_zero, zero_mul] using hh
  change entireReg K 0 = 0
  rw [entireReg, dslope_same, hder, mul_zero]

theorem radius_le_origin_distance (h : 2 ≤ nrRealPlaces K + nrComplexPlaces K) (t : ℝ)
    {p : FormalMultilinearSeries ℂ ℂ ℂ} (hp : 0 < p.radius)
    (hg : ReciprocalRadius.InverseGerm K t p) :
    p.radius ≤ ENNReal.ofReal (Real.sqrt (4+t^2)) := by
  have hd : zeroDistance K t ≤ dist (center t) 0 := infDist_le_dist_of_mem (origin_mem K h)
  have hs : dist (center t) 0 ^ 2 = 4+t^2 := by
    rw [dist_eq_norm, sub_zero, Complex.sq_norm, normSq_apply]
    change 2*2+t*t = 4+t^2
    ring
  rw [radius_eq_zeroDistance K t hp hg, ← hs, Real.sqrt_sq dist_nonneg]
  exact ENNReal.ofReal_le_ofReal hd

theorem degree_ge_three_radius (h : 3 ≤ Module.finrank ℚ K) (t : ℝ)
    {p : FormalMultilinearSeries ℂ ℂ ℂ} (hp : 0 < p.radius)
    (hg : ReciprocalRadius.InverseGerm K t p) :
    p.radius ≤ ENNReal.ofReal (Real.sqrt (4+t^2)) := by
  apply radius_le_origin_distance K _ t hp hg
  have := card_add_two_mul_card_eq_rank K
  omega

#print axioms origin_mem
#print axioms radius_le_origin_distance
#print axioms degree_ge_three_radius
end OMA.ZeroAtOrigin
