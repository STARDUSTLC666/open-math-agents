import AllFieldRadius
import Mathlib.Analysis.Complex.RemovableSingularity

/-! The exact radius for each number field. The completed theta expression
has an apparent division by s; take the divided difference of the reciprocal
archimedean factor so the extension also has the correct value at zero. -/

noncomputable section
namespace OMA.ExactRadius
open Complex NumberField NumberField.InfinitePlace Filter Set Metric
open OMA.EulerBoundary OMA.ThetaContinuation OMA.AllFieldRadius
open scoped Topology NNReal ENNReal

variable (K : Type*) [Field K] [NumberField K]

private theorem arch_zero_of_gamma {s : ℂ} (hs : Gammaℝ s = 0) : arch K s = 0 := by
  have hc : Gammaℂ s = 0 := by rw [← Gammaℝ_mul_Gammaℝ_add_one, hs, zero_mul]
  have hn := card_add_two_mul_card_eq_rank K
  have hp := Module.finrank_pos (R := ℚ) (M := K)
  by_cases h : nrRealPlaces K = 0
  · have h' : nrComplexPlaces K ≠ 0 := by omega
    rw [arch, hc, zero_pow h', mul_zero]
  · rw [arch, hs, zero_pow h, mul_zero, zero_mul]

private theorem inv_arch_zero : (arch K 0)⁻¹ = 0 := by
  rw [arch_zero_of_gamma K (Gammaℝ_eq_zero_iff.mpr ⟨0, by simp⟩), inv_zero]

def entireReg (s : ℂ) : ℂ := (s * (s-1) * (pair K).Λ₀ s + cst K) *
  dslope (fun z => (arch K z)⁻¹) 0 s

theorem entireReg_diff : Differentiable ℂ (entireReg K) := by
  have h : Differentiable ℂ (dslope (fun z => (arch K z)⁻¹) 0) :=
    differentiableOn_univ.mp ((differentiableOn_dslope (univ_mem : (univ : Set ℂ) ∈ 𝓝 0)).mpr
      (analytic_arch_inv K).differentiableOn)
  exact ((((differentiable_id.mul (differentiable_id.sub_const (1:ℂ))).mul
    (pair K).differentiable_Λ₀).add_const (cst K)).mul h)

theorem entireReg_eq_reg {s : ℂ} (hs : s ≠ 0) : entireReg K s = reg K s := by
  have he : s * dslope (fun z => (arch K z)⁻¹) 0 s = (arch K s)⁻¹ := by
    simpa only [sub_zero, smul_eq_mul] using sub_smul_dslope_of_zero (f := fun z => (arch K z)⁻¹)
      (inv_arch_zero K) s
  have h' : dslope (fun z => (arch K z)⁻¹) 0 s = (arch K s)⁻¹ / s :=
    (eq_div_iff hs).mpr ((mul_comm _ _).trans he)
  rw [entireReg, reg, h', div_eq_mul_inv, div_eq_mul_inv]
  ring

def zeros : Set ℂ := {s | entireReg K s = 0}

theorem zeros_closed : IsClosed (zeros K) :=
  isClosed_eq (entireReg_diff K).continuous continuous_const

theorem neg_two_mem : (-2 : ℂ) ∈ zeros K := by
  change entireReg K (-2) = 0
  rw [entireReg_eq_reg K (by norm_num), reg, arch_zero_of_gamma K
    (Gammaℝ_eq_zero_iff.mpr ⟨1, by norm_num⟩), inv_zero, mul_zero]

abbrev center := pt 2
def zeroDistance (t : ℝ) := infDist (center t) (zeros K)

theorem nearest (t : ℝ) : ∃ z ∈ zeros K, zeroDistance K t = dist (center t) z :=
  (zeros_closed K).exists_infDist_eq_dist ⟨-2, neg_two_mem K⟩ _

theorem zeros_left {z : ℂ} (hz : z ∈ zeros K) : z.re < 1 := by
  by_contra! h
  have h0 : z ≠ 0 := by rintro rfl; norm_num at h
  exact nonzero_on_closed_halfplane K h ((entireReg_eq_reg K h0).symm.trans hz)

theorem distance_gt_one (t : ℝ) : 1 < zeroDistance K t := by
  obtain ⟨z, hz, h⟩ := nearest K t
  rw [h, dist_eq_norm]
  have hr := re_le_norm (center t - z)
  change 2 - z.re ≤ _ at hr
  linarith [zeros_left K hz]

private theorem near_center (t : ℝ) : ∀ᶠ z in 𝓝 (center t),
    entireReg K z = (z-1) * dedekindZeta K z := by
  have h : ∀ᶠ z in 𝓝 (center t), 1 < z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (show (1:ℝ) < 2 by norm_num)
  filter_upwards [h] with z hz
  exact (entireReg_eq_reg K (by rintro rfl; norm_num at hz)).trans (reg_agrees K hz)

/-- The identity theorem propagates the inverse identity to the whole open
convergence disk; no convergence on its boundary is needed. -/
theorem radius_le_distance (t : ℝ) {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hp : 0 < p.radius) (hg : ReciprocalRadius.InverseGerm K t p) :
    p.radius ≤ ENNReal.ofReal (zeroDistance K t) := by
  let U := eball (center t) p.radius
  have hA : AnalyticOnNhd ℂ (entireReg K) U :=
    ((entireReg_diff K).differentiableOn.analyticOnNhd isOpen_univ).mono (subset_univ _)
  have hB : AnalyticOnNhd ℂ (fun z => p.sum (z - center t)) U := by
    simpa [U] using p.analyticOnNhd.comp_sub (center t)
  have he : (fun z => entireReg K z * p.sum (z - center t)) =ᶠ[𝓝 (center t)] (fun _ => 1) := by
    filter_upwards [hg, near_center K t] with z hz hf using hf.symm ▸ hz
  have hall := (hA.mul hB).eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
    isPreconnected_eball (mem_eball_self hp) he
  obtain ⟨z, hz, hdist⟩ := nearest K t
  by_contra! hlt
  have hzU : z ∈ U := by
    change edist z (center t) < p.radius
    rwa [edist_dist, dist_comm, ← hdist]
  have hf : entireReg K z * p.sum (z - center t) = 1 := hall hzU
  simp [show entireReg K z = 0 from hz] at hf

/-- Compare the given germ with the Cauchy expansion on every smaller
closed disk. Uniqueness is for the original ideal Dirichlet series germ. -/
theorem distance_le_radius (t : ℝ) {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hp : 0 < p.radius) (hg : ReciprocalRadius.InverseGerm K t p) :
    ENNReal.ofReal (zeroDistance K t) ≤ p.radius := by
  apply ENNReal.le_of_forall_pos_nnreal_lt
  intro r hr hrD
  have hd : (r : ℝ) < zeroDistance K t := by
    rwa [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff
      (zero_lt_one.trans (distance_gt_one K t))] at hrD
  have hn {z : ℂ} (hz : z ∈ closedBall (center t) (r:ℝ)) : entireReg K z ≠ 0 :=
    fun h => notMem_of_dist_lt_infDist ((mem_closedBall'.mp hz).trans_lt hd) (show z ∈ zeros K from h)
  have hdiff : DifferentiableOn ℂ (fun z => (entireReg K z)⁻¹) (closedBall (center t) (r:ℝ)) :=
    fun z hz => (((entireReg_diff K z).inv (hn hz))).differentiableWithinAt
  let q := cauchyPowerSeries (fun z => (entireReg K z)⁻¹) (center t) (r:ℝ)
  have hq : HasFPowerSeriesOnBall (fun z => (entireReg K z)⁻¹) q (center t) r :=
    hdiff.hasFPowerSeriesOnBall hr
  have gq : ReciprocalRadius.InverseGerm K t q := by
    filter_upwards [ball_mem_nhds (center t) (show 0 < (r:ℝ) from hr), near_center K t] with z hz hf
    have hw : z - center t ∈ eball (0 : ℂ) (r : ℝ≥0∞) := by
      simpa only [eball_coe, mem_ball_iff_norm, sub_zero] using hz
    have hv := hq.sum hw
    rw [add_sub_cancel] at hv
    change ((z-1) * dedekindZeta K z) * q.sum (z - center t) = 1
    rw [← hf, ← hv, mul_inv_cancel₀ (hn (ball_subset_closedBall hz))]
  have he := ReciprocalRadius.inverse_unique K t hp ((ENNReal.coe_pos.mpr hr).trans_le hq.r_le) hg gq
  exact he ▸ hq.r_le

theorem radius_eq_zeroDistance (t : ℝ) {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hp : 0 < p.radius) (hg : ReciprocalRadius.InverseGerm K t p) :
    p.radius = ENNReal.ofReal (zeroDistance K t) :=
  le_antisymm (radius_le_distance K t hp hg) (distance_le_radius K t hp hg)

/-- The original bound at all heights for this K is exactly the exclusion
of zeros to the right of the critical line, not an unconditional proof of it. -/
theorem three_halves_iff :
    (∀ t : ℝ, ∃ p : FormalMultilinearSeries ℂ ℂ ℂ,
      ENNReal.ofReal (3 / 2) ≤ p.radius ∧ ReciprocalRadius.InverseGerm K t p) ↔
    ∀ z ∈ zeros K, z.re ≤ 1 / 2 := by
  constructor
  · intro h z hz
    obtain ⟨p, hp, hg⟩ := h z.im
    have hpos : 0 < ENNReal.ofReal (3 / 2) := ENNReal.ofReal_pos.mpr (by norm_num)
    rw [radius_eq_zeroDistance K z.im (hpos.trans_le hp) hg] at hp
    have hbound := (ENNReal.ofReal_le_ofReal_iff (zero_lt_one.trans (distance_gt_one K z.im)).le).mp hp
    have hdist : zeroDistance K z.im ≤ dist (center z.im) z := infDist_le_dist_of_mem hz
    have hsub : center z.im - z = ((2 - z.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [center]
    rw [dist_eq_norm, hsub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [zeros_left K hz])] at hdist
    linarith
  · intro h t
    obtain ⟨p,hp,hg⟩ := all_fields_radius_gt_one K t
    refine ⟨p, ?_, hg⟩
    rw [radius_eq_zeroDistance K t (zero_lt_one.trans hp) hg]
    apply ENNReal.ofReal_le_ofReal
    obtain ⟨z,hz,hd⟩ := nearest K t
    rw [hd, dist_eq_norm]
    have hr := re_le_norm (center t - z)
    change 2 - z.re ≤ _ at hr
    linarith [h z hz]

/-- A particular continuation in the exact sense used in FormalConjectures.
The totalized value at 1 plays no role in that predicate. -/
def canonicalZeta (z : ℂ) := entireReg K z / (z-1)

theorem canonical_isDedekindZeta : ERH.IsDedekindZeta K (canonicalZeta K) := by
  constructor
  · intro z hz
    exact ((entireReg_diff K z).div (differentiableAt_id.sub_const (1:ℂ))
      (sub_ne_zero.mpr (show z ≠ 1 from hz))).differentiableWithinAt
  · intro z hz
    have h0 : z ≠ 0 := by rintro rfl; norm_num at hz
    have h1 : z ≠ 1 := by rintro rfl; norm_num at hz
    rw [canonicalZeta, entireReg_eq_reg K h0, reg_agrees K hz]
    exact mul_div_cancel_left₀ _ (sub_ne_zero.mpr h1)

theorem three_halves_of_field_erh (h : ERH.ExtendedRiemannHypothesis K) :
    ∀ t : ℝ, ∃ p : FormalMultilinearSeries ℂ ℂ ℂ,
      ENNReal.ofReal (3 / 2) ≤ p.radius ∧ ReciprocalRadius.InverseGerm K t p := by
  apply (three_halves_iff K).mpr
  intro z hz
  by_contra! hr
  have h0 : canonicalZeta K z = 0 := by rw [canonicalZeta, show entireReg K z = 0 from hz, zero_div]
  have he := h _ (canonical_isDedekindZeta K) z (by linarith) (zeros_left K hz) h0
  linarith

/-- The exact public H2 predicate, not an implication from an unproved
declaration: both directions here are theorems with no additional axioms. -/
theorem site_h2_iff_erh :
    R_ERH_extended_riemann_hypothesis_R1.H2 ↔
      ∀ (L : Type) [Field L] [NumberField L], ERH.ExtendedRiemannHypothesis L := by
  constructor
  · intro h L _ _
    exact R_ERH_extended_riemann_hypothesis_R1.main ThetaAudit.zero_reflection h L
  · intro h L _ _ t
    exact three_halves_of_field_erh L (h L) t

#print axioms OMA.ExactRadius.entireReg_diff
#print axioms OMA.ExactRadius.entireReg_eq_reg
#print axioms OMA.ExactRadius.neg_two_mem
#print axioms OMA.ExactRadius.distance_gt_one
#print axioms OMA.ExactRadius.radius_eq_zeroDistance
#print axioms OMA.ExactRadius.three_halves_iff
#print axioms OMA.ExactRadius.canonical_isDedekindZeta
#print axioms OMA.ExactRadius.site_h2_iff_erh
end OMA.ExactRadius
