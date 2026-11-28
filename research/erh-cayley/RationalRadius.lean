import ReciprocalRadius
import DedekindThetaAudit
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.ZetaZeros

/-! For the rational field the reciprocal germ has radius exactly the distance
to the nearest zeta zero. This formula by itself gives no bound of 3/2. -/

noncomputable section

namespace OMA.RationalRadius

open Complex NumberField Filter Set Metric
open scoped Topology ENNReal NNReal

abbrev center (t : ℝ) : ℂ := ⟨2, t⟩
def zeroDistance (t : ℝ) : ℝ := infDist (center t) riemannZetaZeros
abbrev Germ (K : Type*) [Field K] [NumberField K] := ReciprocalRadius.InverseGerm K

private theorem regularized_off_one {z : ℂ} (hz : z ≠ 1) :
    riemannZeta₁ z = (z - 1) * riemannZeta z := by
  rw [riemannZeta_eq_inv_sub_mul hz, mul_inv_cancel_left₀ (sub_ne_zero.mpr hz)]

theorem regularized_zero_iff (z : ℂ) : riemannZeta₁ z = 0 ↔ z ∈ riemannZetaZeros := by
  rw [mem_riemannZetaZeros]
  rcases eq_or_ne z 1 with rfl | hz
  · simp [riemannZeta_one_ne_zero]
  · rw [regularized_off_one hz, mul_eq_zero]
    simp [sub_ne_zero.mpr hz]

private theorem zeros_nonempty : riemannZetaZeros.Nonempty := by
  refine ⟨-2, mem_riemannZetaZeros.mpr ?_⟩
  simpa using riemannZeta_neg_two_mul_nat_add_one 0

theorem nearest_zero (t : ℝ) :
    ∃ z ∈ riemannZetaZeros, zeroDistance t = dist (center t) z :=
  isClosed_riemannZetaZeros.exists_infDist_eq_dist zeros_nonempty _

theorem one_lt_zeroDistance (t : ℝ) : 1 < zeroDistance t := by
  obtain ⟨z, hz, he⟩ := nearest_zero t
  rw [he]
  by_contra! h
  have hre := (re_le_norm (center t - z)).trans (show ‖center t - z‖ ≤ 1 by
    simpa only [dist_eq_norm] using h)
  change 2 - z.re ≤ 1 at hre
  exact (riemannZeta_ne_zero_of_one_le_re (by linarith)) (mem_riemannZetaZeros.mp hz)

private theorem near_center (t : ℝ) :
    ∀ᶠ z in 𝓝 (center t), riemannZeta₁ z = (z - 1) * dedekindZeta ℚ z := by
  have h : ∀ᶠ z in 𝓝 (center t), 1 < z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num [center])
  filter_upwards [h] with z hz
  have hz1 : z ≠ 1 := by rintro rfl; norm_num at hz
  rw [regularized_off_one hz1, R_ERH_extended_riemann_hypothesis_R1_H1_R1.zeta_eq_in_half_plane hz]

/-- Cauchy expansions on closed subdisks glue without a boundary hypothesis. -/
private theorem taylor_on_open {f : ℂ → ℂ} {c : ℂ} {R : ℝ≥0} (hR : 0 < R)
    (hd : DifferentiableOn ℂ f (ball c R)) :
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ, HasFPowerSeriesOnBall f p c R := by
  obtain ⟨p, _, h₀⟩ := hd.analyticAt (ball_mem_nhds c (show 0 < (R : ℝ) from hR))
  have small (r : ℝ≥0) (hr : 0 < r) (hrR : (r : ℝ≥0∞) < R) :
      HasFPowerSeriesOnBall f p c r := by
    have hrR' : (r : ℝ) < R := by exact_mod_cast (show r < R by exact_mod_cast hrR)
    exact h₀.exchange_radius ((hd.mono (closedBall_subset_ball hrR')).hasFPowerSeriesOnBall hr)
  refine ⟨p, ⟨ENNReal.le_of_forall_pos_nnreal_lt (fun r hr hlt => (small r hr hlt).r_le),
    ENNReal.coe_pos.mpr hR, ?_⟩⟩
  intro y hy
  obtain ⟨r, hyr, hrR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp (mem_eball_zero_iff.mp hy)
  exact (small r (ENNReal.coe_pos.mp (bot_le.trans_lt hyr)) hrR).hasSum (mem_eball_zero_iff.mpr hyr)

private theorem regularized_ne_on_disk (t : ℝ) {z : ℂ}
    (hz : z ∈ ball (center t) (zeroDistance t)) : riemannZeta₁ z ≠ 0 :=
  fun h => notMem_of_dist_lt_infDist (mem_ball'.mp hz) ((regularized_zero_iff z).mp h)

theorem exists_inverse_to_nearest_zero (t : ℝ) :
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ, ENNReal.ofReal (zeroDistance t) ≤ p.radius ∧
      Germ ℚ t p := by
  have hpos := zero_lt_one.trans (one_lt_zeroDistance t)
  let R : ℝ≥0 := ⟨zeroDistance t, hpos.le⟩
  have hR : (R : ℝ) = zeroDistance t := rfl
  have hd : DifferentiableOn ℂ (fun z => (riemannZeta₁ z)⁻¹) (ball (center t) R) :=
    fun z hz => ((differentiable_riemannZeta₁ z).inv (regularized_ne_on_disk t hz)).differentiableWithinAt
  obtain ⟨p, hp⟩ := taylor_on_open (show 0 < R from hpos) hd
  refine ⟨p, ?_, ?_⟩
  · rw [← hR, ENNReal.ofReal_coe_nnreal]
    exact hp.r_le
  · filter_upwards [ball_mem_nhds (center t) hpos, near_center t] with z hz he
    have hw : z - center t ∈ eball (0 : ℂ) (R : ℝ≥0∞) := by
      simpa only [eball_coe, mem_ball_iff_norm, sub_zero, hR] using hz
    have hv := hp.sum hw
    rw [add_sub_cancel] at hv
    change ((z - 1) * dedekindZeta ℚ z) * p.sum (z - center t) = 1
    rw [← he, ← hv, mul_inv_cancel₀ (regularized_ne_on_disk t hz)]

/-- On the whole convergence disk the product is one, so there is no zero
in that open disk, even if the putative radius is infinite. -/
theorem radius_le_zeroDistance (t : ℝ) {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hp : 0 < p.radius) (hg : Germ ℚ t p) : p.radius ≤ ENNReal.ofReal (zeroDistance t) := by
  let U := eball (center t) p.radius
  have hA : AnalyticOnNhd ℂ riemannZeta₁ U :=
    (differentiable_riemannZeta₁.differentiableOn.analyticOnNhd isOpen_univ).mono (subset_univ _)
  have hB : AnalyticOnNhd ℂ (fun z => p.sum (z - center t)) U := by
    simpa [U] using p.analyticOnNhd.comp_sub (center t)
  have he : (fun z => riemannZeta₁ z * p.sum (z - center t)) =ᶠ[𝓝 (center t)] (fun _ => 1) := by
    filter_upwards [hg, near_center t] with z hz he using he.symm ▸ hz
  have hall := (hA.mul hB).eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
    isPreconnected_eball (mem_eball_self hp) he
  obtain ⟨z, hz, hdist⟩ := nearest_zero t
  by_contra! hlt
  have hzU : z ∈ U := by
    change edist z (center t) < p.radius
    rwa [edist_dist, dist_comm, ← hdist]
  have hprod : riemannZeta₁ z * p.sum (z - center t) = 1 := hall hzU
  simp [(regularized_zero_iff z).mpr hz] at hprod

/-- This is the radius of any positive-radius inverse germ, including the
series already constructed by the arbitrary-number-field baseline. -/
theorem radius_eq_zeroDistance (t : ℝ) {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hp : 0 < p.radius) (hg : Germ ℚ t p) : p.radius = ENNReal.ofReal (zeroDistance t) := by
  obtain ⟨q, hq, gq⟩ := exists_inverse_to_nearest_zero t
  have hpos := ENNReal.ofReal_pos.mpr (zero_lt_one.trans (one_lt_zeroDistance t))
  have he := ReciprocalRadius.inverse_unique ℚ t hp (hpos.trans_le hq) hg gq
  exact le_antisymm (radius_le_zeroDistance t hp hg) (he ▸ hq)

theorem rational_radius_gt_one (t : ℝ) :
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ, 1 < p.radius ∧ Germ ℚ t p := by
  obtain ⟨p, hr, hg⟩ := exists_inverse_to_nearest_zero t
  have h : ENNReal.ofReal 1 < ENNReal.ofReal (zeroDistance t) :=
    (ENNReal.ofReal_lt_ofReal_iff (zero_lt_one.trans (one_lt_zeroDistance t))).mpr (one_lt_zeroDistance t)
  exact ⟨p, (by simpa only [ENNReal.ofReal_one] using h.trans_le hr), hg⟩

theorem continuous_zeroDistance : Continuous zeroDistance := by
  have hc : Continuous center := by
    have he : center = fun t : ℝ => (2 : ℂ) + (t : ℂ) * I := by
      funext t
      apply Complex.ext <;> simp
    rw [he]
    exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  exact (continuous_infDist_pt riemannZetaZeros).comp hc

private theorem germ_iff_rat_of_degree_one {K : Type*} [Field K] [NumberField K]
    (hk : Module.finrank ℚ K = 1) (t : ℝ) (p : FormalMultilinearSeries ℂ ℂ ℂ) :
    Germ K t p ↔ Germ ℚ t p := by
  let e : ℚ ≃+* K := RingEquiv.ofBijective (algebraMap ℚ K)
    ((Algebra.finrank_eq_one_iff_bijective_algebraMap (F := ℚ) (E := K)).mp hk)
  have h := R_ERH_extended_riemann_hypothesis_R1.dedekindZeta_eq_of_ringEquiv e
  simp only [Germ, ReciprocalRadius.InverseGerm, h]

/-- The distance is the same for every degree-one field, since its ideal
counting Dirichlet series is the rational-field series. -/
theorem degree_one_radius_eq {K : Type*} [Field K] [NumberField K]
    (hk : Module.finrank ℚ K = 1) (t : ℝ) {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hp : 0 < p.radius) (hg : Germ K t p) : p.radius = ENNReal.ofReal (zeroDistance t) :=
  radius_eq_zeroDistance t hp ((germ_iff_rat_of_degree_one hk t p).mp hg)

/-- One margin works on any *specified compact* set of heights. Nothing here
asserts that the infimum of the margins over the whole real line is positive. -/
theorem compact_height_gain {S : Set ℝ} (hS : IsCompact S) :
    ∃ R : ℝ, 1 < R ∧ ∀ t ∈ S, ∀ (K : Type*) [Field K] [NumberField K],
      Module.finrank ℚ K = 1 → ∃ p : FormalMultilinearSeries ℂ ℂ ℂ,
        ENNReal.ofReal R ≤ p.radius ∧ Germ K t p := by
  obtain ⟨R, hR, hdist⟩ := hS.exists_forall_le' continuous_zeroDistance.continuousOn
    (fun t _ => one_lt_zeroDistance t)
  refine ⟨R, hR, ?_⟩
  intro t ht K _ _ hk
  obtain ⟨p, hp, hg⟩ := exists_inverse_to_nearest_zero t
  exact ⟨p, (ENNReal.ofReal_le_ofReal (hdist t ht)).trans hp,
    (germ_iff_rat_of_degree_one hk t p).mpr hg⟩

/-- The global rational 3/2 estimate asks exactly for the exclusion of
zeros strictly to the right of the critical line. Zeros on it are allowed. -/
theorem rational_three_halves_iff :
    (∀ t : ℝ, ∃ p : FormalMultilinearSeries ℂ ℂ ℂ,
      ENNReal.ofReal (3 / 2) ≤ p.radius ∧ Germ ℚ t p) ↔
    ∀ z ∈ riemannZetaZeros, z.re ≤ 1 / 2 := by
  constructor
  · intro h z hz
    obtain ⟨p, hp, hg⟩ := h z.im
    have hpos : 0 < ENNReal.ofReal (3 / 2) := ENNReal.ofReal_pos.mpr (by norm_num)
    rw [radius_eq_zeroDistance z.im (hpos.trans_le hp) hg] at hp
    have hlow := (ENNReal.ofReal_le_ofReal_iff (zero_le_one.trans (one_lt_zeroDistance z.im).le)).mp hp
    have hdist : zeroDistance z.im ≤ dist (center z.im) z := infDist_le_dist_of_mem hz
    have hre : z.re < 1 := lt_of_not_ge fun h1 =>
      riemannZeta_ne_zero_of_one_le_re h1 (mem_riemannZetaZeros.mp hz)
    have hsub : center z.im - z = ((2 - z.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [center]
    rw [dist_eq_norm, hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)] at hdist
    linarith
  · intro h t
    obtain ⟨p, hp, hg⟩ := exists_inverse_to_nearest_zero t
    obtain ⟨z, hz, he⟩ := nearest_zero t
    have hnorm := re_le_norm (center t - z)
    change 2 - z.re ≤ ‖center t - z‖ at hnorm
    have hr : 3 / 2 ≤ zeroDistance t := by
      rw [he, dist_eq_norm]
      linarith [h z hz]
    exact ⟨p, (ENNReal.ofReal_le_ofReal hr).trans hp, hg⟩

/-- Explicit interface for a separately certified proof of classical RH. No
declaration asserting RH is imported as a premise of an unconditional bound. -/
theorem degree_one_three_halves_of_rh (hRH : RiemannHypothesis)
    {K : Type*} [Field K] [NumberField K] (hk : Module.finrank ℚ K = 1) (t : ℝ) :
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ, ENNReal.ofReal (3 / 2) ≤ p.radius ∧ Germ K t p := by
  have hz : ∀ z ∈ riemannZetaZeros, z.re ≤ 1 / 2 := by
    intro z hz
    by_cases htriv : ∃ n : ℕ, z = -2 * (n + 1)
    · obtain ⟨n, rfl⟩ := htriv
      simp only [neg_mul, neg_re, mul_re, re_ofNat, im_ofNat, add_re, natCast_re, one_re,
        zero_mul, sub_zero]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    · have hne : z ≠ 1 := by
        rintro rfl
        exact riemannZeta_one_ne_zero (mem_riemannZetaZeros.mp hz)
      exact (hRH z (mem_riemannZetaZeros.mp hz) htriv hne).le
  obtain ⟨p, hp, hg⟩ := rational_three_halves_iff.mpr hz t
  exact ⟨p, hp, (germ_iff_rat_of_degree_one hk t p).mpr hg⟩

#print axioms OMA.RationalRadius.regularized_zero_iff
#print axioms OMA.RationalRadius.one_lt_zeroDistance
#print axioms OMA.RationalRadius.radius_eq_zeroDistance
#print axioms OMA.RationalRadius.rational_radius_gt_one
#print axioms OMA.RationalRadius.degree_one_radius_eq
#print axioms OMA.RationalRadius.compact_height_gain
#print axioms OMA.RationalRadius.rational_three_halves_iff
#print axioms OMA.RationalRadius.degree_one_three_halves_of_rh

end OMA.RationalRadius
