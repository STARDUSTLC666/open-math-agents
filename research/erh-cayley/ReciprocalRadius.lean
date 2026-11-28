import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Group.Tannery

/-! An unconditional baseline for the reciprocal-series step of ERH.
The absolute-convergence half-plane gives radius one, not three halves. -/

noncomputable section

namespace OMA.ReciprocalRadius

open Complex Filter Set NumberField Asymptotics
open scoped NumberField Topology NNReal ENNReal Classical

variable (K : Type*) [Field K] [NumberField K]

abbrev ideals := Ideal (𝓞 K)
abbrev fiber (n : ℕ) := {I : ideals K // Ideal.absNorm I = n}
abbrev a (n : ℕ) := Nat.card (fiber K n)

-- The coefficient estimate is the one used in the earlier Mellin audit.
theorem coeff_mean :
    Tendsto (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n, (a K k : ℝ)) / n) atTop
      (𝓝 (dedekindZeta_residue K)) := by
  refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr fun n => ?_
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum, a, fiber]
  congr
  rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} by simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ => Ideal.finite_setOfPred_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

theorem series_summable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (a K n : ℂ)) s := by
  have h := LSeriesSummable_of_sum_norm_bigO_and_nonneg (f := fun n => (a K n : ℝ))
    (r := 1) (isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (by simpa using coeff_mean K))
    (fun n => Nat.cast_nonneg _) zero_le_one hs
  simpa only [ofReal_natCast] using h

theorem analytic_right {s : ℂ} (hs : 1 < s.re) : AnalyticAt ℂ (dedekindZeta K) s := by
  have ha : LSeries.abscissaOfAbsConv (fun n => (a K n : ℂ)) ≤ (1 : ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun x hx => series_summable K (s := x) hx
  exact LSeries_analyticOnNhd _ s (ha.trans_lt (EReal.coe_lt_coe_iff.mpr hs))

def weight (s : ℂ) (I : ideals K) : ℂ := (Ideal.absNorm I : ℂ) ^ (-s)

theorem weight_mul (s : ℂ) (I J : ideals K) :
    weight K s (I * J) = weight K s I * weight K s J := by
  simp only [weight, map_mul, Nat.cast_mul, natCast_mul_natCast_cpow]

theorem term_eq {s : ℂ} (hs : s ≠ 0) (n : ℕ) :
    LSeries.term (fun k => (a K k : ℂ)) s n = (a K n : ℂ) * (n : ℂ) ^ (-s) := by
  rw [LSeries.term_of_ne_zero' hs, cpow_neg, div_eq_mul_inv]

private abbrev fiberFintype (n : ℕ) : Fintype (fiber K n) :=
  (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) n).fintype

theorem fiber_sum {s : ℂ} (hs : s ≠ 0) (n : ℕ) :
    (∑' I : fiber K n, weight K s I.val) = LSeries.term (fun k => (a K k : ℂ)) s n := by
  let _ := fiberFintype K n
  rw [term_eq K hs, tsum_fintype]
  simp [weight, fun I : fiber K n => I.property, a, Nat.card_eq_fintype_card, nsmul_eq_mul]

theorem fiber_norm {s : ℂ} (hs : s ≠ 0) (n : ℕ) :
    (∑' I : fiber K n, ‖weight K s I.val‖) = ‖LSeries.term (fun k => (a K k : ℂ)) s n‖ := by
  let _ := fiberFintype K n
  rw [term_eq K hs, tsum_fintype, norm_mul]
  simp [weight, fun I : fiber K n => I.property, a, Nat.card_eq_fintype_card, nsmul_eq_mul]

theorem norm_summable {s : ℂ} (hs : 1 < s.re) : Summable fun I => ‖weight K s I‖ := by
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
  let F (n : ℕ) : Set (ideals K) := {I | Ideal.absNorm I = n}
  apply (summable_partition (s := F) (fun I => norm_nonneg _) ?_).2
  · refine ⟨fun n => ?_, ?_⟩
    · let _ := fiberFintype K n
      change Summable fun I : fiber K n => ‖weight K s I.val‖
      exact Summable.of_finite
    · change Summable fun n => ∑' I : fiber K n, ‖weight K s I.val‖
      simp_rw [fiber_norm K hs0]
      exact (series_summable K hs).norm
  · exact fun I => ⟨Ideal.absNorm I, rfl, fun _ h => h.symm⟩

theorem sum_eq_zeta {s : ℂ} (hs : 1 < s.re) : (∑' I, weight K s I) = dedekindZeta K s := by
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have h := ((norm_summable K hs).of_norm.hasSum.tsum_fiberwise (fun I : ideals K => Ideal.absNorm I)).tsum_eq
  exact h.symm.trans (tsum_congr fun n => fiber_sum K hs0 n)

abbrev primeIdeals := {P : ideals K // Prime P}

def sift (s : ℂ) (S : Finset (primeIdeals K)) (I : ideals K) : ℂ := by
  classical
  exact if ∀ p ∈ S, ¬p.val ∣ I then weight K s I else 0

theorem norm_sift_le (s : ℂ) (S : Finset (primeIdeals K)) (I : ideals K) :
    ‖sift K s S I‖ ≤ ‖weight K s I‖ := by
  classical
  unfold sift
  split <;> simp

theorem sift_mul (s : ℂ) {S : Finset (primeIdeals K)} {p : primeIdeals K} (hp : p ∉ S)
    (I : ideals K) : sift K s S (p.val * I) = weight K s p.val * sift K s S I := by
  classical
  have he : (∀ q ∈ S, ¬q.val ∣ p.val * I) ↔ (∀ q ∈ S, ¬q.val ∣ I) := by
    constructor
    · intro h q hq hI
      exact h q hq (dvd_mul_of_dvd_right hI _)
    · intro h q hq hmul
      rcases q.property.dvd_or_dvd hmul with hqp | hqI
      · have heq : q = p := Subtype.ext (associated_iff_eq.mp (q.property.associated_of_dvd p.property hqp))
        exact hp (heq ▸ hq)
      · exact h q hq hqI
  simp only [sift, he, weight_mul]
  split <;> simp

theorem sift_insert {s : ℂ} (hs : 1 < s.re) (S : Finset (primeIdeals K)) (p : primeIdeals K)
    (hp : p ∉ S) :
    (∑' I, sift K s (insert p S) I) = (1 - weight K s p.val) * (∑' I, sift K s S I) := by
  classical
  let omitted (I : ideals K) := if p.val ∣ I then sift K s S I else 0
  have hS := (norm_summable K hs).of_norm_bounded (norm_sift_le K s S)
  have hO : Summable omitted := (norm_summable K hs).of_norm_bounded fun I => by
    dsimp [omitted]; split
    · exact norm_sift_le K s S I
    · simp
  have hdiff (I : ideals K) : sift K s (insert p S) I = sift K s S I - omitted I := by
    by_cases h : p.val ∣ I <;> simp [sift, omitted, h]
  have hi : Function.Injective (fun I : ideals K => p.val * I) := mul_right_injective₀ p.property.ne_zero
  have hsupp : Function.support omitted ⊆ Set.range (fun I : ideals K => p.val * I) := by
    intro I hI
    by_contra h
    have hn : ¬p.val ∣ I := fun ⟨d, hd⟩ => h ⟨d, hd.symm⟩
    exact hI (if_neg hn)
  have hsum : (∑' I, omitted I) = weight K s p.val * (∑' I, sift K s S I) := by
    rw [← hi.tsum_eq hsupp, ← tsum_mul_left]
    apply tsum_congr
    intro I
    simpa [omitted] using sift_mul K s hp I
  simp_rw [hdiff]
  rw [hS.tsum_sub hO, hsum, sub_mul, one_mul]

theorem sift_limit {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun S : Finset (primeIdeals K) => ∑' I, sift K s S I) atTop (𝓝 1) := by
  classical
  let g (I : ideals K) : ℂ := if I = 1 then 1 else 0
  have hg : (∑' I, g I) = 1 := by simp [g]
  rw [← hg]
  apply tendsto_tsum_of_dominated_convergence (norm_summable K hs)
  · intro I
    refine (tendsto_congr' ?_).2 (tendsto_const_nhds (x := g I))
    by_cases h1 : I = 1
    · subst I
      exact Filter.Eventually.of_forall fun S => by
        have h : ∀ q ∈ S, ¬(q : primeIdeals K).val ∣ (1 : ideals K) := fun q _ => q.property.not_dvd_one
        change (if ∀ q ∈ S, ¬q.val ∣ (1 : ideals K) then weight K s 1 else 0) = g 1
        rw [if_pos h]
        simp [weight, g]
    · by_cases h0 : I = 0
      · subst I
        have hs' : -s ≠ 0 := neg_ne_zero.mpr (by rintro rfl; norm_num at hs)
        exact Filter.Eventually.of_forall fun S => by simp [sift, weight, g, zero_cpow hs']
      · have hu : ¬IsUnit I := fun h => h1 (by simpa only [Ideal.one_eq_top] using Ideal.isUnit_iff.mp h)
        obtain ⟨P, hirr, hd⟩ := WfDvdMonoid.exists_irreducible_factor hu h0
        let p : primeIdeals K := ⟨P, hirr.prime⟩
        filter_upwards [eventually_finset_mem_atTop p] with S hS
        have hbad : ¬∀ q ∈ S, ¬q.val ∣ I := fun h => (h p hS) hd
        change (if ∀ q ∈ S, ¬q.val ∣ I then weight K s I else 0) = if I = 1 then 1 else 0
        rw [if_neg hbad, if_neg h1]
  · exact Filter.Eventually.of_forall fun S I => norm_sift_le K s S I

/-- Dedekind zeta is nonzero in the half-plane of absolute convergence. -/
theorem zeta_ne_zero {s : ℂ} (hs : 1 < s.re) : dedekindZeta K s ≠ 0 := by
  classical
  intro hz
  have zero_sums (S : Finset (primeIdeals K)) : (∑' I, sift K s S I) = 0 := by
    induction S using Finset.induction_on with
    | empty => simpa [sift] using (sum_eq_zeta K hs).trans hz
    | @insert p S hp ih => rw [sift_insert K hs S p hp, ih, mul_zero]
  have h0 : Tendsto (fun S : Finset (primeIdeals K) => ∑' I, sift K s S I) atTop (𝓝 0) :=
    tendsto_const_nhds.congr fun S => (zero_sums S).symm
  exact zero_ne_one (tendsto_nhds_unique h0 (sift_limit K hs))

/-- A single Taylor series works on an open unit disk: holomorphy on the
boundary is not necessary, since all smaller disks have the same germ. -/
theorem taylor_on_open_unit {f : ℂ → ℂ} {c : ℂ} (hd : DifferentiableOn ℂ f (Metric.ball c 1)) :
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ, HasFPowerSeriesOnBall f p c 1 := by
  obtain ⟨p, r₀, h₀⟩ := hd.analyticAt (Metric.ball_mem_nhds c zero_lt_one)
  have small (r : ℝ≥0) (hr : 0 < r) (hr1 : (r : ℝ≥0∞) < 1) : HasFPowerSeriesOnBall f p c r := by
    have hr1' : (r : ℝ) < 1 := by exact_mod_cast (show r < 1 by exact_mod_cast hr1)
    exact h₀.exchange_radius ((hd.mono (Metric.closedBall_subset_ball hr1')).hasFPowerSeriesOnBall hr)
  refine ⟨p, ⟨ENNReal.le_of_forall_pos_nnreal_lt (fun r hr hr1 => (small r hr hr1).r_le), zero_lt_one, ?_⟩⟩
  intro y hy
  obtain ⟨r, hyr, hr1⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp (mem_eball_zero_iff.mp hy)
  have hr : 0 < r := ENNReal.coe_pos.mp (bot_le.trans_lt hyr)
  exact (small r hr hr1).hasSum (mem_eball_zero_iff.mpr hyr)

private theorem ball_right (t : ℝ) {z : ℂ} (hz : z ∈ Metric.ball (⟨2,t⟩ : ℂ) 1) : 1 < z.re := by
  have h := (re_le_norm ((⟨2,t⟩ : ℂ) - z)).trans_lt (mem_ball_iff_norm'.mp hz)
  change 2 - z.re < 1 at h
  linarith

/-- On the full open unit disk the series inverts the regularized Dirichlet series. -/
theorem inverse_on_disk (t : ℝ) :
    let c : ℂ := ⟨2,t⟩
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ, 1 ≤ p.radius ∧
      ∀ z ∈ Metric.ball c 1, ((z - 1) * dedekindZeta K z) * p.sum (z - c) = 1 := by
  let c : ℂ := ⟨2,t⟩
  let F (z : ℂ) := (z - 1) * dedekindZeta K z
  have hn {z : ℂ} (hz : z ∈ Metric.ball c 1) : F z ≠ 0 := by
    have h := ball_right t hz
    have hz1 : z ≠ 1 := by rintro rfl; norm_num at h
    exact mul_ne_zero (sub_ne_zero.mpr hz1) (zeta_ne_zero K h)
  have hd : DifferentiableOn ℂ (fun z => (F z)⁻¹) (Metric.ball c 1) := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    exact (((differentiableAt_id.sub_const (1 : ℂ)).mul (analytic_right K (ball_right t hz)).differentiableAt).inv (hn hz))
  obtain ⟨p,hp⟩ := taylor_on_open_unit hd
  refine ⟨p,hp.r_le,fun z hz => ?_⟩
  have hy : z - c ∈ Metric.eball (0 : ℂ) 1 := by
    simpa only [← ENNReal.coe_one, Metric.eball_coe, NNReal.coe_one, mem_ball_iff_norm, sub_zero] using hz
  have hv := hp.sum hy
  rw [add_sub_cancel] at hv
  change F z * p.sum (z - c) = 1
  rw [← hv, mul_inv_cancel₀ (hn hz)]

/-- The site's exact germ conclusion, with its radius 3/2 weakened to 1. -/
theorem radius_one (t : ℝ) :
    let c : ℂ := ⟨2,t⟩
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ, ENNReal.ofReal 1 ≤ p.radius ∧
      ∀ᶠ z in 𝓝 c, ((z - 1) * dedekindZeta K z) * p.sum (z - c) = 1 := by
  obtain ⟨p,hr,h⟩ := inverse_on_disk K t
  refine ⟨p, by simpa using hr, ?_⟩
  filter_upwards [Metric.ball_mem_nhds (⟨2,t⟩ : ℂ) (zero_lt_one : (0 : ℝ) < 1)] with z hz using h z hz

abbrev InverseGerm (t : ℝ) (p : FormalMultilinearSeries ℂ ℂ ℂ) : Prop :=
  let c : ℂ := ⟨2,t⟩
  ∀ᶠ z in 𝓝 c, ((z - 1) * dedekindZeta K z) * p.sum (z - c) = 1

/-- There is no freedom to choose a different inverse series to improve the radius. -/
theorem inverse_unique (t : ℝ) {p q : FormalMultilinearSeries ℂ ℂ ℂ}
    (hp : 0 < p.radius) (hq : 0 < q.radius) (gp : InverseGerm K t p) (gq : InverseGerm K t q) : p = q := by
  let c : ℂ := ⟨2,t⟩
  apply (p.hasFPowerSeriesOnBall hp).hasFPowerSeriesAt.eq_formalMultilinearSeries_of_eventually
    (q.hasFPowerSeriesOnBall hq).hasFPowerSeriesAt
  have hc : Tendsto (fun w : ℂ => c + w) (𝓝 0) (𝓝 c) := by
    simpa only [add_zero, id_eq] using (tendsto_const_nhds (x := c)).add (tendsto_id (x := 𝓝 (0 : ℂ)))
  filter_upwards [hc.eventually gp, hc.eventually gq] with w hw hw'
  change ((c + w - 1) * dedekindZeta K (c + w)) * p.sum (c + w - c) = 1 at hw
  change ((c + w - 1) * dedekindZeta K (c + w)) * q.sum (c + w - c) = 1 at hw'
  simp only [add_sub_cancel_left] at hw hw'
  have hn : (c + w - 1) * dedekindZeta K (c + w) ≠ 0 := by intro he; simp [he] at hw
  exact mul_left_cancel₀ hn (hw.trans hw'.symm)

/-- For the already constructed inverse, exactly the bounds at 1 < r < 3/2
are missing; no convergence on the boundary is asserted or needed. -/
theorem three_halves_iff_coeff_bounds (t : ℝ) {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hp : 1 ≤ p.radius) (gp : InverseGerm K t p) :
    (∃ q : FormalMultilinearSeries ℂ ℂ ℂ, ENNReal.ofReal (3 / 2) ≤ q.radius ∧ InverseGerm K t q) ↔
    ∀ r : ℝ≥0, 1 < (r : ℝ≥0∞) → (r : ℝ≥0∞) < ENNReal.ofReal (3 / 2) →
      ∃ C : ℝ, ∀ n : ℕ, ‖p n‖ * (r : ℝ) ^ n ≤ C := by
  constructor
  · rintro ⟨q, hq, gq⟩ r _ hr
    have hpos : 0 < ENNReal.ofReal (3 / 2) := ENNReal.ofReal_pos.mpr (by norm_num)
    have he := inverse_unique K t (zero_lt_one.trans_le hp) (hpos.trans_le hq) gp gq
    obtain ⟨C, _, hC⟩ := p.norm_mul_pow_le_of_lt_radius (hr.trans_le (he ▸ hq))
    exact ⟨C,hC⟩
  · intro h
    refine ⟨p, ENNReal.le_of_forall_pos_nnreal_lt ?_, gp⟩
    intro r _ hr
    by_cases hsmall : (r : ℝ≥0∞) ≤ 1
    · exact hsmall.trans hp
    · obtain ⟨C,hC⟩ := h r (lt_of_not_ge hsmall) hr
      exact p.le_radius_of_bound C hC

#print axioms OMA.ReciprocalRadius.zeta_ne_zero
#print axioms OMA.ReciprocalRadius.inverse_on_disk
#print axioms OMA.ReciprocalRadius.radius_one
#print axioms OMA.ReciprocalRadius.three_halves_iff_coeff_bounds

end OMA.ReciprocalRadius
