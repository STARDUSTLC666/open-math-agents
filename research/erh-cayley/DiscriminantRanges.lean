import DiskGeometry
import StripHeat

/-! Explicit ranges for the H2 disk, from a lower bound for the heat decay
rate and the horizontal separation between its center and the strip. -/
noncomputable section
namespace OMA.DiscriminantRanges
open NumberField NumberField.InfinitePlace
open ExactRadius HeatDecay
variable (K : Type*) [Field K] [NumberField K]

private theorem rate_lower {D : ℕ} (hD : (discr K).natAbs ≤ D) {a : ℝ}
    (ha : 0 ≤ a) (hsq : a^2 * D ≤ (2*3.14)^2) : a ≤ rate K := by
  let d : ℝ := (discr K).natAbs
  have hd : 0 < d := by dsimp [d]; exact_mod_cast Int.natAbs_pos.mpr (discr_ne_zero K)
  have hdD : d ≤ D := by dsimp [d]; exact_mod_cast hD
  have hp : 2*3.14 ≤ 2*Real.pi := by linarith [Real.pi_gt_d2]
  change a ≤ 2*Real.pi / Real.sqrt d
  rw [le_div_iff₀ (Real.sqrt_pos.mpr hd)]
  apply (sq_le_sq₀ (mul_nonneg ha (Real.sqrt_nonneg _)) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt hd.le]
  exact (mul_le_mul_of_nonneg_left hdD (sq_nonneg a)).trans
    (hsq.trans ((sq_le_sq₀ (by norm_num) (by positivity)).mpr hp))

/-- Every number in this test is real or an integer. The target is the
actual inverse germ for the original ideal series. -/
theorem radius_of_bounds (hr : nrRealPlaces K = 0) (hc : nrComplexPlaces K = 1)
    {D : ℕ} {a b t : ℝ} (hD : (discr K).natAbs ≤ D) (ha : 1 ≤ a)
    (hq : a^2 * D ≤ (2*3.14)^2) (hgap : (b+28/25)^2 ≤ (a-1)*(a+1/2))
    (ht : |t| ≤ b) :
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ, ENNReal.ofReal (3/2) < p.radius ∧
      ReciprocalRadius.InverseGerm K t p := by
  have haq := rate_lower K hD (zero_le_one.trans ha) hq
  have hprod : (a-1)*(a+1/2) ≤ (rate K-1)*(rate K+1/2) := by
    apply mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have hzero (z : ℂ) (hz : z ∈ zeros K) (hp : 0 < z.re) : b+28/25 < |z.im| := by
    apply (sq_lt_sq₀ (by linarith [abs_nonneg t]) (abs_nonneg _)).mp
    rw [sq_abs]
    exact (hgap.trans hprod).trans_lt (StripHeat.zero_height_rate K hr hc hz hp)
  have hd : 3/2 < zeroDistance K t := by
    rcases DiskGeometry.distance_of_zero_height K (t := t) hzero (by linarith) with hr | hr
    · linarith
    · have hm : 28/25 ≤ b+28/25-|t| := by linarith
      have := (sq_le_sq₀ (by norm_num) (by linarith : 0 ≤ b+28/25-|t|)).mpr hm
      apply (sq_lt_sq₀ (by norm_num) (by linarith [distance_gt_one K t])).mp
      linarith
  obtain ⟨p, hp, hg⟩ := AllFieldRadius.all_fields_radius_gt_one K t
  refine ⟨p, ?_, hg⟩
  rw [radius_eq_zeroDistance K t (zero_lt_one.trans hp) hg]
  exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hd

theorem certified_windows (hr : nrRealPlaces K = 0) (hc : nrComplexPlaces K = 1)
    {t : ℝ} (h :
      ((discr K).natAbs ≤ 3 ∧ |t| ≤ 13/6) ∨
      ((discr K).natAbs ≤ 4 ∧ |t| ≤ 5/3) ∨
      ((discr K).natAbs ≤ 8 ∧ |t| ≤ 2/3) ∨
      ((discr K).natAbs ≤ 11 ∧ |t| ≤ 1/4) ∨
      ((discr K).natAbs ≤ 15 ∧ |t| ≤ 1/50)) :
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ, ENNReal.ofReal (3/2) < p.radius ∧
      ReciprocalRadius.InverseGerm K t p := by
  rcases h with ⟨hD, ht⟩ | ⟨hD, ht⟩ | ⟨hD, ht⟩ | ⟨hD, ht⟩ | ⟨hD, ht⟩
  · exact radius_of_bounds K hr hc (a := 29/8) hD (by norm_num) (by norm_num) (by norm_num) ht
  · exact radius_of_bounds K hr hc (a := 3.14) hD (by norm_num) (by norm_num) (by norm_num) ht
  · exact radius_of_bounds K hr hc (a := 11/5) hD (by norm_num) (by norm_num) (by norm_num) ht
  · exact radius_of_bounds K hr hc (a := 15/8) hD (by norm_num) (by norm_num) (by norm_num) ht
  · exact radius_of_bounds K hr hc (a := 81/50) hD (by norm_num) (by norm_num) (by norm_num) ht

#print axioms radius_of_bounds
#print axioms certified_windows
end OMA.DiscriminantRanges
