import SmallEndpoint

/-! A bound on the height of zeros gives a Euclidean distance bound for
reciprocal disks. Separate zeros with nonpositive real part, whose distance
to 2+it is already at least two. -/

noncomputable section
namespace OMA.DiskGeometry

open Complex NumberField NumberField.InfinitePlace
open ExactRadius QuadraticMoment SmallEndpoint ThetaContinuation
variable (K : Type*) [Field K] [NumberField K]

theorem zero_height_sq (hr : nrRealPlaces K = 0) (hc : nrComplexPlaces K = 1)
    (hD : (discr K).natAbs ≤ 4) {z : ℂ} (hz : z ∈ zeros K) (hpos : 0 < z.re) :
    29/6 < z.im ^ 2 := by
  have hC := norm_pos_iff.mpr (cst_ne K)
  have hzero := zero_obstruction K hr hc hz hpos
  have hM : 0 < endpoint K := by
    by_contra! h
    have := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (norm_nonneg z) (norm_nonneg (z-1))) h
    linarith
  have hA : ‖z‖^2 = z.re^2 + z.im^2 := by
    rw [Complex.sq_norm, normSq_apply]; ring
  have hB : ‖z-1‖^2 = (z.re-1)^2 + z.im^2 := by
    rw [Complex.sq_norm, normSq_apply]; simp [sq]
  have hprod : ‖z‖ * ‖z-1‖ < z.im^2 + 1/2 := by
    nlinarith [sq_nonneg (‖z‖-‖z-1‖), mul_pos hpos (sub_pos.mpr (zeros_left K hz))]
  by_contra! h
  have hsmall : ‖z‖ * ‖z-1‖ < 16/3 := by linarith
  have hstrict := mul_lt_mul_of_pos_right hsmall hM
  linarith [endpoint_bound K hr hc (small_discriminant_rate K hD)]

/-- The two alternatives also cover the endpoint at radius two, where a
zero could have real part zero. -/
theorem distance_of_zero_height {T t : ℝ}
    (hzeros : ∀ z ∈ zeros K, 0 < z.re → T < |z.im|) (ht : |t| ≤ T) :
    2 ≤ zeroDistance K t ∨ 1 + (T-|t|)^2 < (zeroDistance K t)^2 := by
  obtain ⟨z, hz, he⟩ := nearest K t
  rw [he, dist_eq_norm]
  rcases le_or_gt z.re 0 with h | h
  · left
    have hd := re_le_norm (center t - z)
    change 2-z.re ≤ ‖center t-z‖ at hd
    linarith
  · right
    have hs : ‖center t-z‖^2 = (2-z.re)^2 + (t-z.im)^2 := by
      rw [Complex.sq_norm, normSq_apply, sq, sq]
      rfl
    have htriangle : |z.im| ≤ |t| + |t-z.im| := by
      calc |z.im| = |t+(z.im-t)| := by rw [add_sub_cancel]
           _ ≤ |t|+|z.im-t| := abs_add_le _ _
           _ = _ := by rw [abs_sub_comm z.im t]
    have hvert : T-|t| < |t-z.im| := by linarith [hzeros z hz h]
    have hvsq := (sq_lt_sq₀ (sub_nonneg.mpr ht) (abs_nonneg _)).mpr hvert
    rw [sq_abs] at hvsq
    have hhor : 1 < 2-z.re := by linarith [zeros_left K hz]
    have hhsq := (sq_lt_sq₀ zero_le_one (zero_le_one.trans hhor.le)).mpr hhor
    rw [hs]
    linarith

/-- For a small-discriminant imaginary quadratic field, the height threshold
is the square root of the explicit zero-height bound. -/
theorem small_discriminant_distance (hr : nrRealPlaces K = 0) (hc : nrComplexPlaces K = 1)
    (hD : (discr K).natAbs ≤ 4) {t : ℝ} (ht : |t| ≤ Real.sqrt (29/6)) :
    2 ≤ zeroDistance K t ∨ 1 + (Real.sqrt (29/6)-|t|)^2 < (zeroDistance K t)^2 := by
  apply distance_of_zero_height K _ ht
  intro z hz hp
  apply (sq_lt_sq₀ (Real.sqrt_nonneg _) (abs_nonneg _)).mp
  rw [Real.sq_sqrt (by norm_num), sq_abs]
  exact zero_height_sq K hr hc hD hz hp

private theorem thirteen_sixths_le : 13/6 ≤ Real.sqrt (29/6) := by
  apply (sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (by norm_num)]
  norm_num

theorem radius_gt_three_halves (hr : nrRealPlaces K = 0) (hc : nrComplexPlaces K = 1)
    (hD : (discr K).natAbs ≤ 4) {t : ℝ} (ht : |t| ≤ 1) :
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ, ENNReal.ofReal (3/2) < p.radius ∧
      ReciprocalRadius.InverseGerm K t p := by
  have hmargin : 7/6 ≤ Real.sqrt (29/6)-|t| := by linarith [thirteen_sixths_le]
  have hsq := (sq_le_sq₀ (by norm_num) (by linarith : 0 ≤ Real.sqrt (29/6)-|t|)).mpr hmargin
  have hd : 3/2 < zeroDistance K t := by
    rcases small_discriminant_distance K hr hc hD (t := t) (by linarith) with h | h
    · linarith
    · apply (sq_lt_sq₀ (by norm_num) (by linarith [distance_gt_one K t])).mp
      linarith
  obtain ⟨p, hp, hg⟩ := AllFieldRadius.all_fields_radius_gt_one K t
  refine ⟨p, ?_, hg⟩
  rw [radius_eq_zeroDistance K t (zero_lt_one.trans hp) hg]
  exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hd

theorem radius_ge_two (hr : nrRealPlaces K = 0) (hc : nrComplexPlaces K = 1)
    (hD : (discr K).natAbs ≤ 4) {t : ℝ} (ht : |t| ≤ 2/5) :
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ, ENNReal.ofReal 2 ≤ p.radius ∧
      ReciprocalRadius.InverseGerm K t p := by
  have hmargin : 53/30 ≤ Real.sqrt (29/6)-|t| := by linarith [thirteen_sixths_le]
  have hsq := (sq_le_sq₀ (by norm_num) (by linarith : 0 ≤ Real.sqrt (29/6)-|t|)).mpr hmargin
  have hd : 2 ≤ zeroDistance K t := by
    rcases small_discriminant_distance K hr hc hD (t := t) (by linarith) with h | h
    · exact h
    · apply (sq_le_sq₀ (by norm_num) (by linarith [distance_gt_one K t])).mp
      linarith
  obtain ⟨p, hp, hg⟩ := AllFieldRadius.all_fields_radius_gt_one K t
  refine ⟨p, ?_, hg⟩
  rw [radius_eq_zeroDistance K t (zero_lt_one.trans hp) hg]
  exact ENNReal.ofReal_le_ofReal hd

#print axioms zero_height_sq
#print axioms distance_of_zero_height
#print axioms small_discriminant_distance
#print axioms radius_gt_three_halves
#print axioms radius_ge_two
end OMA.DiskGeometry
