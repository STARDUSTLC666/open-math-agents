import ThetaMoment
import RationalRadius

/-! Unconditional low-height certificates for the actual reciprocal germ
of the Dedekind ideal series of any degree-one number field. -/
noncomputable section
namespace OMA.LowHeight
open Complex NumberField Set Metric RationalRadius ThetaMoment
open scoped ENNReal Topology

theorem zero_free_six {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (hi : |s.im| ≤ 6) :
    riemannZeta s ≠ 0 := by
  have hs : s ≠ 0 := by rintro rfl; norm_num at h0
  have hs' : 1-s ≠ 0 := sub_ne_zero.mpr (by rintro rfl; norm_num at h1)
  have hn := moment_bound (s := s) (by linarith) (by linarith)
  have hs2 : ‖s‖^2 ≤ 37 := by
    rw [Complex.sq_norm, normSq_apply]
    nlinarith [sq_le_sq₀ (abs_nonneg s.im) (by norm_num : (0:ℝ) ≤ 6) |>.mpr hi,
      sq_abs s.im, mul_self_le_mul_self h0.le h1.le]
  have ht2 : ‖1-s‖^2 ≤ 37 := by
    rw [Complex.sq_norm, normSq_apply]
    simp only [sub_re, sub_im, one_re, one_im, zero_sub, neg_mul_neg]
    nlinarith [sq_le_sq₀ (abs_nonneg s.im) (by norm_num : (0:ℝ) ≤ 6) |>.mpr hi,
      sq_abs s.im, mul_self_le_mul_self (by linarith : 0 ≤ 1-s.re) (by linarith : 1-s.re ≤ 1)]
  have hprod : ‖s‖ * ‖1-s‖ ≤ 37 := by nlinarith [sq_nonneg (‖s‖ - ‖1-s‖)]
  intro hz
  rw [riemannZeta_def_of_ne_zero hs] at hz
  have hc := (div_eq_zero_iff.mp hz).resolve_right (Gammaℝ_ne_zero_of_re_pos h0)
  rw [completedRiemannZeta_eq] at hc
  have he : completedRiemannZeta₀ s = 1/s + 1/(1-s) := by linear_combination hc
  have hidentity : s * (1-s) * completedRiemannZeta₀ s = 1 := by
    rw [he]; field_simp [hs, hs']; ring
  have hnorm := congrArg (fun z : ℂ => ‖z‖) hidentity
  simp only [norm_mul, norm_one] at hnorm
  have hu : ‖completedRiemannZeta₀ s‖ ≤ 1/40 := by linarith [Real.pi_lt_d4]
  have hsmall := mul_le_mul hprod hu (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 37)
  linarith

/-- Left of the strip, reflection excludes all but the negative even integers. -/
theorem zero_cases {z : ℂ} (hz : z ∈ riemannZetaZeros) :
    (∃ n : ℕ, z = -2*((n:ℂ)+1)) ∨ (0 < z.re ∧ z.re < 1 ∧ 6 < |z.im|) := by
  have hzero := mem_riemannZetaZeros.mp hz
  have hr : z.re < 1 := lt_of_not_ge fun h => riemannZeta_ne_zero_of_one_le_re h hzero
  rcases lt_or_ge 0 z.re with hp | hp
  · exact .inr ⟨hp,hr,lt_of_not_ge fun hi => zero_free_six hp hr hi hzero⟩
  left
  have hn : z ≠ 0 := by rintro rfl; rw [riemannZeta_zero] at hzero; norm_num at hzero
  have hG : Gammaℝ z = 0 := by
    by_contra hG
    rw [riemannZeta_def_of_ne_zero hn] at hzero
    have hc := (div_eq_zero_iff.mp hzero).resolve_right hG
    have hR : 1 ≤ (1-z).re := by rw [sub_re,one_re]; linarith
    apply riemannZeta_ne_zero_of_one_le_re hR
    rw [riemannZeta_def_of_ne_zero (by intro e; rw [e] at hR; norm_num at hR),
      completedRiemannZeta_one_sub, hc, zero_div]
  obtain ⟨n,he⟩ := Gammaℝ_eq_zero_iff.mp hG
  cases n with
  | zero => simp at he; exact (hn he).elim
  | succ n => exact ⟨n,by simpa [neg_mul] using he⟩

private theorem real_dist_sq (t x : ℝ) :
    dist (center t) (x:ℂ) ^ 2 = (2-x)^2 + t^2 := by
  rw [dist_eq_norm, Complex.sq_norm, normSq_apply]
  simp [RationalRadius.center,sq]

private theorem first_dist (t : ℝ) : dist (center t) (-2) = Real.sqrt (16+t^2) := by
  have h := real_dist_sq t (-2)
  norm_num at h
  rw [← h,Real.sqrt_sq dist_nonneg]

private theorem first_le_trivial (t : ℝ) (n : ℕ) :
    dist (center t) (-2) ≤ dist (center t) (-2*((n:ℂ)+1)) := by
  apply (sq_le_sq₀ dist_nonneg dist_nonneg).mp
  have h := real_dist_sq t (-2)
  have h' := real_dist_sq t (-2*((n:ℝ)+1))
  push_cast at h h'
  rw [h,h']
  apply add_le_add_left
  apply (sq_le_sq₀ (by norm_num) (by nlinarith [Nat.cast_nonneg (α := ℝ) n])).mpr
  linarith [Nat.cast_nonneg (α := ℝ) n]

private theorem vertical (t : ℝ) (z : ℂ) : |z.im| ≤ |t| + dist (center t) z := by
  have h := abs_im_le_norm (center t - z)
  change |t-z.im| ≤ ‖center t - z‖ at h
  rw [dist_eq_norm]
  calc |z.im| = |t + (z.im-t)| := by rw [add_sub_cancel]
       _ ≤ |t| + |z.im-t| := abs_add_le _ _
       _ ≤ _ := add_le_add_right (by rwa [abs_sub_comm z.im t]) _

/-- The nearest zeta zero is at distance |(2+it)-(-2)| throughout this
explicit interval; in particular this gives the exact central radius 4. -/
theorem distance_small {t : ℝ} (ht : |t| ≤ 5/3) :
    zeroDistance t = Real.sqrt (16+t^2) := by
  rw [← first_dist]
  have hm : (-2 : ℂ) ∈ riemannZetaZeros := mem_riemannZetaZeros.mpr (by
    simpa using riemannZeta_neg_two_mul_nat_add_one 0)
  apply le_antisymm (infDist_le_dist_of_mem hm)
  change dist (center t) (-2) ≤ zeroDistance t
  obtain ⟨z,hz,he⟩ := nearest_zero t
  rw [he]
  rcases zero_cases hz with ⟨n,rfl⟩ | ⟨_,_,him⟩
  · exact first_le_trivial t n
  · have h : dist (center t) (-2) ≤ 6 - |t| := by
      apply (sq_le_sq₀ dist_nonneg (by linarith)).mp
      have he := real_dist_sq t (-2)
      norm_num at he
      nlinarith [sq_abs t]
    linarith [vertical t z]

theorem distance_three_halves {t : ℝ} (ht : |t| ≤ 9/2) : 3/2 < zeroDistance t := by
  obtain ⟨z,hz,he⟩ := nearest_zero t
  rw [he]
  rcases zero_cases hz with ⟨n,rfl⟩ | ⟨_,_,him⟩
  · have h := real_dist_sq t (-2)
    norm_num at h
    have hlow : (3:ℝ)/2 < dist (center t) (-2) := by nlinarith [sq_nonneg t, dist_nonneg (x := center t) (y := (-2:ℂ))]
    exact hlow.trans_le (first_le_trivial t n)
  · linarith [vertical t z]

theorem degree_one_exact_low {K : Type*} [Field K] [NumberField K] (hk : Module.finrank ℚ K = 1)
    {t : ℝ} (ht : |t| ≤ 5/3) {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hp : 0 < p.radius) (hg : ReciprocalRadius.InverseGerm K t p) :
    p.radius = ENNReal.ofReal (Real.sqrt (16+t^2)) := by
  rw [degree_one_radius_eq hk t hp hg, distance_small ht]

theorem degree_one_three_halves_low {K : Type*} [Field K] [NumberField K]
    (hk : Module.finrank ℚ K = 1) {t : ℝ} (ht : |t| ≤ 9/2) :
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ, ENNReal.ofReal (3/2) < p.radius ∧
      ReciprocalRadius.InverseGerm K t p := by
  obtain ⟨p,hp,hg⟩ := ReciprocalRadius.radius_one K t
  rw [ENNReal.ofReal_one] at hp
  refine ⟨p, ?_, hg⟩
  rw [degree_one_radius_eq hk t (zero_lt_one.trans_le hp) hg]
  exact (ENNReal.ofReal_lt_ofReal_iff (by linarith [distance_three_halves ht])).mpr (distance_three_halves ht)

theorem degree_one_radius_four {K : Type*} [Field K] [NumberField K]
    (hk : Module.finrank ℚ K = 1) :
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ, p.radius = 4 ∧ ReciprocalRadius.InverseGerm K 0 p := by
  obtain ⟨p,hp,hg⟩ := ReciprocalRadius.radius_one K 0
  rw [ENNReal.ofReal_one] at hp
  refine ⟨p, ?_, hg⟩
  rw [degree_one_exact_low hk (show |(0:ℝ)| ≤ 5/3 by norm_num) (zero_lt_one.trans_le hp) hg]
  norm_num

#print axioms OMA.LowHeight.zero_free_six
#print axioms OMA.LowHeight.zero_cases
#print axioms OMA.LowHeight.distance_small
#print axioms OMA.LowHeight.degree_one_exact_low
#print axioms OMA.LowHeight.degree_one_three_halves_low
#print axioms OMA.LowHeight.degree_one_radius_four
end OMA.LowHeight
