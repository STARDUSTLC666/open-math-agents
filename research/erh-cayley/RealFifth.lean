import QuarticDisk
import ZeroAtOrigin
import CentralRadius
import Mathlib.NumberTheory.NumberField.CMField

/-! The maximal real subfield of the fifth cyclotomic field has absolute
discriminant five. In a central interval its nearest zero is the origin. -/
noncomputable section
namespace OMA.RealFifth
open Complex NumberField NumberField.InfinitePlace Metric
open GeneralStrip GeneralSlope RadialProfile ExactRadius ThetaContinuation QuarticDisk
open scoped NumberField

abbrev F := maximalRealSubfield Fifth

private theorem square_divisor {m : ℕ} (h : m^2 ∣ 125) : m=1 ∨ m=5 := by
  have hl := Nat.le_of_dvd (by decide : 0 < 125) h
  have hm : m ≤ 11 := by
    by_contra! hn
    have h12 : 12 ≤ m := by omega
    have hh := Nat.pow_le_pow_left h12 2
    norm_num at hh
    omega
  interval_cases m <;> norm_num at *

theorem invariants : Module.finrank ℚ F = 2 ∧ nrRealPlaces F = 2 ∧
    nrComplexPlaces F = 0 ∧ (discr F).natAbs = 5 := by
  let A : Algebra ℚ Fifth := DivisionRing.toRatAlgebra
  have hcyc : @IsCyclotomicExtension {5} ℚ Fifth _ _ A := by
    rw [Subsingleton.elim A (CyclotomicField.algebra 5 ℚ)]; infer_instance
  let : @IsCyclotomicExtension {5} ℚ Fifth _ _ DivisionRing.toRatAlgebra := hcyc
  let : IsCMField Fifth := IsCyclotomicExtension.Rat.isCMField Fifth (S := ({5} : Set ℕ))
    ⟨5, by simp, by decide⟩
  have hrel : Module.finrank F Fifth = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have ht := Module.finrank_mul_finrank ℚ F Fifth
  rw [hrel, fifth_invariants.1] at ht
  have hdeg : Module.finrank ℚ F = 2 := by omega
  refine ⟨hdeg, (IsTotallyReal.finrank F).symm.trans hdeg, IsTotallyReal.nrComplexPlaces_eq_zero F, ?_⟩
  have he := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow F (𝓞 F) Fifth (𝓞 Fifth)
  rw [hrel, fifth_invariants.2] at he
  have hdiv : (discr F).natAbs^2 ∣ 125 := by
    change _ ∣ (125:ℤ).natAbs
    rw [he]; exact dvd_mul_left _ _
  have hl := NumberField.abs_discr_gt_two (K := F) (by omega)
  have hlarge : 2 < (discr F).natAbs := by
    exact_mod_cast (show (2:ℤ) < ((discr F).natAbs : ℤ) by simpa only [Int.natCast_natAbs] using hl)
  exact (square_divisor hdiv).resolve_left (by omega)

variable (K : Type*) [Field K] [NumberField K]

private theorem gammaR_ne_of_im_ne {z : ℂ} (hi : z.im ≠ 0) : Gammaℝ z ≠ 0 := by
  intro h
  obtain ⟨n, rfl⟩ := Gammaℝ_eq_zero_iff.mp h
  simp at hi

theorem left_zero_real {z : ℂ} (hz : z ∈ zeros K) (hr : z.re ≤ 0) : z.im = 0 := by
  by_contra hn
  have hne : z ≠ 0 := by rintro rfl; exact hn rfl
  have ha := (CentralRadius.left_zero_iff_arch K hne hr).mp hz
  have hc : Gammaℂ z ≠ 0 := by
    rw [← Gammaℝ_mul_Gammaℝ_add_one]
    exact mul_ne_zero (gammaR_ne_of_im_ne hn) (gammaR_ne_of_im_ne (by simpa using hn))
  exact (mul_ne_zero (mul_ne_zero (exp_ne_zero _) (pow_ne_zero _ (gammaR_ne_of_im_ne hn)))
    (pow_ne_zero _ hc)) ha

theorem exact_at_origin_zero (hzero : (0:ℂ) ∈ zeros K) {t T : ℝ}
    (hheight : ∀ z ∈ zeros K, 0 < z.re → T < |z.im|)
    (ht : |t| ≤ T) (hgap : 4+t^2 ≤ 1+(T-|t|)^2) :
    zeroDistance K t = Real.sqrt (4+t^2) := by
  have hd0 : dist (center t) 0 ^ 2 = 4+t^2 := by
    rw [dist_eq_norm, sub_zero, Complex.sq_norm, normSq_apply]
    change 2*2+t*t=4+t^2; ring
  rw [← hd0, Real.sqrt_sq dist_nonneg]
  refine le_antisymm (infDist_le_dist_of_mem hzero) ?_
  obtain ⟨z,hz,he⟩ := nearest K t
  rw [he]
  apply (sq_le_sq₀ dist_nonneg dist_nonneg).mp
  have hs : dist (center t) z ^ 2 = (2-z.re)^2+(t-z.im)^2 := by
    rw [dist_eq_norm, Complex.sq_norm, normSq_apply, sq, sq]; rfl
  rw [hd0, hs]
  rcases le_or_gt z.re 0 with hr | hr
  · rw [left_zero_real K hz hr, sub_zero]
    nlinarith [sq_nonneg z.re]
  · have hhor : 1 < 2-z.re := by linarith [zeros_left K hz]
    have htri : |z.im| ≤ |t|+|t-z.im| := by
      simpa only [add_sub_cancel, abs_sub_comm z.im t] using abs_add_le t (z.im-t)
    have hv : T-|t| ≤ |t-z.im| := by linarith [hheight z hz hr]
    have hvsq := (sq_le_sq₀ (sub_nonneg.mpr ht) (abs_nonneg _)).mpr hv
    rw [sq_abs] at hvsq
    have hhsq := (sq_le_sq₀ zero_le_one (zero_le_one.trans hhor.le)).mpr hhor.le
    linarith

private theorem slope_lower : (14/5:ℝ) ≤ slopeRate F := by
  obtain ⟨hd, _, _, hD⟩ := invariants
  have hd' : degree F = 2 := by unfold degree; rw [hd]; norm_num
  rw [slopeRate_eq, hD, hd']
  change 14/5 ≤ 2*Real.pi/(5:ℝ)^(1/2:ℝ)
  rw [← Real.sqrt_eq_rpow, le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num))]
  have hs : Real.sqrt 5 ≤ 56/25 := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp
    rw [Real.sq_sqrt (by norm_num)]; norm_num
  linarith [Real.pi_gt_d2]

theorem exact_radius {t : ℝ} (ht : |t| ≤ 1/3) :
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ, p.radius = ENNReal.ofReal (Real.sqrt (4+t^2)) ∧
      ReciprocalRadius.InverseGerm F t p := by
  have hq := slope_lower
  have hprod : (14/5)*((14/5)-1) ≤ slopeRate F*(slopeRate F-1) :=
    mul_le_mul hq (by linarith) (by norm_num) (by linarith)
  have hzeros (z : ℂ) (hz : z ∈ zeros F) (hp : 0 < z.re) : 17/8 < |z.im| := by
    apply (sq_lt_sq₀ (by norm_num) (abs_nonneg _)).mp
    rw [sq_abs]; linarith [zero_height F (by linarith) hz hp]
  have hzero := ZeroAtOrigin.origin_mem F (by rw [invariants.2.1]; omega)
  have hgap : 4+t^2 ≤ 1+(17/8-|t|)^2 := by nlinarith [sq_abs t]
  have hd := exact_at_origin_zero F hzero hzeros (by linarith : |t| ≤ 17/8) hgap
  obtain ⟨p,hp,hg⟩ := AllFieldRadius.all_fields_radius_gt_one F t
  exact ⟨p, (radius_eq_zeroDistance F t (zero_lt_one.trans hp) hg).trans (congrArg ENNReal.ofReal hd), hg⟩

theorem maximum_two_places {t : ℝ} (ht : |t| ≤ 1/3) :
    (2 ≤ nrRealPlaces F + nrComplexPlaces F) ∧
    (∃ p : FormalMultilinearSeries ℂ ℂ ℂ, p.radius = ENNReal.ofReal (Real.sqrt (4+t^2)) ∧
      ReciprocalRadius.InverseGerm F t p) ∧
    (∀ (L : Type) [Field L] [NumberField L], 2 ≤ nrRealPlaces L + nrComplexPlaces L →
      ∀ p : FormalMultilinearSeries ℂ ℂ ℂ, 0 < p.radius → ReciprocalRadius.InverseGerm L t p →
        p.radius ≤ ENNReal.ofReal (Real.sqrt (4+t^2))) := by
  exact ⟨by rw [invariants.2.1]; omega, exact_radius ht,
    fun L _ _ h p hp hg => ZeroAtOrigin.radius_le_origin_distance L h t hp hg⟩

#print axioms invariants
#print axioms left_zero_real
#print axioms exact_at_origin_zero
#print axioms exact_radius
#print axioms maximum_two_places
end OMA.RealFifth
