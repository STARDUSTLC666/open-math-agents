import DiscriminantRanges
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic

/-! Discriminants, infinite places, and reciprocal zeta disks for the third
and fourth cyclotomic fields. -/

noncomputable section
namespace OMA.CyclotomicDisks

open NumberField NumberField.InfinitePlace
open IsCyclotomicExtension.Rat

private theorem cyclotomic_over_rat (n : ℕ) (A : Algebra ℚ (CyclotomicField n ℚ)) :
    @IsCyclotomicExtension {n} ℚ (CyclotomicField n ℚ) _ _ A := by
  rw [Subsingleton.elim A (CyclotomicField.algebra n ℚ)]
  infer_instance

theorem gaussian_invariants :
    nrRealPlaces (CyclotomicField 4 ℚ) = 0 ∧
    nrComplexPlaces (CyclotomicField 4 ℚ) = 1 ∧
    NumberField.discr (CyclotomicField 4 ℚ) = -4 := by
  let := cyclotomic_over_rat 4 DivisionRing.toRatAlgebra
  refine ⟨nrRealPlaces_eq_zero (n := 4) _ (by decide), ?_, ?_⟩
  · rw [nrComplexPlaces_eq_totient_div_two 4]
    decide
  · rw [IsCyclotomicExtension.Rat.discr_prime_pow_succ 2 1 (CyclotomicField 4 ℚ)]
    norm_num

theorem eisenstein_invariants :
    nrRealPlaces (CyclotomicField 3 ℚ) = 0 ∧
    nrComplexPlaces (CyclotomicField 3 ℚ) = 1 ∧
    NumberField.discr (CyclotomicField 3 ℚ) = -3 := by
  let := cyclotomic_over_rat 3 DivisionRing.toRatAlgebra
  refine ⟨nrRealPlaces_eq_zero (n := 3) _ (by decide), ?_, ?_⟩
  · rw [nrComplexPlaces_eq_totient_div_two 3]
    decide
  · rw [IsCyclotomicExtension.Rat.discr_prime 3 (CyclotomicField 3 ℚ)]
    norm_num

theorem gaussian_radius {t : ℝ} (ht : |t| ≤ 5/3) :
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ, ENNReal.ofReal (3/2) < p.radius ∧
      ReciprocalRadius.InverseGerm (CyclotomicField 4 ℚ) t p := by
  obtain ⟨hr, hc, hd⟩ := gaussian_invariants
  exact DiscriminantRanges.certified_windows _ hr hc (.inr (.inl ⟨by rw [hd]; decide, ht⟩))

theorem eisenstein_radius {t : ℝ} (ht : |t| ≤ 13/6) :
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ, ENNReal.ofReal (3/2) < p.radius ∧
      ReciprocalRadius.InverseGerm (CyclotomicField 3 ℚ) t p := by
  obtain ⟨hr, hc, hd⟩ := eisenstein_invariants
  exact DiscriminantRanges.certified_windows _ hr hc (.inl ⟨by rw [hd]; decide, ht⟩)

#print axioms gaussian_invariants
#print axioms eisenstein_invariants
#print axioms gaussian_radius
#print axioms eisenstein_radius

end OMA.CyclotomicDisks
