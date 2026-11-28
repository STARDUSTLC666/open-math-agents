import ExactRadius

/-! The real radial profile underlying the Dedekind theta kernel in every
signature. The logarithmic hyperplane forces its Gaussian energy to be at
least the degree. -/
noncomputable section
namespace OMA.RadialProfile

open Complex NumberField NumberField.InfinitePlace NumberField.Units
open NumberField.Units.dirichletUnitTheorem MeasureTheory
open OMA.HeckeExpansion
open DedekindUnitDomain DedekindUnitGaussian DedekindOrbitIntegrable DedekindOrbitProfile
open scoped NumberField Classical

variable (K : Type*) [Field K] [NumberField K]

abbrev degree : ℝ := Module.finrank ℚ K
def exponent : ℝ := 2 / degree K
theorem degree_pos : 0 < degree K := by exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
theorem exponent_pos : 0 < exponent K := div_pos zero_lt_two (degree_pos K)

def energy (y : logSpace K) : ℝ :=
  ∑ w : InfinitePlace K, (mult w : ℝ) * dilation K y w ^ 2

theorem degree_le_energy (y : logSpace K) : degree K ≤ energy K y := by
  have hplace (w : InfinitePlace K) :
      (mult w : ℝ) + 2*fullCoordinate K y w ≤ (mult w : ℝ) * dilation K y w ^ 2 := by
    let u := fullCoordinate K y w
    let m : ℝ := mult w
    have hm : 0 < m := zero_lt_one.trans_le one_le_mult
    have he := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (u/m+u/m)) hm.le
    have heq : m*((u/m+u/m)+1) = m+2*u := by field_simp [hm.ne']; ring
    rw [heq, Real.exp_add] at he
    simpa only [dilation, sq, u, m] using he
  have h := Finset.sum_le_sum fun w (_ : w ∈ (Finset.univ : Finset (InfinitePlace K))) => hplace w
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, full_sum, mul_zero, add_zero] at h
  have hdeg : ∑ w : InfinitePlace K, (mult w : ℝ) = degree K := by
    exact_mod_cast (sum_mult_eq (K := K))
  rwa [hdeg] at h

def density (x : ℝ) (y : logSpace K) : ℝ :=
  Real.exp (-(Real.pi * x^(exponent K)) * energy K y)

def radial (x : ℝ) : ℝ := ∫ y : logSpace K, density K x y

private theorem density_eq (x : ℝ) (y : logSpace K) :
    gaussian K (x^(exponent K)) 1 y = (density K x y : ℂ) := by
  simp [gaussian, density, energy]

theorem density_integrable {x : ℝ} (hx : 0 < x) : Integrable (density K x) := by
  have hi := (integrable_one K (Real.rpow_pos_of_pos hx (exponent K))).re
  change Integrable (fun y => (gaussian K (x^(exponent K)) 1 y).re) at hi
  simpa only [density_eq, Complex.ofReal_re] using hi

theorem profile_eq {x : ℝ} (hx : 0 < x) :
    DedekindSignatureKernel.profile (nrRealPlaces K) (nrComplexPlaces K) x = (radial K x : ℂ) := by
  rw [← radial_profile K hx]
  change (∫ y, gaussian K (x^(exponent K)) 1 y) = _
  simp only [density_eq, radial]
  exact integral_complex_ofReal

theorem radial_nonneg (x : ℝ) : 0 ≤ radial K x :=
  integral_nonneg (fun _ => (Real.exp_pos _).le)

theorem radial_contraction {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    radial K y ≤ Real.exp (-(Real.pi * degree K * (y^(exponent K)-x^(exponent K)))) * radial K x := by
  let a := exponent K
  let m := Real.exp (-(Real.pi * degree K * (y^a-x^a)))
  have hd : 0 ≤ y^a-x^a := sub_nonneg.mpr (Real.rpow_le_rpow hx.le hxy (exponent_pos K).le)
  have hp (v : logSpace K) : density K y v ≤ m * density K x v := by
    dsimp only [density, m]
    rw [← Real.exp_add, Real.exp_le_exp]
    have h := mul_le_mul_of_nonneg_left (degree_le_energy K v) (mul_nonneg Real.pi_pos.le hd)
    change -(Real.pi*y^a)*energy K v ≤ -(Real.pi*degree K*(y^a-x^a)) + -(Real.pi*x^a)*energy K v
    linarith only [h, show Real.pi*(y^a-x^a)*energy K v =
      Real.pi*y^a*energy K v-Real.pi*x^a*energy K v by ring,
      show Real.pi*(y^a-x^a)*degree K = Real.pi*degree K*(y^a-x^a) by ring]
  have h := integral_mono (density_integrable K (hx.trans_le hxy)) ((density_integrable K hx).const_mul m) hp
  rwa [integral_const_mul] at h

#print axioms degree_le_energy
#print axioms profile_eq
#print axioms radial_contraction
end OMA.RadialProfile
