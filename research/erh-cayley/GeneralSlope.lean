import GeneralHeat
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! Apply the right derivative at the self-dual point to two explicit
exponential envelopes. This never differentiates the infinite heat sum. -/
noncomputable section
namespace OMA.GeneralSlope
open Complex NumberField Set Filter GeneralHeat RadialProfile ThetaContinuation
open scoped Topology
variable (K : Type*) [Field K] [NumberField K]

def slopeRate : ℝ := GeneralHeat.rate K * exponent K

private def difference (l a x : ℝ) :=
  Real.exp (l*(1-x^(-a))) - x * Real.exp ((-l)*(x^a-1))

private theorem difference_one (l a : ℝ) : difference l a 1 = 0 := by simp [difference]

private theorem difference_deriv (l a : ℝ) : HasDerivAt (difference l a) (2*l*a-1) 1 := by
  have hp (e : ℝ) : HasDerivAt (fun x : ℝ => x^e) e 1 := by
    simpa using (Real.hasDerivAt_rpow_const (x := (1:ℝ)) (p := e) (Or.inl one_ne_zero))
  have h := (((hp (-a)).const_sub 1).const_mul l).exp.sub
    ((hasDerivAt_id 1).fun_mul ((((hp a).sub_const 1).const_mul (-l)).exp))
  have hv : Real.exp (l*(1-(1:ℝ)^(-a))) * (l * - -a) -
      (1*Real.exp (-l*(1^a-1)) + id 1 * (Real.exp (-l*(1^a-1)) * (-l*a))) =
      2*l*a-1 := by simp; ring
  rw [hv] at h
  exact h

private theorem difference_bound {x : ℝ} (hx : 1 < x) :
    difference (GeneralHeat.rate K) (exponent K) x * heat K 1 ≤ (x-1)*(cst K).re := by
  let l := GeneralHeat.rate K
  let a := exponent K
  have hx0 := zero_lt_one.trans hx
  have hS := contraction K (x := x⁻¹) (y := 1) (inv_pos.mpr hx0) (inv_lt_one_of_one_lt₀ hx).le
  rw [Real.one_rpow, Real.exp_neg, ← div_eq_inv_mul, le_div_iff₀ (Real.exp_pos _),
    Real.inv_rpow hx0.le, ← Real.rpow_neg hx0.le] at hS
  have hL := contraction K (x := 1) (y := x) zero_lt_one hx.le
  rw [Real.one_rpow] at hL
  have hL' := mul_le_mul_of_nonneg_left hL hx0.le
  have hfe := heat_inversion K hx0
  change (Real.exp (l*(1-x^(-a))) - x*Real.exp ((-l)*(x^a-1))) * heat K 1 ≤ _
  change heat K 1 * Real.exp (l*(1-x^(-a))) ≤ heat K x⁻¹ at hS
  change x*heat K x ≤ x*(Real.exp (-(l*(x^a-1)))*heat K 1) at hL'
  rw [neg_mul] 
  linarith only [hS, hfe, hL', show (Real.exp (l*(1-x^(-a)))-x*Real.exp (-(l*(x^a-1))))*heat K 1 =
    heat K 1*Real.exp (l*(1-x^(-a)))-x*(Real.exp (-(l*(x^a-1)))*heat K 1) by ring]

theorem self_dual_residue : (2*slopeRate K-1)*heat K 1 ≤ ‖cst K‖ := by
  let f := difference (GeneralHeat.rate K) (exponent K)
  have ht := (hasDerivAt_iff_tendsto_slope_left_right.mp
    (difference_deriv (GeneralHeat.rate K) (exponent K))).2.mul_const (heat K 1)
  have hlim : (2*(GeneralHeat.rate K)*(exponent K)-1)*heat K 1 ≤ (cst K).re := by
    apply le_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin (s := Ioi (1:ℝ))] with x hx
    change slope f 1 x * heat K 1 ≤ _
    rw [slope_def_field, show f 1 = 0 from difference_one _ _, sub_zero,
      div_mul_eq_mul_div, div_le_iff₀ (sub_pos.mpr hx)]
    simpa only [mul_comm (cst K).re] using difference_bound K hx
  unfold slopeRate
  linarith [re_le_norm (cst K)]

/-- This is 2π divided by the root discriminant. -/
theorem slopeRate_eq : slopeRate K =
    2*Real.pi / ((discr K).natAbs : ℝ)^(1/(degree K)) := by
  have hd : 0 < ((discr K).natAbs:ℝ) := by exact_mod_cast Int.natAbs_pos.mpr (discr_ne_zero K)
  rw [slopeRate, GeneralHeat.rate, scale, Real.inv_rpow (Real.sqrt_nonneg _),
    Real.sqrt_eq_rpow, ← Real.rpow_mul hd.le]
  have he : (1/2:ℝ)*exponent K = 1/(degree K) := by unfold exponent; ring
  rw [he]
  unfold exponent
  field_simp [(degree_pos K).ne', (Real.rpow_pos_of_pos hd _).ne']

#print axioms self_dual_residue
#print axioms slopeRate_eq
end OMA.GeneralSlope
