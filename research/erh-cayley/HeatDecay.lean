import QuadraticMoment
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Positive heat kernels of imaginary quadratic fields.  Compare the
same ideal at two scales; the first positive ideal norm is at least one. -/
noncomputable section
namespace OMA.HeatDecay
open Complex NumberField NumberField.InfinitePlace Real Set MeasureTheory
open ThetaContinuation
open scoped NumberField
variable (K : Type*) [Field K] [NumberField K]

def rate : ℝ := 2*Real.pi / Real.sqrt ((discr K).natAbs : ℝ)
def term (x : ℝ) (n : ℕ) : ℝ := if n=0 then 0 else
  (ReciprocalRadius.a K n : ℝ) * Real.exp (-(rate K*x*n))
def heat (x : ℝ) : ℝ := 2 * ∑' n, term K x n

theorem rate_pos : 0 < rate K := div_pos (by positivity) (Real.sqrt_pos.mpr
  (by exact_mod_cast Int.natAbs_pos.mpr (discr_ne_zero K)))

theorem term_nonneg (x : ℝ) (n : ℕ) : 0 ≤ term K x n := by unfold term; split <;> positivity
theorem heat_nonneg (x : ℝ) : 0 ≤ heat K x := mul_nonneg (by norm_num) (tsum_nonneg (term_nonneg K x))

theorem sum_term {x : ℝ} (hx : 0 < x) : Summable (term K x) := by
  let u := rate K*x
  have hu : 0 < u := mul_pos (rate_pos K) hx
  have hs := (ReciprocalRadius.series_summable K (s := 2) (by norm_num)).norm
  apply Summable.of_nonneg_of_le (term_nonneg K x) _ (hs.mul_left (2/u^2))
  intro n
  by_cases hn : n=0
  · subst n; simp [term]
  · have hn' : 0 < (n:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have he := Real.pow_div_factorial_le_exp (u*n) (mul_nonneg hu.le hn'.le) 2
    norm_num at he
    have hb : Real.exp (-(u*n)) ≤ (2/u^2) / (n:ℝ)^2 := by
      rw [Real.exp_neg]
      apply (le_div_iff₀ (sq_pos_of_pos hn')).mpr
      apply (le_div_iff₀ (sq_pos_of_pos hu)).mpr
      rw [inv_mul_eq_div,div_mul_eq_mul_div,div_le_iff₀ (Real.exp_pos _)]
      nlinarith
    rw [term,if_neg hn,LSeries.term_of_ne_zero hn,Complex.cpow_ofNat,norm_div,norm_pow,
      Complex.norm_natCast,Complex.norm_natCast]
    calc _ ≤ (ReciprocalRadius.a K n : ℝ)*((2/u^2)/(n:ℝ)^2) :=
                mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
         _ = _ := by ring

theorem kernel_eq (hr : nrRealPlaces K = 0) (hc : nrComplexPlaces K = 1)
    {x : ℝ} (hx : 0 < x) : DedekindMellin.kernel K x = (heat K x : ℂ) := by
  have he := R_ERH_extended_riemann_hypothesis_R1_H1_R1_H2_R1.kernel_expansion_of_signature K hr hc hx
  change DedekindMellin.kernel K x = _ at he
  rw [he,heat,ofReal_mul,ofReal_ofNat,ofReal_tsum]
  congr 1; apply tsum_congr; intro n
  by_cases h : n=0
  · simp [term,h]
  · simp only [term,h,if_false,rate,ofReal_mul,ofReal_natCast,ReciprocalRadius.a,ReciprocalRadius.fiber]

theorem contraction {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    heat K y ≤ Real.exp (-(rate K*(y-x))) * heat K x := by
  let m := Real.exp (-(rate K*(y-x)))
  have H (n : ℕ) : term K y n ≤ m * term K x n := by
    by_cases hn : n=0
    · simp [term,hn]
    · simp only [term,hn,if_false]
      rw [mul_left_comm m]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      rw [show m = Real.exp (-(rate K*(y-x))) from rfl,← Real.exp_add,Real.exp_le_exp]
      have h := mul_nonneg (mul_nonneg (rate_pos K).le (sub_nonneg.mpr hxy))
        (sub_nonneg.mpr (show 1 ≤ (n:ℝ) by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn))
      linarith only [show rate K*(y-x)*((n:ℝ)-1) = rate K*y*n-rate K*x*n-rate K*(y-x) by ring,h]
  have h := (sum_term K (hx.trans_le hxy)).tsum_le_tsum H ((sum_term K hx).mul_left m)
  rw [tsum_mul_left] at h
  unfold heat; rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left h (by norm_num)

private theorem num_exp : 17/4 ≤ Real.exp (3/2) ∧ Real.exp (-3) ≤ 1/8 := by
  have hE : (27/10:ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h3 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 27/10) hE 3
  have he3 : (Real.exp 1)^3 = Real.exp 3 := by
    rw [show (3:ℝ)=1+1+1 by norm_num, Real.exp_add, Real.exp_add]; ring
  have he2 : (Real.exp (3/2))^2 = Real.exp 3 := by rw [sq, ← Real.exp_add]; norm_num
  rw [he3] at h3
  constructor
  · nlinarith [he2,Real.exp_pos (3/2)]
  · rw [Real.exp_neg,inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    norm_num; linarith

/-- Finite difference of the theta FE at 2: C=H(1/2)-2H(2).
Use the positive exponential gap; neither a class number nor a special
L-value is needed. -/
theorem four_heat_le_cst (hr : nrRealPlaces K = 0) (hc : nrComplexPlaces K = 1)
    (hq : 3 ≤ rate K) : 4*heat K 1 ≤ ‖cst K‖ := by
  have fe := (pair K).h_feq 2 (by norm_num)
  change DedekindMellin.kernel K (1/2) + cst K = (1*(((2:ℝ)^(1:ℝ):ℝ):ℂ)) •
    (DedekindMellin.kernel K 2 + cst K) at fe
  rw [kernel_eq K hr hc (by norm_num),kernel_eq K hr hc (by norm_num),
    Real.rpow_one,ofReal_ofNat,one_mul,smul_eq_mul] at fe
  have hC := congrArg Complex.re fe
  simp only [add_re,ofReal_re,mul_re,re_ofNat,im_ofNat,zero_mul,sub_zero] at hC
  have small := contraction K (x := 1/2) (y := 1) (by norm_num) (by norm_num)
  have large := contraction K (x := 1) (y := 2) (by norm_num) (by norm_num)
  have hs : (17/4) * heat K 1 ≤ heat K (1/2) := by
    have hx : Real.exp (rate K*(1-1/2)) * heat K 1 ≤ heat K (1/2) := by
      rw [Real.exp_neg,← div_eq_inv_mul, le_div_iff₀ (Real.exp_pos _)] at small
      rwa [mul_comm]
    exact (mul_le_mul_of_nonneg_right (num_exp.1.trans (Real.exp_le_exp.mpr (by linarith))) (heat_nonneg K _)).trans hx
  have hl : heat K 2 ≤ (1/8) * heat K 1 := large.trans
    (mul_le_mul_of_nonneg_right ((Real.exp_le_exp.mpr (by linarith : -(rate K*(2-1)) ≤ -3)).trans num_exp.2) (heat_nonneg K _))
  linarith [re_le_norm (cst K)]

#print axioms OMA.HeatDecay.sum_term
#print axioms OMA.HeatDecay.contraction
#print axioms OMA.HeatDecay.four_heat_le_cst
end OMA.HeatDecay
