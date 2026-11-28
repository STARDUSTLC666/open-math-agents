import CayleyBounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Finite triangular equations for the reciprocal arithmetic coefficients.
The numerator derivatives needed at each order are evaluated at s = 2. -/
noncomputable section
namespace OMA.CayleyRecurrence
open Complex Filter Set NumberField CayleyBounds
open scoped Topology

def coeff (f : ℂ → ℂ) (n : ℕ) := iteratedDeriv n f 0 / n.factorial

def op (f : ℂ → ℂ) (s : ℂ) := (16/33)*(s+1/16)^2*deriv f s

private theorem point_deriv {w : ℂ} (hw : w ≠ 1) :
    HasDerivAt point ((16/33)*(point w+1/16)^2) w := by
  have hd := sub_ne_zero.mpr hw.symm
  have hnum : HasDerivAt (fun z : ℂ => 2+z/16) (1/16) w :=
    ((hasDerivAt_id w).div_const 16).const_add 2
  have hden : HasDerivAt (fun z : ℂ => 1-z) (-1) w := by
    simpa using (hasDerivAt_id w).const_sub (1:ℂ)
  have he : point w+1/16 = (33/16)/(1-w) := by
    apply (eq_div_iff hd).mpr
    rw [add_mul,show point w*(1-w) = 2+w/16 from div_mul_cancel₀ _ hd]
    ring
  apply (hnum.div hden hd).congr_deriv
  rw [he]
  field_simp [hd]
  <;> ring

private theorem op_analytic {f : ℂ → ℂ} {s : ℂ} (hf : AnalyticAt ℂ f s) :
    AnalyticAt ℂ (op f) s :=
  (analyticAt_const.mul ((analyticAt_id.add analyticAt_const).pow 2)).mul hf.deriv

theorem base_derivatives (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 2) (n : ℕ) :
    iteratedDeriv n (fun w => f (point w)) 0 = (op^[n] f) 2 := by
  induction n generalizing f with
  | zero => simp [point]
  | succ n ih =>
    rw [iteratedDeriv_succ',Function.iterate_succ_apply]
    have ht : Tendsto point (𝓝 0) (𝓝 (2:ℂ)) := by
      simpa [point] using (point_deriv (w := 0) (by norm_num)).continuousAt.tendsto
    have hg : deriv (fun w => f (point w)) =ᶠ[𝓝 0] (fun w => op f (point w)) := by
      filter_upwards [ht hf.eventually_analyticAt,eventually_ne_nhds (by norm_num : (0:ℂ)≠1)] with w hw hne
      have h := (hw.differentiableAt.hasDerivAt.comp w (point_deriv hne)).deriv
      simpa only [Function.comp_def,op,mul_comm] using h
    exact (hg.iteratedDeriv_eq n).trans (ih (op f) (op_analytic hf))

theorem product_coeff {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (n : ℕ) :
    coeff (f*g) n = ∑ j ∈ Finset.range (n+1), coeff f j * coeff g (n-j) := by
  unfold coeff
  rw [iteratedDeriv_mul hf.contDiffAt hg.contDiffAt,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hc : (n.choose j:ℂ)*j.factorial*(n-j).factorial = n.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hjn
  have hn : (n.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hk : (j.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hd : ((n-j).factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n-j)
  field_simp [hn,hk,hd]
  linear_combination iteratedDeriv j f 0 * iteratedDeriv (n-j) g 0 * hc

def raw (K : Type*) [Field K] [NumberField K] (s : ℂ) := (s-1)*dedekindZeta K s
def b (K : Type*) [Field K] [NumberField K] (n : ℕ) := (op^[n] (raw K)) 2 / n.factorial

private theorem origin {K : Type*} [Field K] [NumberField K]
    {W : ℂ → ℂ} (hW : Differentiable ℂ W)
    (ha : ∀ s : ℂ, 1 < s.re → W s = (s-1)*dedekindZeta K s) :
    AnalyticAt ℂ (raw K) 2 := by
  apply (hW.differentiableOn.analyticOnNhd isOpen_univ _ (mem_univ _)).congr
  filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds (show 1 < (2:ℂ).re by norm_num)] with z hz
  exact ha z hz

theorem reciprocal_system (K : Type*) [Field K] [NumberField K]
    (hraw : AnalyticAt ℂ (raw K) 2) (h0 : raw K 2 ≠ 0) :
    coeff (germ K) 0 = (b K 0)⁻¹ ∧ ∀ n : ℕ,
      coeff (germ K) (n+1) = -(∑ j ∈ Finset.range (n+1), b K (j+1)*coeff (germ K) (n-j))/(b K 0) := by
  let B := fun w => raw K (point w)
  have hp : AnalyticAt ℂ point 0 := (analyticAt_const.add analyticAt_id.div_const).div
    (analyticAt_const.sub analyticAt_id) (by norm_num : (1:ℂ)-0 ≠ 0)
  have hB : AnalyticAt ℂ B 0 := (show AnalyticAt ℂ (raw K) (point 0) by simpa [point] using hraw).comp hp
  have hn : B 0 ≠ 0 := by simpa [B,point] using h0
  have hG : AnalyticAt ℂ (germ K) 0 := hB.inv hn
  have hb (n : ℕ) : coeff B n = b K n := by
    unfold coeff b
    rw [show iteratedDeriv n B 0 = _ from base_derivatives (raw K) hraw n]
  have hb0 : b K 0 ≠ 0 := by simpa [b] using h0
  constructor
  · simp [germ,raw,coeff,b,point]
  intro n
  have he : B * germ K =ᶠ[𝓝 0] (fun _ : ℂ => 1) := by
    filter_upwards [hB.continuousAt.eventually_ne hn] with w hw
    exact mul_inv_cancel₀ hw
  have hprod := product_coeff hB hG (n+1)
  have hz : coeff (B*germ K) (n+1) = 0 := by
    rw [coeff,he.iteratedDeriv_eq,iteratedDeriv_const]
    simp
  rw [hz,Finset.sum_range_succ'] at hprod
  simp only [hb,Nat.sub_zero,Nat.succ_sub_succ_eq_sub] at hprod
  apply (eq_div_iff hb0).mpr
  linear_combination -hprod

theorem arithmetic_recurrence (h1 : R_ERH_extended_riemann_hypothesis_R3_H2_R1_H2_R1.H1)
    (K : Type) [Field K] [NumberField K] :
    coeff (germ K) 0 = (b K 0)⁻¹ ∧ ∀ n : ℕ,
      coeff (germ K) (n+1) = -(∑ j ∈ Finset.range (n+1), b K (j+1)*coeff (germ K) (n-j))/(b K 0) := by
  obtain ⟨W,hW,ha,hfree⟩ := h1 K
  have hn := hfree (2:ℂ) (by norm_num)
  rw [ha 2 (by norm_num)] at hn
  exact reciprocal_system K (origin hW ha) hn

theorem weighted_inverse_bound (a u : ℕ → ℂ) {r : ℝ} (hr : 0 ≤ r)
    (hu : u 0 ≠ 0)
    (hstep : ∀ n, a (n+1) = -(∑ j ∈ Finset.range (n+1), u (j+1)*a (n-j))/u 0)
    (hprefix : ∀ n, ∑ j ∈ Finset.range (n+1), ‖u (j+1)‖*r^(j+1) ≤ ‖u 0‖) :
    ∀ n, ‖a n‖*r^n ≤ ‖a 0‖ := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [hstep,norm_div,norm_neg,div_mul_eq_mul_div,div_le_iff₀ (norm_pos_iff.mpr hu)]
      calc
        ‖∑ j ∈ Finset.range (n+1), u (j+1)*a (n-j)‖*r^(n+1)
            ≤ (∑ j ∈ Finset.range (n+1), ‖u (j+1)*a (n-j)‖)*r^(n+1) :=
          mul_le_mul_of_nonneg_right (norm_sum_le _ _) (pow_nonneg hr _)
        _ = ∑ j ∈ Finset.range (n+1), (‖u (j+1)‖*r^(j+1))*(‖a (n-j)‖*r^(n-j)) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j hj
          have hjn := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
          have hp : r^(n+1) = r^(j+1)*r^(n-j) := by
            rw [← pow_add]
            congr 1
            omega
          rw [norm_mul,hp]
          ring
        _ ≤ ∑ j ∈ Finset.range (n+1), (‖u (j+1)‖*r^(j+1))*‖a 0‖ := by
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_left (ih (n-j) (by omega)) (mul_nonneg (norm_nonneg _) (pow_nonneg hr _))
        _ ≤ ‖a 0‖*‖u 0‖ := by
          rw [← Finset.sum_mul,mul_comm (‖a 0‖)]
          exact mul_le_mul_of_nonneg_right (hprefix n) (norm_nonneg _)

theorem bound_of_prefix (h1 : R_ERH_extended_riemann_hypothesis_R3_H2_R1_H2_R1.H1)
    (K : Type) [Field K] [NumberField K] {r : ℝ} (hr : 0 ≤ r)
    (hprefix : ∀ n, ∑ j ∈ Finset.range (n+1), ‖b K (j+1)‖*r^(j+1) ≤ ‖b K 0‖) :
    bound K r := by
  obtain ⟨W,_,ha,hfree⟩ := h1 K
  have h0 := hfree (2:ℂ) (by norm_num)
  rw [ha 2 (by norm_num)] at h0
  have hb : b K 0 ≠ 0 := by simpa [b,raw] using h0
  exact ⟨‖coeff (germ K) 0‖,weighted_inverse_bound _ _ hr hb (arithmetic_recurrence h1 K).2 hprefix⟩

#print axioms base_derivatives
#print axioms product_coeff
#print axioms reciprocal_system
#print axioms arithmetic_recurrence
#print axioms weighted_inverse_bound
#print axioms bound_of_prefix
end OMA.CayleyRecurrence
