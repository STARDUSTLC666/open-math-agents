import CayleySmoothing
import ZetaGrowth

/-! A sufficient finite difference order for every number field. -/
noncomputable section
namespace OMA.CayleyHigher
open Complex Filter Set Metric NumberField CayleyBounds CayleyRecurrence CayleySmoothing ExactRadius
open scoped Topology

def difference (u : ℕ → ℂ) : ℕ → ℂ
  | 0 => u 0
  | n+1 => u (n+1)-u n

private theorem linear_coeff (n : ℕ) : coeff (fun w : ℂ => 1-w) n =
    if n = 0 then 1 else if n = 1 then -1 else 0 := by
  cases n with
  | zero => simp [coeff]
  | succ n =>
    have he : deriv (fun w : ℂ => 1-w) = fun _ => -1 := by
      funext w
      simpa using ((hasDerivAt_id w).const_sub (1:ℂ)).deriv
    rw [coeff,iteratedDeriv_succ',he,iteratedDeriv_const]
    cases n <;> simp

theorem linear_difference {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    coeff (fun w => (1-w)*f w) = difference (coeff f) := by
  funext n
  cases n with
  | zero => simp [coeff,difference]
  | succ n =>
    change coeff ((fun w : ℂ => 1-w)*f) (n+1) = coeff f (n+1)-coeff f n
    have hlin : AnalyticAt ℂ (fun w : ℂ => 1-w) 0 := analyticAt_const.sub analyticAt_id
    rw [product_coeff hlin hf,Finset.sum_range_succ',Finset.sum_range_succ']
    simp [linear_coeff]
    <;> ring

variable (K : Type*) [Field K] [NumberField K]

theorem difference_formula (m : ℕ) :
    coeff (damp (entireReg K) m) = difference^[m] (b K) := by
  induction m with
  | zero =>
    have he : damp (entireReg K) 0 = CayleyDifference.forward K := by
      funext w
      simp [damp,CayleyDifference.forward]
    rw [he]
    funext n
    exact CayleyDifference.forward_coeff K n
  | succ m ih =>
    have he : damp (entireReg K) (m+1) = fun w => (1-w)*damp (entireReg K) m w := by
      funext w
      rw [damp,damp,pow_succ]
      ring
    rw [he,linear_difference ((damp_analytic _ (entireReg_diff K) m) 0
      (mem_ball_self (by norm_num : (0:ℝ)<1))),ih,Function.iterate_succ_apply']

theorem halfplane_growth : ∃ C : ℝ, 1 ≤ C ∧
    ∀ s : ℂ, -(1/2:ℝ) ≤ s.re → ‖entireReg K s‖ ≤ C*(4+‖s‖)^ZetaGrowth.power K := by
  obtain ⟨S,hS,hs⟩ := ZetaGrowth.polynomial_strip K
  obtain ⟨B,hB⟩ := DedekindMellin.bounded K (a := 3/2) (by norm_num)
  let C := max S B
  have hC : 1 ≤ C := hS.trans (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro s hleft
  by_cases hright : s.re ≤ 3/2
  · apply (hs s ⟨hleft,hright⟩).trans
    exact mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ (by positivity)
      (add_le_add (le_refl 4) (abs_im_le_norm s)) _) (by positivity) (by linarith)
  · have hp : 1 < s.re := by linarith [lt_of_not_ge hright]
    rw [(CayleyFields.boundary K).1 s hp,norm_mul,mul_comm]
    have hbase : 1 ≤ 4+‖s‖ := by linarith [norm_nonneg s]
    have hl : ‖s-1‖ ≤ 4+‖s‖ := (norm_sub_le _ _).trans (by simp; linarith)
    exact mul_le_mul ((hB s (lt_of_not_ge hright).le).trans (le_max_right _ _))
      (hl.trans (le_self_pow₀ hbase (Nat.succ_ne_zero _))) (norm_nonneg _) (by linarith)

abbrev order := Module.finrank ℚ K + 5

theorem decay : ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ,
    ‖(difference^[order K] (b K)) (n+2)‖ ≤ M/(((n:ℝ)+1)*(n+2)) := by
  obtain ⟨C,hC,hg⟩ := halfplane_growth K
  have hC0 := zero_le_one.trans hC
  refine ⟨32768*C*20^(ZetaGrowth.power K),by positivity,?_⟩
  rw [← difference_formula]
  exact coefficient_decay _ (damp_analytic _ (entireReg_diff K) (order K))
    (second_bound _ (entireReg_diff K) (ZetaGrowth.power K) hC0 (fun s hs => hg s (by linarith)))

theorem summable_differences : Summable fun n => ‖(difference^[order K] (b K)) n‖ := by
  obtain ⟨C,hC,hg⟩ := halfplane_growth K
  rw [← difference_formula]
  exact absolute_coefficients _ (entireReg_diff K) (ZetaGrowth.power K) (zero_le_one.trans hC)
    (fun s hs => hg s (by linarith))

theorem damp_zero_iff {m : ℕ} {w : ℂ} (hw : ‖w‖ < 1) :
    damp (entireReg K) m w = 0 ↔ entireReg K (point w) = 0 := by
  have hn : 1-w ≠ 0 := sub_ne_zero.mpr (fun e => by rw [← e,norm_one] at hw; exact lt_irrefl _ hw)
  simp [damp,hn]

#print axioms linear_difference
#print axioms difference_formula
#print axioms halfplane_growth
#print axioms decay
#print axioms summable_differences
#print axioms damp_zero_iff
end OMA.CayleyHigher
