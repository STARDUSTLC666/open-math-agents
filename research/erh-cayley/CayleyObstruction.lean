import CayleyRecurrence
import CayleyFields

/-! Absolute prefix control for the unmodified forward series cannot reach every radius. -/
noncomputable section
namespace OMA.CayleyObstruction
open Complex Filter Metric Set NumberField CayleyBounds CayleyRecurrence ExactRadius
open scoped Topology

private theorem analytic_point {w : ℂ} (hw : ‖w‖ < 1) : AnalyticAt ℂ point w := by
  have hn : 1-w ≠ 0 := sub_ne_zero.mpr (fun e => by rw [← e,norm_one] at hw; exact lt_irrefl _ hw)
  exact (analyticAt_const.add analyticAt_id.div_const).div (analyticAt_const.sub analyticAt_id) hn

variable (K : Type*) [Field K] [NumberField K]

theorem forward_sum {w : ℂ} (hw : ‖w‖ < 1) :
    HasSum (fun n : ℕ => b K n*w^n) (entireReg K (point w)) := by
  let F := fun v => entireReg K (point v)
  have hd : DifferentiableOn ℂ F (ball 0 1) := fun v hv =>
    (((entireReg_diff K) _).comp v (analytic_point (mem_ball_zero_iff.mp hv)).differentiableAt).differentiableWithinAt
  have he : entireReg K =ᶠ[𝓝 (2:ℂ)] raw K := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds (show 1 < (2:ℂ).re by norm_num)] with s hs
    exact (CayleyFields.boundary K).1 s hs
  have hraw : AnalyticAt ℂ (raw K) 2 :=
    ((entireReg_diff K).differentiableOn.analyticOnNhd isOpen_univ _ (mem_univ _)).congr he
  have ht : Tendsto point (𝓝 0) (𝓝 (2:ℂ)) := by
    simpa [point] using (analytic_point (w := 0) (by norm_num)).continuousAt.tendsto
  have hg : F =ᶠ[𝓝 0] (fun v => raw K (point v)) := he.comp_tendsto ht
  apply (Complex.hasSum_taylorSeries_on_ball hd (mem_ball_zero_iff.mpr hw)).congr_fun
  intro n
  simp only [smul_eq_mul,sub_zero,b,div_eq_mul_inv,hg.iteratedDeriv_eq n,
    base_derivatives (raw K) hraw n]
  ring

theorem value_bound {w : ℂ} (hw : ‖w‖ < 1)
    (hp : ∀ n, ∑ j ∈ Finset.range (n+1), ‖b K (j+1)‖*‖w‖^(j+1) ≤ ‖b K 0‖) :
    ‖entireReg K (point w)‖ ≤ 2*‖b K 0‖ := by
  apply le_of_tendsto (forward_sum K hw).tendsto_sum_nat.norm
  apply Eventually.of_forall
  intro n
  cases n with
  | zero => simp [norm_nonneg]
  | succ n =>
    rw [Finset.sum_range_succ']
    simp only [pow_zero,mul_one]
    apply (norm_add_le _ _).trans
    cases n with
    | zero => simp [two_mul,norm_nonneg]
    | succ n =>
      have h := norm_sum_le (Finset.range (n+1)) (fun j => b K (j+1)*w^(j+1))
      simp only [norm_mul,norm_pow] at h
      linarith [hp n]

private theorem real_lower {x : ℝ} (hx : 1 < x) : 1 ≤ ‖dedekindZeta K (x:ℂ)‖ := by
  have h := EulerBoundary.zeta341 K x 0 hx
  have he : EulerBoundary.pt x 0 = (x:ℂ) := by apply Complex.ext <;> simp [EulerBoundary.pt]
  rw [mul_zero,he,norm_mul,norm_mul,norm_pow,norm_pow] at h
  have hl : 1 ≤ ‖dedekindZeta K (x:ℂ)‖^8 := by convert h using 1 <;> ring
  by_contra! hlt
  exact (pow_lt_one₀ (norm_nonneg _) hlt (by decide : (8:ℕ) ≠ 0)).not_ge hl

theorem prefix_violation :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∃ n : ℕ,
      ‖b K 0‖ < ∑ j ∈ Finset.range (n+1), ‖b K (j+1)‖*r^(j+1) := by
  let x : ℝ := 2*‖b K 0‖+3
  have hx : 2 < x := by dsimp [x]; linarith [norm_nonneg (b K 0)]
  let w : ℂ := ((x:ℂ)-2)/((x:ℂ)+1/16)
  obtain ⟨hunit,hback⟩ := R_ERH_extended_riemann_hypothesis_R3_H2_R1_H2_R1.inverse_coordinate
    (s := (x:ℂ)) (show 31/32 < x by linarith)
  have hcoord : point w = (x:ℂ) := hback
  have hne : w ≠ 0 := by
    intro h
    rw [h] at hcoord
    have e := congrArg Complex.re hcoord
    norm_num [point] at e
    linarith
  refine ⟨‖w‖,norm_pos_iff.mpr hne,hunit,?_⟩
  by_contra! hp
  have h := value_bound K hunit hp
  rw [hcoord,(CayleyFields.boundary K).1 _ (show 1<x by linarith),norm_mul] at h
  have hnorm : ‖(x:ℂ)-1‖ = x-1 := by
    rw [← ofReal_one,← ofReal_sub,Complex.norm_of_nonneg (by linarith)]
  rw [hnorm] at h
  have hl := le_mul_of_one_le_right (show 0 ≤ x-1 by linarith) (real_lower K (by linarith : 1 < x))
  dsimp only [x] at h hl
  linarith

#print axioms forward_sum
#print axioms value_bound
#print axioms prefix_violation
end OMA.CayleyObstruction
