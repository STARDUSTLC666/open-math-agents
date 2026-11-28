import CayleyObstruction

/-! Linear normalization of the forward series and exact transfer of the reciprocal bounds. -/
noncomputable section
namespace OMA.CayleyDifference
open Complex Filter Set Metric NumberField CayleyBounds CayleyRecurrence ExactRadius
open scoped Topology

def forward (K : Type*) [Field K] [NumberField K] (w : ℂ) := entireReg K (point w)
def normalized (K : Type*) [Field K] [NumberField K] (w : ℂ) := (1-w)*forward K w
def inverse (K : Type*) [Field K] [NumberField K] (w : ℂ) := germ K w/(1-w)
def c (K : Type*) [Field K] [NumberField K] := coeff (normalized K)
def d (K : Type*) [Field K] [NumberField K] := coeff (inverse K)

theorem point_analytic {w : ℂ} (hw : ‖w‖ < 1) : AnalyticAt ℂ point w := by
  exact (analyticAt_const.add analyticAt_id.div_const).div (analyticAt_const.sub analyticAt_id)
    (sub_ne_zero.mpr (fun e => by rw [← e,norm_one] at hw; exact lt_irrefl _ hw))

variable (K : Type*) [Field K] [NumberField K]

theorem forward_analytic {w : ℂ} (hw : ‖w‖ < 1) : AnalyticAt ℂ (forward K) w :=
  ((entireReg_diff K).differentiableOn.analyticOnNhd isOpen_univ _ (mem_univ _)).comp (point_analytic hw)

private theorem near_arithmetic :
    forward K =ᶠ[𝓝 (0:ℂ)] fun w => raw K (point w) := by
  have ht := (point_analytic (w := 0) (by norm_num)).continuousAt.tendsto
  have hright : ∀ᶠ w : ℂ in 𝓝 0, 1 < (point w).re :=
    ht ((isOpen_lt continuous_const continuous_re).mem_nhds (show 1 < (point 0).re by norm_num [point]))
  filter_upwards [hright] with w hw
  exact (CayleyFields.boundary K).1 _ hw

theorem forward_coeff (n : ℕ) : coeff (forward K) n = b K n := by
  have hraw : AnalyticAt ℂ (raw K) 2 := by
    apply ((entireReg_diff K).differentiableOn.analyticOnNhd isOpen_univ _ (mem_univ _)).congr
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds (show 1 < (2:ℂ).re by norm_num)] with z hz
    exact (CayleyFields.boundary K).1 _ hz
  unfold coeff b
  rw [(near_arithmetic K).iteratedDeriv_eq n,base_derivatives _ hraw n]

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

private theorem coeff_difference {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (n : ℕ) :
    coeff (fun w => (1-w)*f w) (n+1) = coeff f (n+1)-coeff f n := by
  change coeff ((fun w : ℂ => 1-w)*f) (n+1) = _
  have hlin : AnalyticAt ℂ (fun w : ℂ => 1-w) 0 := analyticAt_const.sub analyticAt_id
  rw [product_coeff hlin hf,Finset.sum_range_succ',Finset.sum_range_succ']
  simp [linear_coeff]
  <;> ring

theorem first_differences :
    c K 0 = b K 0 ∧ ∀ n : ℕ, c K (n+1) = b K (n+1)-b K n := by
  constructor
  · rw [← forward_coeff K 0]
    simp [c,normalized,coeff]
  · intro n
    change coeff (fun w => (1-w)*forward K w) (n+1) = _
    rw [coeff_difference (forward_analytic K (by norm_num)),forward_coeff,forward_coeff]

private theorem germ_analytic : AnalyticAt ℂ (germ K) 0 := by
  have hn : forward K 0 ≠ 0 := (CayleyFields.boundary K).2 _ (by norm_num [point])
  apply ((forward_analytic K (w := 0) (by norm_num)).inv hn).congr
  filter_upwards [near_arithmetic K] with w hw
  exact congrArg Inv.inv hw

theorem inverse_differences :
    coeff (germ K) 0 = d K 0 ∧ ∀ n, coeff (germ K) (n+1) = d K (n+1)-d K n := by
  constructor
  · simp [d,coeff,inverse]
  · intro n
    have hg : germ K =ᶠ[𝓝 0] (fun w => (1-w)*inverse K w) := by
      filter_upwards [eventually_ne_nhds (by norm_num : (0:ℂ)≠1)] with w hw
      dsimp [inverse]
      field_simp [sub_ne_zero.mpr hw.symm]
    have hU : AnalyticAt ℂ (inverse K) 0 :=
      (germ_analytic K).div (analyticAt_const.sub analyticAt_id) (by norm_num)
    calc coeff (germ K) (n+1) = coeff (fun w => (1-w)*inverse K w) (n+1) := by
           simp only [coeff,hg.iteratedDeriv_eq (n+1)]
         _ = _ := coeff_difference hU n

theorem inverse_partial_sums (n : ℕ) :
    d K n = ∑ j ∈ Finset.range (n+1), coeff (germ K) j := by
  induction n with
  | zero => simpa using (inverse_differences K).1.symm
  | succ n ih =>
    rw [Finset.sum_range_succ,← ih]
    linear_combination -(inverse_differences K).2 n

theorem bound_iff {r : ℝ} (hr : 0 ≤ r) (h1 : r < 1) :
    bound K r ↔ ∃ M : ℝ, ∀ n, ‖d K n‖*r^n ≤ M := by
  change (∃ C : ℝ, ∀ n, ‖coeff (germ K) n‖*r^n ≤ C) ↔ _
  constructor
  · rintro ⟨C,hC⟩
    let M := C/(1-r)
    have he : M*(1-r)=C := div_mul_cancel₀ _ (sub_pos.mpr h1).ne'
    have hc0 : 0 ≤ C := (norm_nonneg _).trans (by simpa using hC 0)
    have hm : 0 ≤ M := div_nonneg hc0 (sub_pos.mpr h1).le
    have hcm : C ≤ M := by nlinarith [mul_nonneg hm hr]
    refine ⟨M,fun n => ?_⟩
    induction n with
    | zero => rw [← (inverse_differences K).1]; exact (hC 0).trans hcm
    | succ n ih =>
      have hstep : d K (n+1) = coeff (germ K) (n+1)+d K n := by
        rw [(inverse_differences K).2,sub_add_cancel]
      rw [hstep]
      calc _ ≤ (‖coeff (germ K) (n+1)‖ + ‖d K n‖)*r^(n+1) :=
             mul_le_mul_of_nonneg_right (norm_add_le _ _) (pow_nonneg hr _)
           _ = ‖coeff (germ K) (n+1)‖*r^(n+1)+(‖d K n‖*r^n)*r := by rw [pow_succ]; ring
           _ ≤ C+M*r := add_le_add (hC _) (mul_le_mul_of_nonneg_right ih hr)
           _ = M := by linarith only [he]
  · rintro ⟨M,hM⟩
    have hm : 0 ≤ M := (norm_nonneg _).trans (by simpa using hM 0)
    refine ⟨M+M*r,fun n => ?_⟩
    cases n with
    | zero => rw [(inverse_differences K).1]; exact (hM 0).trans (le_add_of_nonneg_right (mul_nonneg hm hr))
    | succ n =>
      rw [(inverse_differences K).2]
      calc _ ≤ (‖d K (n+1)‖+‖d K n‖)*r^(n+1) :=
             mul_le_mul_of_nonneg_right (norm_sub_le _ _) (pow_nonneg hr _)
           _ = ‖d K (n+1)‖*r^(n+1)+(‖d K n‖*r^n)*r := by rw [pow_succ]; ring
           _ ≤ _ := add_le_add (hM _) (mul_le_mul_of_nonneg_right (hM _) hr)

theorem normalized_sum {w : ℂ} (hw : ‖w‖ < 1) :
    HasSum (fun n => c K n*w^n) (normalized K w) := by
  have hd : DifferentiableOn ℂ (normalized K) (ball 0 1) := fun v hv =>
    (((analyticAt_const.sub analyticAt_id).mul
      (forward_analytic K (mem_ball_zero_iff.mp hv))).differentiableAt).differentiableWithinAt
  apply (Complex.hasSum_taylorSeries_on_ball hd (mem_ball_zero_iff.mpr hw)).congr_fun
  intro n
  simp only [c,coeff,sub_zero,smul_eq_mul,div_eq_mul_inv]
  ring

theorem bound_of_difference_prefix {r : ℝ} (hr : 0 ≤ r) (h1 : r < 1)
    (hp : ∀ n, ∑ j ∈ Finset.range (n+1), ‖c K (j+1)‖*r^(j+1) ≤ ‖c K 0‖) :
    bound K r := by
  have hF := forward_analytic K (w := 0) (by norm_num)
  have hn : forward K 0 ≠ 0 := (CayleyFields.boundary K).2 _ (by norm_num [point])
  have hc0 : c K 0 ≠ 0 := by simpa [c,coeff,normalized] using hn
  have hN : AnalyticAt ℂ (normalized K) 0 := (analyticAt_const.sub analyticAt_id).mul hF
  have hI : AnalyticAt ℂ (inverse K) 0 :=
    (germ_analytic K).div (analyticAt_const.sub analyticAt_id) (by norm_num)
  have he : normalized K * inverse K =ᶠ[𝓝 (0:ℂ)] (fun _ => 1) := by
    filter_upwards [near_arithmetic K,hF.continuousAt.eventually_ne hn,
      eventually_ne_nhds (by norm_num : (0:ℂ)≠1)] with w hw hf hw1
    change ((1-w)*forward K w)*((raw K (point w))⁻¹/(1-w)) = 1
    rw [← hw]
    field_simp [hf,sub_ne_zero.mpr hw1.symm]
  have hstep (n : ℕ) : d K (n+1) =
      -(∑ j ∈ Finset.range (n+1), c K (j+1)*d K (n-j))/(c K 0) := by
    have hprod := product_coeff hN hI (n+1)
    have hz : coeff (normalized K * inverse K) (n+1) = 0 := by
      rw [coeff,he.iteratedDeriv_eq,iteratedDeriv_const]
      simp
    rw [hz,Finset.sum_range_succ'] at hprod
    simp only [Nat.sub_zero,Nat.succ_sub_succ_eq_sub] at hprod
    apply (eq_div_iff hc0).mpr
    dsimp only [c,d]
    linear_combination -hprod
  exact (bound_iff K hr h1).mpr ⟨‖d K 0‖,weighted_inverse_bound _ _ hr hc0 hstep hp⟩

#print axioms forward_coeff
#print axioms first_differences
#print axioms inverse_differences
#print axioms inverse_partial_sums
#print axioms bound_iff
#print axioms normalized_sum
#print axioms bound_of_difference_prefix
end OMA.CayleyDifference
