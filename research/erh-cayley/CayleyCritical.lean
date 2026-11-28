import CayleyFiniteGrid

/-! Damped, origin-centered arithmetic Taylor sections for the full critical
half-plane. Every individual test is finite. Existence of passing tests for
all fields and all subdisks is equivalent to ERH and remains open. -/
noncomputable section
namespace OMA.CayleyCritical
open Complex Set Filter Metric NumberField CayleyBounds CayleyRecurrence CayleySmoothing CayleyHigher
open CayleySections ExactRadius
open scoped Topology

def affine (s : ℂ) := (16*s-10)/11
def criticalPoint (w : ℂ) := affine (point w)

theorem critical_formula {w : ℂ} (hw : ‖w‖ < 1) :
    criticalPoint w = (2+w)/(1-w) := by
  have hn : w ≠ 1 := by rintro rfl; simp at hw
  have hd := sub_ne_zero.mpr hn.symm
  have he : point w*(1-w) = 2+w/16 := div_mul_cancel₀ _ hd
  apply (eq_div_iff hd).mpr
  unfold criticalPoint affine
  linear_combination (16/11)*he

theorem image_halfplane {s : ℂ} :
    (∃ w : ℂ, ‖w‖ < 1 ∧ criticalPoint w = s) ↔ 1/2 < s.re := by
  constructor
  · rintro ⟨w,hw,rfl⟩
    have h := point_right hw
    norm_num [criticalPoint,affine]
    linarith
  · intro hs
    let t : ℂ := (11*s+10)/16
    have ht : 31/32 < t.re := by dsimp [t]; norm_num; linarith
    obtain ⟨hw,he⟩ := R_ERH_extended_riemann_hypothesis_R3_H2_R1_H2_R1.inverse_coordinate ht
    refine ⟨_,hw,?_⟩
    change affine (point ((t-2)/(t+1/16))) = s
    rw [show point ((t-2)/(t+1/16)) = t from he]
    unfold affine t
    ring

variable (K : Type*) [Field K] [NumberField K]
def W (s : ℂ) := entireReg K (affine s)
def H := damp (W K) (order K)

/-- Only the germ of the ideal Dirichlet series near s=2 enters these coefficients. -/
def a := coeff (fun w : ℂ => (1-w)^(order K)*raw K (criticalPoint w))

private theorem analytic_affine (s : ℂ) : AnalyticAt ℂ affine s :=
  ((analyticAt_const.mul analyticAt_id).sub analyticAt_const).div_const

private theorem W_diff : Differentiable ℂ (W K) :=
  fun s => ((entireReg_diff K) _).comp s (analytic_affine s).differentiableAt

theorem arithmetic_coeff : coeff (H K) = a K := by
  have hT : AnalyticAt ℂ criticalPoint 0 := (analytic_affine _).comp
    (CayleyDifference.point_analytic (w := 0) (by norm_num))
  have he : H K =ᶠ[𝓝 0] fun w => (1-w)^(order K)*raw K (criticalPoint w) := by
    have hh : ∀ᶠ w : ℂ in 𝓝 0, 1 < (criticalPoint w).re := hT.continuousAt.tendsto
      ((isOpen_lt continuous_const continuous_re).mem_nhds (show 1 < (criticalPoint 0).re by norm_num [criticalPoint,affine,point]))
    filter_upwards [hh] with w hw
    change (1-w)^_*entireReg K (criticalPoint w) = _
    rw [(CayleyFields.boundary K).1 _ hw]
    rfl
  funext n
  exact congrArg (fun v : ℂ => v/n.factorial) (he.iteratedDeriv_eq n)

private theorem growth : ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, (1/3:ℝ) ≤ s.re →
    ‖W K s‖ ≤ C*(4+‖s‖)^ZetaGrowth.power K := by
  obtain ⟨B,hB,hg⟩ := halfplane_growth K
  let p := ZetaGrowth.power K
  refine ⟨B*3^p,by positivity,?_⟩
  intro s hs
  have hre : -(1/2:ℝ) ≤ (affine s).re := by norm_num [affine]; linarith
  have hsize : 4+‖affine s‖ ≤ 3*(4+‖s‖) := by
    have h := norm_sub_le (16*s) (10:ℂ)
    rw [norm_mul] at h
    norm_num at h
    dsimp [affine]
    rw [norm_div]
    norm_num
    linarith [norm_nonneg s]
  apply (hg _ hre).trans
  calc _ ≤ B*(3*(4+‖s‖))^p := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hsize _) (by linarith)
       _ = _ := by rw [mul_pow]; ring

theorem critical_decay : ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, ‖a K (n+2)‖ ≤ M/(((n:ℝ)+1)*(n+2)) := by
  obtain ⟨C,hC,hg⟩ := growth K
  refine ⟨32768*C*20^(ZetaGrowth.power K),by positivity,?_⟩
  rw [← arithmetic_coeff]
  exact coefficient_decay _ (damp_analytic _ (W_diff K) (order K))
    (second_bound _ (W_diff K) (ZetaGrowth.power K) hC hg)

theorem critical_summable : Summable fun n => ‖a K n‖ := by
  obtain ⟨C,hC,hg⟩ := growth K
  rw [← arithmetic_coeff]
  exact absolute_coefficients _ (W_diff K) (ZetaGrowth.power K) hC hg

/-- A single field-dependent constant from the unconditional coefficient estimate. -/
def major := (critical_decay K).choose

theorem critical_tail (N : ℕ) {w : ℂ} (hw : ‖w‖ < 1) :
    ‖H K w-taylorPoly (a K) (N+2) w‖ ≤ major K/((N:ℝ)+1) := by
  apply tail_of_decay _ (critical_decay K).choose_spec.1 (critical_decay K).choose_spec.2 _ N w hw
  intro z hz
  have hd := (damp_analytic _ (W_diff K) (order K)).differentiableOn
  apply (Complex.hasSum_taylorSeries_on_ball hd (mem_ball_zero_iff.mpr hz)).congr_fun
  intro n
  rw [← arithmetic_coeff]
  simp only [H,coeff,smul_eq_mul,sub_zero,div_eq_mul_inv]
  ring

theorem grid_iff_subdisk {r : ℝ} (hr : 0 ≤ r) (h1 : r < 1) :
    (∀ w : ℂ, ‖w‖ ≤ r → entireReg K (criticalPoint w) ≠ 0) ↔
      ∃ N D : ℕ, 0 < D ∧ CayleyFiniteGrid.passes (a K) r (major K/((N:ℝ)+1)) (N+2) D := by
  have he {w : ℂ} (hw : ‖w‖ ≤ r) : (entireReg K (criticalPoint w) ≠ 0) ↔ H K w ≠ 0 := by
    have hn : w ≠ 1 := by rintro rfl; simp at hw; linarith
    simp [H,damp,W,criticalPoint,sub_ne_zero.mpr hn.symm]
  apply (forall_congr' (fun w => forall_congr' (fun hw => he (w := w) hw))).trans
  apply (disk_lower_iff _ (damp_analytic _ (W_diff K) (order K)).continuousOn
    (fun N _ hw => critical_tail K N hw) hr h1).trans
  exact exists_congr fun N => CayleyFiniteGrid.finite_lower_test _ hr h1.le _ _

def subradius (m : ℕ) : ℝ := (m:ℝ)/(m+1)
private theorem radius_mem (m : ℕ) : 0 ≤ subradius m ∧ subradius m < 1 := by
  dsimp [subradius]
  constructor
  · positivity
  · rw [div_lt_one (by positivity : 0 < (m:ℝ)+1)]
    linarith

private theorem covers {r : ℝ} (hr : r < 1) : ∃ m : ℕ, r ≤ subradius m := by
  obtain ⟨m,hm⟩ := exists_nat_gt (1/(1-r))
  have h := (div_lt_iff₀ (sub_pos.mpr hr)).mp hm
  refine ⟨m,(le_div_iff₀ (by positivity : 0 < (m:ℝ)+1)).mpr ?_⟩
  nlinarith only [h,hr]

def tests := ∀ m : ℕ, ∃ N D : ℕ, 0 < D ∧
  CayleyFiniteGrid.passes (a K) (subradius m) (major K/((N:ℝ)+1)) (N+2) D

theorem tests_iff_zeros : tests K ↔ ∀ z ∈ zeros K, z.re ≤ 1/2 := by
  constructor
  · intro h z hz
    by_contra! hr
    obtain ⟨w,hw,he⟩ := image_halfplane.mpr hr
    obtain ⟨m,hm⟩ := covers hw
    have hf := (grid_iff_subdisk K (radius_mem m).1 (radius_mem m).2).mpr (h m) w hm
    exact hf (he.symm ▸ hz)
  · intro h m
    apply (grid_iff_subdisk K (radius_mem m).1 (radius_mem m).2).mp
    intro w hw he
    exact (image_halfplane.mp ⟨w,hw.trans_lt (radius_mem m).2,rfl⟩).not_ge (h _ he)

theorem tests_iff_erh :
    (∀ (L : Type) [Field L] [NumberField L], tests L) ↔
      ∀ (L : Type) [Field L] [NumberField L], ERH.ExtendedRiemannHypothesis L := by
  rw [← ExactRadius.site_h2_iff_erh]
  constructor
  · intro h L _ _
    exact (three_halves_iff L).mpr ((tests_iff_zeros L).mp (h L))
  · intro h L _ _
    exact (tests_iff_zeros L).mpr ((three_halves_iff L).mp (h L))

#print axioms critical_formula
#print axioms image_halfplane
#print axioms arithmetic_coeff
#print axioms critical_decay
#print axioms critical_summable
#print axioms critical_tail
#print axioms grid_iff_subdisk
#print axioms tests_iff_zeros
#print axioms tests_iff_erh
end OMA.CayleyCritical
