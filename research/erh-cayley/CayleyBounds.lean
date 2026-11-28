import OMAReductions.R_ERH_extended_riemann_hypothesis_R3_H2_R1_H2_R1
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-! Unconditional disks for the reciprocal Cayley coefficients of the 31/32 collar. -/
noncomputable section
namespace OMA.CayleyBounds
open Complex Filter Set Metric NumberField
open scoped Topology

def point (w : ℂ) := (2+w/16)/(1-w)
def germ (K : Type*) [Field K] [NumberField K] (w : ℂ) :=
  ((point w-1)*dedekindZeta K (point w))⁻¹

def bound (K : Type*) [Field K] [NumberField K] (r : ℝ) :=
  ∃ C : ℝ, ∀ n : ℕ, ‖iteratedDeriv n (germ K) 0 / n.factorial‖*r^n ≤ C

private theorem point_analytic {w : ℂ} (h : w ≠ 1) : AnalyticAt ℂ point w :=
  (analyticAt_const.add analyticAt_id.div_const).div (analyticAt_const.sub analyticAt_id)
    (sub_ne_zero.mpr h.symm)

private theorem disk_ineq {w : ℂ} {r : ℝ} (hr : r < 1) (hw : ‖w‖ ≤ r) :
    let z := point w
    (z.re-2)^2+z.im^2 ≤ r^2*((z.re+1/16)^2+z.im^2) := by
  let z := point w
  have h1 : w ≠ 1 := by rintro rfl; simp at hw; linarith
  have hz : z*(1-w) = 2+w/16 := div_mul_cancel₀ _ (sub_ne_zero.mpr h1.symm)
  have he : z-2 = w*(z+1/16) := by linear_combination hz
  have hh : ‖z-2‖^2 ≤ r^2*‖z+1/16‖^2 := by
    rw [he,norm_mul,mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg w) hw _) (sq_nonneg _)
  rw [Complex.sq_norm,Complex.sq_norm,Complex.normSq_apply,Complex.normSq_apply] at hh
  norm_num [sub_re,sub_im,add_re,add_im,pow_two] at hh ⊢
  exact hh

theorem point_positive {w : ℂ} {r : ℝ} (hr : r < 1) (hw : ‖w‖ ≤ r) :
    0 < (point w).re := by
  have hg := disk_ineq hr hw
  have hsq : r^2 ≤ 1 := calc
    r^2 ≤ 1^2 := pow_le_pow_left₀ ((norm_nonneg w).trans hw) hr.le 2
    _ = 1 := one_pow _
  have h := mul_le_mul_of_nonneg_right hsq
    (add_nonneg (sq_nonneg ((point w).re+1/16)) (sq_nonneg (point w).im))
  dsimp only at hg
  nlinarith only [h,hg]

theorem left_height {w : ℂ} {r : ℝ} (hr : r < 1) (hw : ‖w‖ ≤ r)
    (hx : (point w).re < 1) :
    1 + (1-r^2)*(point w).im^2 < r^2*(17/16)^2 := by
  let z := point w
  have hp : 0 < z.re := point_positive hr hw
  have hg := disk_ineq hr hw
  change (z.re-2)^2+z.im^2 ≤ r^2*((z.re+1/16)^2+z.im^2) at hg
  change z.re < 1 at hx
  have hl : 1 < (z.re-2)^2 := by nlinarith [sq_nonneg (1-z.re)]
  have hu : (z.re+1/16)^2 ≤ (17/16:ℝ)^2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  have h := mul_le_mul_of_nonneg_left hu (sq_nonneg r)
  change 1+(1-r^2)*z.im^2 < _
  nlinarith only [hl,hg,h]

variable (K : Type*) [Field K] [NumberField K]
variable {W : ℂ → ℂ} (hW : Differentiable ℂ W)
  (ha : ∀ s : ℂ, 1 < s.re → W s = (s-1)*dedekindZeta K s)
include hW ha

private theorem transfer {r : ℝ} (hr : 0 < r) (h1 : r < 1)
    (hf : ∀ w : ℂ, ‖w‖ ≤ r → W (point w) ≠ 0) : bound K r := by
  let U := fun w => (W (point w))⁻¹
  have hd : DifferentiableOn ℂ U (closedBall 0 r) := by
    intro w hw
    have hn := mem_closedBall_zero_iff.mp hw
    have hne : w ≠ 1 := by rintro rfl; simp at hn; linarith
    exact (((hW _).comp w (point_analytic hne).differentiableAt).inv (hf w hn)).differentiableWithinAt
  have ht := (point_analytic (w := 0) (by norm_num)).continuousAt.tendsto
  have he : germ K =ᶠ[𝓝 0] U := by
    have hright : ∀ᶠ w : ℂ in 𝓝 0, 1 < (point w).re :=
      ht ((isOpen_lt continuous_const continuous_re).mem_nhds (show 1 < (point 0).re by norm_num [point]))
    filter_upwards [hright] with w hw
    simp only [U,germ,ha _ hw]
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0:ℂ) r).bddAbove_image hd.continuousOn.norm
  refine ⟨C,fun n => ?_⟩
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr
    (hd.diffContOnCl_ball (Subset.rfl)) (fun w hw => hC (mem_image_of_mem _ (sphere_subset_closedBall hw)))
  rw [he.iteratedDeriv_eq n,norm_div,Complex.norm_natCast]
  have hfac : 0 < (n.factorial:ℝ) := by positivity
  calc ‖iteratedDeriv n U 0‖ / (n.factorial:ℝ) * r^n
      = (‖iteratedDeriv n U 0‖ * r^n) / n.factorial := by ring
    _ ≤ C := (div_le_iff₀ hfac).mpr (by simpa only [mul_comm C] using (le_div_iff₀ (pow_pos hr n)).mp h)

theorem initial_radius (hf : ∀ s : ℂ, 1 ≤ s.re → W s ≠ 0) :
    ∃ r : ℝ, 16/17 < r ∧ r < 1 ∧ bound K r := by
  let U := {w : ℂ | w ≠ 1 ∧ W (point w) ≠ 0}
  have hu : IsOpen U := by
    apply isOpen_iff_mem_nhds.mpr
    intro w hw
    exact inter_mem (eventually_ne_nhds hw.1) ((hW.continuous.continuousAt.comp
      (point_analytic hw.1).continuousAt).eventually_ne hw.2)
  have hs : closedBall (0:ℂ) (16/17) ⊆ U := by
    intro w hw
    have hn := mem_closedBall_zero_iff.mp hw
    refine ⟨fun he => by rw [he,norm_one] at hn; norm_num at hn,hf _ ?_⟩
    by_contra! hx
    have hy := left_height (by norm_num : (16/17:ℝ)<1) hn hx
    nlinarith only [hy,sq_nonneg (point w).im]
  obtain ⟨δ,hδ,hsub⟩ := (isCompact_closedBall (0:ℂ) (16/17)).exists_cthickening_subset_open hu hs
  rw [cthickening_closedBall hδ.le (by norm_num)] at hsub
  obtain ⟨r,hlo,hhi⟩ := exists_between (lt_min (lt_add_of_pos_left _ hδ) (by norm_num : (16/17:ℝ)<1))
  have h1 := hhi.trans_le (min_le_right _ _)
  refine ⟨r,hlo,h1,transfer K hW ha ((by norm_num : (0:ℝ)<16/17).trans hlo) h1 ?_⟩
  intro w hw
  exact (hsub (mem_closedBall_zero_iff.mpr (hw.trans (hhi.le.trans (min_le_left _ _))))).2

theorem bound_of_height {r H : ℝ} (hr : 0 < r) (h1 : r < 1) (hH : 0 ≤ H)
    (hsize : r^2*((17/16)^2+H^2) ≤ 1+H^2)
    (hfree : ∀ s : ℂ, 1 ≤ s.re → W s ≠ 0)
    (hzeros : ∀ s : ℂ, W s = 0 → 0 < s.re → H < |s.im|) : bound K r := by
  apply transfer K hW ha hr h1
  intro w hw hz
  have hx : (point w).re < 1 := lt_of_not_ge (fun h => hfree _ h hz)
  have hg := left_height h1 hw hx
  have hy := hzeros _ hz (point_positive h1 hw)
  have hysq : H^2 ≤ (point w).im^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ hH hy.le 2
  have hnon : 0 ≤ 1-r^2 := by nlinarith [mul_pos (sub_pos.mpr h1) (by linarith : 0<1+r)]
  nlinarith only [hg,hsize,mul_le_mul_of_nonneg_left hysq hnon]

#print axioms point_positive
#print axioms left_height
#print axioms initial_radius
#print axioms bound_of_height
end OMA.CayleyBounds
