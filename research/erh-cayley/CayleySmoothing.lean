import CayleyDifference
import Mathlib.Analysis.PSeries

/-! A polynomially bounded entire function on Re(s) >= 1/3 has absolutely
summable Cayley coefficients after multiplying by a sufficient power of 1-w. -/
noncomputable section
namespace OMA.CayleySmoothing
open Complex Filter Metric Set CayleyBounds CayleyRecurrence
open scoped Topology

def damp (W : ℂ → ℂ) (m : ℕ) (w : ℂ) := (1-w)^m * W (point w)

private theorem point_eq {w : ℂ} (hw : w ≠ 1) : point w*(1-w) = 2+w/16 :=
  div_mul_cancel₀ _ (sub_ne_zero.mpr hw.symm)

theorem point_right {w : ℂ} (hw : ‖w‖ < 1) : 31/32 < (point w).re := by
  have hw1 : w ≠ 1 := by rintro rfl; simp at hw
  have he : point w-2 = w*(point w+1/16) := by linear_combination point_eq hw1
  have hd : point w+1/16 ≠ 0 := by
    intro h
    rw [h,mul_zero] at he
    rw [sub_eq_zero.mp he] at h
    norm_num at h
  have hl : ‖point w-2‖ < ‖point w+1/16‖ := by
    rw [he,norm_mul]
    exact mul_lt_of_lt_one_left (norm_pos_iff.mpr hd) hw
  have hs := (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hl
  rw [Complex.sq_norm,Complex.sq_norm,Complex.normSq_apply,Complex.normSq_apply] at hs
  norm_num [sub_re,sub_im,add_re,add_im] at hs
  nlinarith only [hs]

/-- On this shrinking disk the change in the s-coordinate is at most one half.
The radius is quadratic in the distance to the boundary point w = 1. -/
theorem local_geometry {w u : ℂ} (hw : ‖w‖ < 1)
    (hu : ‖u-w‖ ≤ ‖1-w‖^2/32) :
    u ≠ 1 ∧ (1/3:ℝ) ≤ (point u).re ∧
      ‖1-u‖ ≤ 2*‖1-w‖ ∧ (4+‖point u‖)*‖1-u‖ ≤ 20 := by
  let t := ‖1-w‖
  let q := ‖1-u‖
  have hw1 : w ≠ 1 := by rintro rfl; simp at hw
  have ht : 0 < t := norm_pos_iff.mpr (sub_ne_zero.mpr hw1.symm)
  have ht2 : t ≤ 2 := (norm_sub_le _ _).trans (by simp; linarith)
  change ‖u-w‖ ≤ t^2/32 at hu
  have hsmall : t^2/32 ≤ t/2 := by nlinarith [mul_nonneg ht.le (sub_nonneg.mpr ht2)]
  have hlow : t/2 ≤ q := by
    have h := norm_add_le (1-u) (u-w)
    rw [sub_add_sub_cancel] at h
    change t ≤ q+_ at h
    linarith
  have hhigh : q ≤ 2*t := by
    have h := norm_add_le (1-w) (w-u)
    rw [sub_add_sub_cancel,norm_sub_rev w u] at h
    change q ≤ t+_ at h
    linarith
  have hu1 : u ≠ 1 := by
    intro e
    have hq : q = 0 := by simp [q,e]
    linarith
  have hid : (point u-point w)*(1-u)*(1-w) = (33/16)*(u-w) := by
    linear_combination (1-w)*point_eq hu1 - (1-u)*point_eq hw1
  have hn := congrArg norm hid
  simp only [norm_mul] at hn
  norm_num at hn
  change ‖point u-point w‖ * q * t = (33/16)*‖u-w‖ at hn
  have hdist : ‖point u-point w‖ ≤ 1/2 := by
    apply (mul_le_mul_iff_of_pos_right (show 0 < t/2*t by positivity)).mp
    calc ‖point u-point w‖*(t/2*t) ≤ ‖point u-point w‖*q*t := by
           rw [← mul_assoc]
           exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlow (norm_nonneg _)) ht.le
         _ = _ := hn
         _ ≤ (33/16)*(t^2/32) := mul_le_mul_of_nonneg_left hu (by norm_num)
         _ ≤ _ := by nlinarith only [sq_nonneg t]
  have hre := (abs_re_le_norm (point u-point w)).trans hdist
  rw [sub_re,abs_le] at hre
  have hp := point_right hw
  refine ⟨hu1,by linarith [hre.1],hhigh,?_⟩
  have hunorm : ‖u‖ ≤ 2 := by
    have h := norm_add_le (u-w) w
    rw [sub_add_cancel] at h
    linarith
  have hpoint : ‖point u‖*q ≤ 3 := by
    change ‖point u‖*‖1-u‖ ≤ 3
    rw [← norm_mul,point_eq hu1]
    apply (norm_add_le _ _).trans
    rw [norm_div]
    norm_num
    linarith
  change (4+‖point u‖)*q ≤ 20
  nlinarith only [hpoint,hhigh,ht2]

theorem damp_analytic (W : ℂ → ℂ) (hW : Differentiable ℂ W) (m : ℕ) :
    AnalyticOnNhd ℂ (damp W m) (ball 0 1) := by
  intro w hw
  exact ((analyticAt_const.sub analyticAt_id).pow m).mul
    ((hW.differentiableOn.analyticOnNhd isOpen_univ _ (mem_univ _)).comp
      (CayleyDifference.point_analytic (mem_ball_zero_iff.mp hw)))

theorem second_bound (W : ℂ → ℂ) (hW : Differentiable ℂ W) (p : ℕ)
    {C : ℝ} (hC : 0 ≤ C) (hg : ∀ s : ℂ, (1/3:ℝ) ≤ s.re → ‖W s‖ ≤ C*(4+‖s‖)^p) :
    ∀ w : ℂ, ‖w‖ < 1 → ‖iteratedDeriv 2 (damp W (p+4)) w‖ ≤ 32768*C*20^p := by
  intro w hw
  let t := ‖1-w‖
  let R := t^2/32
  have hw1 : w ≠ 1 := by rintro rfl; simp at hw
  have ht : 0 < t := norm_pos_iff.mpr (sub_ne_zero.mpr hw1.symm)
  have hR : 0 < R := by dsimp [R]; positivity
  have hd : DifferentiableOn ℂ (damp W (p+4)) (closedBall w R) := by
    intro u hu
    obtain ⟨hne,_,_,_⟩ := local_geometry hw (mem_closedBall_iff_norm.mp hu)
    have hT : AnalyticAt ℂ point u :=
      (analyticAt_const.add analyticAt_id.div_const).div
        (analyticAt_const.sub analyticAt_id) (sub_ne_zero.mpr hne.symm)
    have hq : AnalyticAt ℂ (fun z : ℂ => (1-z)^(p+4)) u := (analyticAt_const.sub analyticAt_id).pow _
    exact (hq.differentiableAt.mul ((hW _).comp u hT.differentiableAt)).differentiableWithinAt
  have hb (u : ℂ) (hu : u ∈ sphere w R) :
      ‖damp W (p+4) u‖ ≤ C*20^p*(2*t)^4 := by
    obtain ⟨_,hs,hq,hprod⟩ := local_geometry hw (mem_closedBall_iff_norm.mp (sphere_subset_closedBall hu))
    have hlocal : ‖1-u‖^p * ‖W (point u)‖ ≤ C*20^p := calc
      _ ≤ ‖1-u‖^p*(C*(4+‖point u‖)^p) := mul_le_mul_of_nonneg_left (hg _ hs) (by positivity)
      _ = C*((4+‖point u‖)*‖1-u‖)^p := by rw [mul_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hprod _) hC
    rw [damp,norm_mul,norm_pow,pow_add]
    calc _ = (‖1-u‖^p*‖W (point u)‖)*‖1-u‖^4 := by ring
         _ ≤ _ := mul_le_mul hlocal (pow_le_pow_left₀ (norm_nonneg _) hq _) (by positivity) (by positivity)
  apply (Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2 hR
    (hd.diffContOnCl_ball Subset.rfl) hb).trans_eq
  dsimp only [R]
  norm_num [Nat.factorial]
  field_simp [ht.ne']
  <;> ring

theorem coefficient_decay (H : ℂ → ℂ) (ha : AnalyticOnNhd ℂ H (ball 0 1)) {M : ℝ}
    (hb : ∀ z : ℂ, ‖z‖ < 1 → ‖iteratedDeriv 2 H z‖ ≤ M) (n : ℕ) :
    ‖coeff H (n+2)‖ ≤ M/(((n:ℝ)+1)*(n+2)) := by
  let g := deriv (deriv H)
  have hg : DifferentiableOn ℂ g (ball 0 1) := fun z hz => (ha z hz).deriv.deriv.differentiableAt.differentiableWithinAt
  have hbounded {z : ℂ} (hz : ‖z‖ < 1) : ‖g z‖ ≤ M := by
    simpa only [g,show (2:ℕ)=0+1+1 from rfl,iteratedDeriv_succ',iteratedDeriv_zero] using hb z hz
  have hder : ‖iteratedDeriv n g 0‖ ≤ (n.factorial:ℝ)*M := by
    have ht : Tendsto (fun r : ℝ => ‖iteratedDeriv n g 0‖*r^n) (𝓝[<] 1) (𝓝 ‖iteratedDeriv n g 0‖) := by
      simpa using (((continuous_id.pow n).const_mul ‖iteratedDeriv n g 0‖).continuousAt (x := (1:ℝ))).tendsto.mono_left nhdsWithin_le_nhds
    apply le_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin,((lt_mem_nhds (by norm_num : (0:ℝ)<1)) : ∀ᶠ r : ℝ in 𝓝 1, 0 < r).filter_mono nhdsWithin_le_nhds] with r (hr : r < 1) hr0
    apply (le_div_iff₀ (pow_pos hr0 n)).mp
    apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr0
      (hg.diffContOnCl_ball (closedBall_subset_ball hr))
    intro z hz
    exact hbounded ((mem_sphere_zero_iff_norm.mp hz).trans_lt hr)
  have he : iteratedDeriv (n+2) H 0 = iteratedDeriv n g 0 := by
    rw [show n+2=n+1+1 from rfl,iteratedDeriv_succ',iteratedDeriv_succ']
  have hf : ((n+2).factorial:ℝ) = ((n:ℝ)+2)*(n+1)*n.factorial := by
    rw [Nat.factorial_succ,Nat.factorial_succ]
    push_cast
    ring
  rw [coeff,he,norm_div,Complex.norm_natCast,hf]
  apply (div_le_div_of_nonneg_right hder (by positivity)).trans_eq
  have hnf : (n.factorial:ℝ) ≠ 0 := by positivity
  field_simp [hnf]
  <;> ring

theorem absolute_coefficients (W : ℂ → ℂ) (hW : Differentiable ℂ W) (p : ℕ)
    {C : ℝ} (hC : 0 ≤ C) (hg : ∀ s : ℂ, (1/3:ℝ) ≤ s.re → ‖W s‖ ≤ C*(4+‖s‖)^p) :
    Summable fun n => ‖coeff (damp W (p+4)) n‖ := by
  let M : ℝ := 32768*C*20^p
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hmajor : Summable (fun n : ℕ => M*(((n+1:ℕ):ℝ)^2)⁻¹) :=
    ((summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2))).mul_left M
  apply (summable_nat_add_iff 2).mp
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hmajor
  intro n
  apply (coefficient_decay _ (damp_analytic W hW (p+4)) (second_bound W hW p hC hg) n).trans
  push_cast
  rw [← div_eq_mul_inv]
  apply div_le_div_of_nonneg_left hM (by positivity)
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

#print axioms point_right
#print axioms local_geometry
#print axioms second_bound
#print axioms coefficient_decay
#print axioms absolute_coefficients
end OMA.CayleySmoothing
