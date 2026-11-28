import CayleyBounds
import LowHeight
import SharpStrip
import CubicDisk
import QuarticDisk

/-! Specialize the Cayley coefficient estimates to the canonical regularization. -/
noncomputable section
namespace OMA.CayleyFields
open NumberField Complex CayleyBounds ExactRadius ThetaContinuation AllFieldRadius
variable (K : Type*) [Field K] [NumberField K]

theorem boundary : (∀ s : ℂ, 1 < s.re → entireReg K s = (s-1)*dedekindZeta K s) ∧
    ∀ s : ℂ, 1 ≤ s.re → entireReg K s ≠ 0 := by
  constructor
  · intro s hs
    rw [entireReg_eq_reg K (ne_zero_of_re_pos (zero_lt_one.trans hs)),reg_agrees K hs]
  · intro s hs
    rw [entireReg_eq_reg K (ne_zero_of_re_pos (zero_lt_one.trans_le hs))]
    exact nonzero_on_closed_halfplane K hs

theorem all_fields : ∃ r : ℝ, 16/17 < r ∧ r < 1 ∧ bound K r :=
  initial_radius K (entireReg_diff K) (boundary K).1 (boundary K).2

private theorem from_height {r H : ℝ} (hr : 0 < r) (h1 : r < 1) (hH : 0 ≤ H)
    (hsize : r^2*((17/16)^2+H^2) ≤ 1+H^2)
    (hzero : ∀ z ∈ zeros K, 0 < z.re → H < |z.im|) : bound K r :=
  bound_of_height K (entireReg_diff K) (boundary K).1 hr h1 hH hsize (boundary K).2 hzero

theorem degree_one (hk : Module.finrank ℚ K = 1) : bound K (499/500) := by
  apply from_height K (H := 6) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  intro z hz hp
  have hlt := zeros_left K hz
  have hne : z ≠ 1 := by rintro rfl; norm_num at hlt
  have hQ := R_ERH_extended_riemann_hypothesis_R1_H1_R1.isDedekindZeta_rat_of_finrank_one hk
    (canonical_isDedekindZeta K)
  by_contra! h
  apply LowHeight.zero_free_six hp hlt h
  rw [← R_ERH_extended_riemann_hypothesis_R1_H1_R1.agrees_off_one hQ hne,canonicalZeta,
    show entireReg K z = 0 from hz,zero_div]

theorem gaussian : bound (CyclotomicField 4 ℚ) (993/1000) := by
  apply from_height _ (H := 23/8) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact fun _ hz hp => SharpStrip.gaussian_zero_height hz hp

theorem small_cubic (hk : Module.finrank ℚ K = 3) (hD : (discr K).natAbs ≤ 23) : bound K (123/125) := by
  apply from_height K (H := 89/50) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  intro z hz hp
  have h := CubicDisk.small_cubic_height K hk hD hz hp
  by_contra! hle
  nlinarith only [h,sq_abs z.im,pow_le_pow_left₀ (abs_nonneg z.im) hle 2]

theorem fifth : bound (CyclotomicField 5 ℚ) (39/40) := by
  apply from_height _ (H := 21/16) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  intro z hz hp
  have h := QuarticDisk.fifth_zero_height hz hp
  by_contra! hle
  nlinarith only [h,sq_abs z.im,pow_le_pow_left₀ (abs_nonneg z.im) hle 2]

#print axioms boundary
#print axioms all_fields
#print axioms degree_one
#print axioms gaussian
#print axioms small_cubic
#print axioms fifth
end OMA.CayleyFields
