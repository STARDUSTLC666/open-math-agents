import EulerBoundary
import ThetaContinuation
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-! Nonvanishing on the full closed right half-plane after removal of the pole,
and a strict gain in the reciprocal Taylor radius for every number field. -/

noncomputable section
namespace OMA.AllFieldRadius
open Complex Filter Set Metric NumberField OMA.EulerBoundary OMA.ThetaContinuation
open scoped ENNReal NNReal Topology

variable (K : Type*) [Field K] [NumberField K]

private theorem pt_one_ne {t : ℝ} (ht : t ≠ 0) : pt 1 t ≠ 1 := by
  intro he
  exact ht (congrArg Complex.im he)

/-- A zero at 1+it would contribute four horizontal factors x whereas the
pole is used only three times. Keep the remaining x instead of dividing by it. -/
theorem nonzero_on_line (t : ℝ) : reg K (pt 1 t) ≠ 0 := by
  rcases eq_or_ne t 0 with rfl | ht
  · exact reg_one K
  intro hz
  let u (y x : ℝ) := pt 1 y + (x : ℂ)
  let Z (y x : ℝ) := dedekindZeta K (u y x)
  let Q (x : ℝ) := dslope (reg K) (pt 1 t) (u t x)
  let A (x : ℝ) := (u t x - 1)^4 * (u (2*t) x - 1)
  let B (x : ℝ) := (x:ℂ) * reg K (u 0 x)^3 * Q x^4 * reg K (u (2*t) x)
  have u0 (y : ℝ) : u y 0 = pt 1 y := by simp [u]
  have uc (y : ℝ) : ContinuousAt (u y) 0 := (continuous_const.add Complex.continuous_ofReal).continuousAt
  have fc (y : ℝ) : ContinuousAt (fun x => reg K (u y x)) 0 := by
    change ContinuousAt (reg K ∘ u y) 0
    have hy : 0 < (u y 0).re := by rw [u0]; exact zero_lt_one
    exact (reg_diff K hy).continuousAt.comp (uc y)
  have qc : ContinuousAt Q 0 := by
    apply ContinuousAt.comp _ (uc t)
    rw [u0]
    exact continuousAt_dslope_same.mpr (reg_diff K (show 0 < (pt 1 t).re from zero_lt_one))
  have ac : ContinuousAt A 0 := (((uc t).sub continuousAt_const).pow 4).mul ((uc (2*t)).sub continuousAt_const)
  have bc : ContinuousAt B 0 := (((Complex.continuous_ofReal.continuousAt.mul ((fc 0).pow 3)).mul (qc.pow 4)).mul (fc (2*t)))
  have bound (x : ℝ) (hx : 0 < x) : ‖A x‖ ≤ ‖B x‖ := by
    have ux (y : ℝ) : u y x = pt (1+x) y := by apply Complex.ext <;> simp [u,pt]
    have hf (y : ℝ) : reg K (u y x) = (u y x - 1) * Z y x :=
      reg_agrees K (by rw [ux]; change 1 < 1+x; linarith)
    have hf0 : reg K (u 0 x) = (x:ℂ) * Z 0 x := by
      rw [hf]; congr 1; change (1:ℂ) + (x:ℂ) - 1 = _; ring
    have hq : (x:ℂ) * Q x = reg K (u t x) := by
      simpa only [u,Q,add_sub_cancel_left,smul_eq_mul] using sub_smul_dslope_of_zero hz (u t x)
    have e : B x = A x * (Z 0 x^3 * Z t x^4 * Z (2*t) x) := by
      calc B x = ((x:ℂ)*Q x)^4 * Z 0 x^3 * reg K (u (2*t) x) := by unfold B; rw [hf0]; ring
           _ = _ := by rw [hq, hf t, hf (2*t)]; unfold A; ring
    rw [e, norm_mul (A x) (Z 0 x^3 * Z t x^4 * Z (2*t) x)]
    apply le_mul_of_one_le_right (norm_nonneg _)
    simpa only [Z,ux] using zeta341 K (1+x) t (by linarith)
  have h := le_of_tendsto_of_tendsto (ac.norm.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0)))
    (bc.norm.tendsto.mono_left nhdsWithin_le_nhds) (eventually_nhdsWithin_of_forall bound)
  have ha : A 0 ≠ 0 := by
    unfold A; rw [u0, u0]
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr (pt_one_ne ht)))
      (sub_ne_zero.mpr (pt_one_ne (mul_ne_zero two_ne_zero ht)))
  exact (norm_pos_iff.mpr ha).not_ge (by simpa [B] using h)

theorem nonzero_on_closed_halfplane {z : ℂ} (hz : 1 ≤ z.re) : reg K z ≠ 0 := by
  rcases lt_or_eq_of_le hz with h | h
  · rw [reg_agrees K h]
    exact mul_ne_zero (sub_ne_zero.mpr (by rintro rfl; norm_num at h)) (ReciprocalRadius.zeta_ne_zero K h)
  · have he : z = pt 1 z.im := by apply Complex.ext <;> simp [h]
    exact he ▸ nonzero_on_line K z.im

def good : Set ℂ := {z | 0 < z.re ∧ reg K z ≠ 0}

theorem good_open : IsOpen (good K) := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  exact inter_mem ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz.1)
    ((reg_diff K hz.1).continuousAt.tendsto.eventually_ne hz.2)

def margin (t : ℝ) : ℝ := (1 + infDist (pt 2 t) (good K)ᶜ) / 2

theorem margin_gt_one (t : ℝ) : 1 < margin K t := by
  have h0 : (0:ℂ) ∈ (good K)ᶜ := by simp [good]
  obtain ⟨z,hz,he⟩ := (good_open K).isClosed_compl.exists_infDist_eq_dist ⟨0,h0⟩ (pt 2 t)
  have hd : 1 < dist (pt 2 t) z := by
    by_contra! hh
    rw [dist_eq_norm] at hh
    have hre := (re_le_norm (pt 2 t - z)).trans hh
    change 2 - z.re ≤ 1 at hre
    have hz' : 1 ≤ z.re := by linarith
    exact hz ⟨zero_lt_one.trans_le hz', nonzero_on_closed_halfplane K hz'⟩
  unfold margin; rw [he]; linarith

theorem inverse_on_larger_disk (t : ℝ) :
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ, ENNReal.ofReal (margin K t) ≤ p.radius ∧
      ReciprocalRadius.InverseGerm K t p := by
  let c := pt 2 t
  have hR := margin_gt_one K t
  let R : ℝ≥0 := ⟨margin K t, (zero_lt_one.trans hR).le⟩
  have hcoe : (R:ℝ) = margin K t := rfl
  have hpos : 0 < R := zero_lt_one.trans hR
  have hlt : margin K t < infDist c (good K)ᶜ := by unfold margin at *; dsimp [c]; linarith
  have sub : closedBall c (R:ℝ) ⊆ good K := by
    intro z hz
    have hn := notMem_of_dist_lt_infDist ((mem_closedBall'.mp hz).trans_lt hlt)
    exact Classical.not_not.mp hn
  have hd : DifferentiableOn ℂ (fun z => (reg K z)⁻¹) (closedBall c (R:ℝ)) :=
    fun z hz => ((reg_diff K (sub hz).1).inv (sub hz).2).differentiableWithinAt
  have hp := hd.hasFPowerSeriesOnBall hpos
  refine ⟨cauchyPowerSeries (fun z => (reg K z)⁻¹) c (R : ℝ), ?_, ?_⟩
  · rw [← hcoe, ENNReal.ofReal_coe_nnreal]; exact hp.r_le
  · have hre : ∀ᶠ z in 𝓝 c, 1 < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (show 1 < (2:ℝ) by norm_num)
    filter_upwards [ball_mem_nhds c (show 0 < (R:ℝ) from hpos), hre] with z hz hright
    have hw : z-c ∈ eball (0:ℂ) (R:ℝ≥0∞) := by simpa only [eball_coe,mem_ball_iff_norm,sub_zero] using hz
    have hv := hp.sum hw
    rw [add_sub_cancel] at hv
    change ((z-1)*dedekindZeta K z) * _ = 1
    rw [← reg_agrees K hright, ← hv, mul_inv_cancel₀ (sub (ball_subset_closedBall hz)).2]

theorem all_fields_radius_gt_one (t : ℝ) :
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ, 1 < p.radius ∧ ReciprocalRadius.InverseGerm K t p := by
  obtain ⟨p,hp,hg⟩ := inverse_on_larger_disk K t
  have hm := margin_gt_one K t
  have h := (ENNReal.ofReal_lt_ofReal_iff (zero_lt_one.trans hm)).mpr hm
  exact ⟨p, by simpa only [ENNReal.ofReal_one] using h.trans_le hp, hg⟩

theorem compact_height_gain {S : Set ℝ} (hS : IsCompact S) :
    ∃ R : ℝ, 1 < R ∧ ∀ t ∈ S, ∃ p : FormalMultilinearSeries ℂ ℂ ℂ,
      ENNReal.ofReal R ≤ p.radius ∧ ReciprocalRadius.InverseGerm K t p := by
  have hc : Continuous (pt 2) := by
    have he : pt 2 = fun t : ℝ => (2:ℂ) + (t:ℂ)*I := by funext t; apply Complex.ext <;> simp
    rw [he]; exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hm : Continuous (margin K) :=
    (continuous_const.add ((continuous_infDist_pt _).comp hc)).div_const _
  obtain ⟨R,hR,h⟩ := hS.exists_forall_le' hm.continuousOn (fun t _ => margin_gt_one K t)
  refine ⟨R,hR, fun t ht => ?_⟩
  obtain ⟨p,hp,hg⟩ := inverse_on_larger_disk K t
  exact ⟨p, (ENNReal.ofReal_le_ofReal (h t ht)).trans hp, hg⟩

#print axioms OMA.AllFieldRadius.nonzero_on_line
#print axioms OMA.AllFieldRadius.nonzero_on_closed_halfplane
#print axioms OMA.AllFieldRadius.inverse_on_larger_disk
#print axioms OMA.AllFieldRadius.all_fields_radius_gt_one
#print axioms OMA.AllFieldRadius.compact_height_gain
end OMA.AllFieldRadius
