import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Real.Pi.Bounds

/-! A positive Mellin interpolation bound for the pole-subtracted completed
Riemann zeta. Both endpoint moments are evaluated exactly, not by quadrature. -/
noncomputable section
namespace OMA.ThetaMoment
open Complex MeasureTheory Set HurwitzZeta
open scoped Real Topology

private abbrev P := hurwitzEvenFEPair 0

private theorem theta_ge_one {x : ℝ} (hx : 0 < x) : 1 ≤ evenKernel 0 x := by
  have hs := hasSum_int_evenKernel₀ (0:ℝ) hx
  have h := hs.nonneg (fun i => by split_ifs <;> positivity)
  simpa using h

private theorem kernel_posreal {x : ℝ} (hx : 0 < x) :
    ∃ a : ℝ, 0 ≤ a ∧ P.f_modif x = (a : ℂ) := by
  rcases lt_trichotomy x 1 with h | rfl | h
  · refine ⟨evenKernel 0 x - x ^ (-(1/2:ℝ)), ?_, ?_⟩
    · apply sub_nonneg.mpr
      rw [evenKernel_functional_equation, ← evenKernel_eq_cosKernel_of_zero, Real.rpow_neg hx.le]
      simpa only [one_div, mul_one] using
        (le_mul_of_one_le_right (inv_nonneg.mpr (Real.rpow_nonneg hx.le _)) (theta_ge_one (one_div_pos.mpr hx)))
    · simp [WeakFEPair.f_modif, h.not_gt, h, hx, hurwitzEvenFEPair]
  · exact ⟨0,le_rfl,by simp [WeakFEPair.f_modif]⟩
  · exact ⟨evenKernel 0 x - 1,sub_nonneg.mpr (theta_ge_one hx),by
      simp [WeakFEPair.f_modif, h, h.not_gt, hurwitzEvenFEPair]⟩

private def W (s : ℂ) (x : ℝ) := (x:ℂ) ^ (s/2-1) * P.f_modif x

private theorem wi (s : ℂ) : IntegrableOn (W s) (Ioi 0) :=
  (P.isStrongFEPair_toStrongFEPair.hasMellin (s/2)).1

private theorem value (s : ℂ) :
    completedRiemannZeta₀ s = (∫ x in Ioi 0, W s x) / 2 := rfl

private theorem wnorm {x : ℝ} (hx : 0 < x) (s : ℂ) :
    ‖W s x‖ = x ^ (s.re/2-1) * ‖P.f_modif x‖ := by
  rw [W, norm_mul, norm_cpow_eq_rpow_re_of_pos hx]; simp

private theorem realnorm {x : ℝ} (hx : 0 < x) (s : ℝ) :
    (W (s:ℂ) x).re = ‖W (s:ℂ) x‖ := by
  obtain ⟨a,ha,he⟩ := kernel_posreal hx
  have e : W (s:ℂ) x = ((x^(s/2-1) * a : ℝ) : ℂ) := by
    simp only [W, he, ofReal_mul, ofReal_cpow hx.le, ofReal_sub, ofReal_div, ofReal_one, ofReal_ofNat]
  rw [e, ofReal_re, Complex.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hx.le _) ha)]

private theorem real_moment (s : ℝ) :
    ∫ x in Ioi 0, ‖W (s:ℂ) x‖ = 2 * (completedRiemannZeta₀ (s:ℂ)).re := by
  have e : (∫ x in Ioi 0, ‖W (s:ℂ) x‖) = ∫ x in Ioi 0, (W (s:ℂ) x).re :=
    setIntegral_congr_fun measurableSet_Ioi (fun _ hx => (realnorm hx s).symm)
  rw [e, value, div_ofNat_re]
  have he := integral_re (wi (s:ℂ))
  change (∫ x in Ioi 0, (W (s:ℂ) x).re) = (∫ x in Ioi 0, W (s:ℂ) x).re at he
  linarith

theorem completed_two : completedRiemannZeta₀ 2 = ((Real.pi/6-1/2 : ℝ) : ℂ) := by
  have h := riemannZeta_two
  rw [riemannZeta_def_of_ne_zero (by norm_num : (2:ℂ) ≠ 0), completedRiemannZeta_eq] at h
  have hG : Gammaℝ 2 = ((Real.pi:ℂ))⁻¹ := by
    rw [Gammaℝ_def, show (-(2:ℂ)/2) = -1 by norm_num, Complex.cpow_neg_one, div_self (by norm_num), Gamma_one, mul_one]
  have hpi : (Real.pi:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [hG] at h
  push_cast
  field_simp [hpi] at h ⊢
  linear_combination -h

/-- Convexity in the real exponent interpolates between the equal positive
moments at s=-1 and s=2. No bound depending on the imaginary part is used. -/
theorem moment_bound {s : ℂ} (hlo : -1 ≤ s.re) (hhi : s.re ≤ 2) :
    ‖completedRiemannZeta₀ s‖ ≤ Real.pi/6-1/2 := by
  let a := (2-s.re)/3
  let b := (s.re+1)/3
  have ha : 0 ≤ a := by unfold a; linarith
  have hb : 0 ≤ b := by unfold b; linarith
  have hab : a+b=1 := by unfold a b; ring
  have hpoint {x : ℝ} (hx : 0 < x) :
      ‖W s x‖ ≤ a*‖W (-1) x‖ + b*‖W 2 x‖ := by
    rw [wnorm hx, wnorm hx, wnorm hx]
    simp only [neg_re, one_re, re_ofNat]
    rw [← mul_assoc, ← mul_assoc, ← add_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have hh := (convexOn_rpow_left hx).2 (x := (-1:ℝ)/2-1) (y := (2:ℝ)/2-1)
      (mem_univ _) (mem_univ _) ha hb hab
    simp only [smul_eq_mul] at hh
    rwa [show a * (-1/2-1) + b * (2/2-1) = s.re/2-1 by unfold a b; ring] at hh
  have hi := integral_mono_ae (wi s).norm (((wi (-1)).norm.const_mul a).add ((wi 2).norm.const_mul b))
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall (fun x hx => hpoint hx)))
  change (∫ x in Ioi 0, ‖W s x‖) ≤ ∫ x in Ioi 0, a*‖W (-1) x‖ + b*‖W 2 x‖ at hi
  rw [integral_add ((wi (-1)).norm.const_mul _) ((wi 2).norm.const_mul _),
    integral_const_mul, integral_const_mul] at hi
  have hm := real_moment (-1)
  have hp := real_moment 2
  simp only [ofReal_neg, ofReal_one, ofReal_ofNat] at hm hp
  have he : completedRiemannZeta₀ (-1) = completedRiemannZeta₀ 2 := by
    exact (show (1:ℂ)-2 = -1 by norm_num) ▸ completedRiemannZeta₀_one_sub (2:ℂ)
  rw [hm, hp, he, ← add_mul, hab, one_mul, completed_two, ofReal_re] at hi
  rw [value, norm_div, Complex.norm_two]
  linarith [norm_integral_le_integral_norm (μ := volume.restrict (Ioi 0)) (W s)]

#print axioms OMA.ThetaMoment.completed_two
#print axioms OMA.ThetaMoment.moment_bound
end OMA.ThetaMoment
