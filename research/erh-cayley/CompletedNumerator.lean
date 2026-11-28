import VerticalDecay
import Mathlib.Analysis.Complex.PhragmenLindelof

/-! The entire completed numerator on the two lines Re(s)=2 and Re(s)=-1.
The gamma recurrence gives polynomial decay of every order on either line. -/
noncomputable section
namespace OMA.CompletedNumerator
open Complex NumberField NumberField.InfinitePlace Set MeasureTheory
open ThetaContinuation

variable (K : Type*) [Field K] [NumberField K]

def xi (s : ℂ) := s*(s-1)*(pair K).Λ₀ s+cst K

theorem xi_diff : Differentiable ℂ (xi K) :=
  ((differentiable_id.mul (differentiable_id.sub_const (1:ℂ))).mul
    (pair K).differentiable_Λ₀).add_const _

theorem xi_reflect (s : ℂ) : xi K (1-s) = xi K s := by
  have hs : (pair K).symm = pair K := by unfold WeakFEPair.symm pair; congr 1; simp
  have hf := (pair K).functional_equation₀ s
  rw [hs] at hf
  change (pair K).Λ₀ (1-s) = (1:ℂ) • (pair K).Λ₀ s at hf
  rw [one_smul] at hf
  rw [xi, xi, hf]; ring

theorem xi_agrees {s : ℂ} (hs : 1 < s.re) :
    xi K s = s*(s-1)*(arch K s * dedekindZeta K s) := by
  have h0 : s ≠ 0 := ne_zero_of_re_pos (zero_lt_one.trans hs)
  have h1 : s ≠ 1 := by rintro rfl; norm_num at hs
  rw [← completed_agrees K hs, WeakFEPair.Λ]
  change s*(s-1)*(pair K).Λ₀ s+cst K =
    s*(s-1)*((pair K).Λ₀ s-(1/s)*cst K-(1/(1-s))*cst K)
  field_simp [h0, sub_ne_zero.mpr h1.symm]; ring

private theorem norm_le_shift {s : ℂ} (hs : 0 ≤ s.re) : ‖s‖ ≤ ‖s+1‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [Complex.sq_norm, normSq_apply, add_re, one_re, add_im, one_im, add_zero]
  linarith only [hs, show (s.re+1)*(s.re+1) = s.re*s.re+2*s.re+1 by ring]

/-- Each recurrence step gains one full complex norm, uniformly in the
imaginary part, because shifting a positive real part increases the norm. -/
theorem gamma_norm_shift {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ‖s‖^n * ‖Gamma s‖ ≤ Real.Gamma (s.re+n) := by
  induction n generalizing s with
  | zero => simpa using DedekindMellin.norm_Gamma_le_real hs
  | succ n ih =>
    have hs' : 0 < (s+1).re := by rw [add_re, one_re]; linarith
    have hg : ‖s‖*‖Gamma s‖ = ‖Gamma (s+1)‖ := by
      rw [Gamma_add_one s (ne_zero_of_re_pos hs), norm_mul]
    calc ‖s‖^(n+1)*‖Gamma s‖ = ‖s‖^n*‖Gamma (s+1)‖ := by rw [pow_succ, mul_assoc, hg]
         _ ≤ ‖s+1‖^n*‖Gamma (s+1)‖ :=
              mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (norm_le_shift hs.le) n) (norm_nonneg _)
         _ ≤ _ := (ih hs').trans_eq (by rw [add_re, one_re, Nat.cast_succ]; congr 1; ring)

private theorem gammaR_norm {s : ℂ} (hs : s.re = 2) : ‖Gammaℝ s‖ ≤ ‖Gamma (s/2)‖ := by
  rw [Gammaℝ_def, norm_mul]
  apply mul_le_of_le_one_left (norm_nonneg _)
  rw [norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three])
  rw [div_ofNat_re, neg_re, hs]; norm_num

theorem gammaR_boundary {s : ℂ} (hs : s.re = 2) (n : ℕ) :
    ‖s‖^n * ‖Gammaℝ s‖ ≤ 2^n * Real.Gamma (1+n) := by
  have hhalf : (s/2).re = 1 := by rw [div_ofNat_re, hs]; norm_num
  have h := gamma_norm_shift (s := s/2) (by rw [hhalf]; norm_num) n
  rw [hhalf, norm_div, Complex.norm_ofNat] at h
  calc _ ≤ ‖s‖^n * ‖Gamma (s/2)‖ := mul_le_mul_of_nonneg_left (gammaR_norm hs) (by positivity)
       _ = (2:ℝ)^n * ((‖s‖/2)^n * ‖Gamma (s/2)‖) := by rw [div_pow]; field_simp
       _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)

theorem arch_boundary (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ s : ℂ, s.re = 2 → ‖s‖^n*‖arch K s‖ ≤ A := by
  obtain ⟨B,hB,hBd⟩ := (DedekindMellin.gammaR_strip (a := (3:ℝ)) (b := 3) (by norm_num)).bound
  let E := Real.exp (2*(Real.log (discr K).natAbs/2))
  let G := (2:ℝ)^n*Real.Gamma (1+n)
  have hG : 0 ≤ G := mul_nonneg (by positivity) (Real.Gamma_pos_of_pos (by positivity)).le
  refine ⟨(E*B^nrComplexPlaces K)*G, mul_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg hB _)) hG, ?_⟩
  intro s hs
  have he : ‖exp (s*(Real.log (discr K).natAbs/2 : ℝ))‖ = E := by
    rw [norm_exp]; dsimp [E]; congr 1; simp [hs, mul_re]
  have hR : ‖Gammaℝ s‖ ≤ 1 := by
    simpa using gammaR_boundary hs 0
  have hS : ‖Gammaℝ (s+1)‖ ≤ B :=
    hBd (s+1) (by norm_num [hs])
  have hplaces : 0 < nrRealPlaces K + nrComplexPlaces K := by
    rw [← card_eq_nrRealPlaces_add_nrComplexPlaces]; exact Fintype.card_pos
  have hP : ‖Gammaℝ s‖^(nrRealPlaces K+nrComplexPlaces K) ≤ ‖Gammaℝ s‖ :=
    pow_le_of_le_one (norm_nonneg _) hR hplaces.ne'
  have hS' := pow_le_pow_left₀ (norm_nonneg _) hS (nrComplexPlaces K)
  calc _ = ‖s‖^n * (E*(‖Gammaℝ s‖^(nrRealPlaces K+nrComplexPlaces K)*‖Gammaℝ (s+1)‖^nrComplexPlaces K)) := by
             rw [arch, ← Gammaℝ_mul_Gammaℝ_add_one, pow_add]
             simp only [norm_mul, norm_pow, he, mul_pow]; ring
       _ ≤ ‖s‖^n * (E*(‖Gammaℝ s‖*B^nrComplexPlaces K)) := by
             gcongr
       _ = (E*B^nrComplexPlaces K)*(‖s‖^n*‖Gammaℝ s‖) := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_left (gammaR_boundary hs n) (mul_nonneg (Real.exp_pos _).le (pow_nonneg hB _))

theorem right_boundary (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, s.re = 2 → ‖s‖^n*‖xi K s‖ ≤ C := by
  obtain ⟨A,hA,hArch⟩ := arch_boundary K (n+2)
  obtain ⟨Z,hZ⟩ := DedekindMellin.bounded K (a := 2) (by norm_num)
  refine ⟨A*max Z 0,mul_nonneg hA (le_max_right _ _),?_⟩
  intro s hs
  have h1 : ‖s-1‖ ≤ ‖s‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [Complex.sq_norm, normSq_apply, sub_re, one_re, sub_im, one_im, sub_zero, hs]; norm_num
  have hz := (hZ s hs.ge).trans (le_max_left Z 0)
  rw [xi_agrees K (by linarith), norm_mul, norm_mul, norm_mul]
  calc _ ≤ ‖s‖^n*(‖s‖*‖s‖*(‖arch K s‖*‖dedekindZeta K s‖)) := by gcongr
       _ = (‖s‖^(n+2)*‖arch K s‖)*‖dedekindZeta K s‖ := by rw [pow_add]; ring
       _ ≤ _ := mul_le_mul (hArch s hs) hz (norm_nonneg _) hA

#print axioms xi_diff
#print axioms xi_reflect
#print axioms xi_agrees
#print axioms gamma_norm_shift
#print axioms gammaR_boundary
#print axioms arch_boundary
#print axioms right_boundary
end OMA.CompletedNumerator
