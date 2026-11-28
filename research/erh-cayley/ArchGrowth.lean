import MellinAsymptotic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-! A growth bound for the inverse archimedean factor and its exact
two-unit shift. The crude bound is used only for the growth hypothesis in
Phragmén-Lindelöf; the boundary estimate will be polynomial. -/
noncomputable section
namespace OMA.ArchGrowth
open Complex NumberField NumberField.InfinitePlace Set
open ThetaContinuation
open scoped ComplexConjugate

private theorem sin_bound (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  rw [Complex.sin,norm_div,norm_mul,norm_I,mul_one,Complex.norm_ofNat]
  apply (div_le_iff₀ zero_lt_two).mpr
  apply (norm_sub_le _ _).trans
  simp only [norm_exp, mul_I_re, neg_im, neg_neg]
  linarith [Real.exp_le_exp.mpr (le_abs_self z.im), Real.exp_le_exp.mpr (neg_le_abs z.im)]

private theorem inv_gamma_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc (-(1/2:ℝ)) (3/2) → 1/2 ≤ |z.im| →
      ‖(Gamma z)⁻¹‖ ≤ C * Real.exp (Real.pi*|z.im|) := by
  obtain ⟨B,hB,hG⟩ := (DedekindMellin.gamma_strip (a := 1/2) (b := 3) (by norm_num)).bound
  refine ⟨2*B/Real.pi, by positivity, ?_⟩
  intro z hz ht
  have hIm : z.im ≠ 0 := by intro e; rw [e] at ht; norm_num at ht
  have hπ : (Real.pi:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have h1 : 1-z ≠ 0 := sub_ne_zero.mpr (by rintro rfl; simp at hIm)
  have hΓ : Gamma z ≠ 0 := by
    intro h; obtain ⟨n,rfl⟩ := (Gamma_eq_zero_iff z).mp h; simp at hIm
  have hsin : Complex.sin ((Real.pi:ℂ)*z) ≠ 0 := by
    intro h; obtain ⟨k,hk⟩ := sin_eq_zero_iff.mp h
    have hi := congrArg Complex.im hk
    simp [mul_im, Real.pi_ne_zero, hIm] at hi
  have hproduct := (eq_div_iff hsin).mp (Gamma_mul_Gamma_one_sub z)
  have he : (Gamma z)⁻¹ = Gamma (1-z) * Complex.sin ((Real.pi:ℂ)*z) / (Real.pi:ℂ) := by
    apply (eq_div_iff hπ).mpr
    apply mul_left_cancel₀ hΓ
    rw [← mul_assoc, mul_inv_cancel₀ hΓ, one_mul, ← mul_assoc]
    exact hproduct.symm
  have hnorm := congrArg norm (Gamma_add_one (1-z) h1)
  rw [show 1-z+1=2-z by ring, norm_mul] at hnorm
  have hb := hG (2-z) (by rw [sub_re, re_ofNat]; exact ⟨by linarith [hz.2],by linarith [hz.1]⟩)
  have hOne : 1/2 ≤ ‖1-z‖ := ht.trans (by simpa using abs_im_le_norm (1-z))
  have hGa : ‖Gamma (1-z)‖ ≤ 2*B := by
    linarith [mul_le_mul_of_nonneg_left hOne (norm_nonneg (Gamma (1-z)))]
  have hS := sin_bound ((Real.pi:ℂ)*z)
  simp only [mul_im,ofReal_re,ofReal_im,zero_mul,add_zero,abs_mul,abs_of_pos Real.pi_pos] at hS
  rw [he,norm_div,norm_mul,Complex.norm_of_nonneg Real.pi_pos.le]
  calc _ ≤ (2*B*Real.exp (Real.pi*|z.im|))/Real.pi :=
             div_le_div_of_nonneg_right (mul_le_mul hGa hS (norm_nonneg _) (by positivity)) Real.pi_pos.le
       _ = _ := by ring

private theorem inv_gammaR :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc (-1:ℝ) 3 → 1 ≤ |z.im| →
      ‖(Gammaℝ z)⁻¹‖ ≤ C*Real.exp (Real.pi*|z.im|) := by
  obtain ⟨B,hB,h⟩ := inv_gamma_bound
  refine ⟨Real.pi^2*B,by positivity,?_⟩
  intro z hz ht
  have hhalf : (z/2).re ∈ Icc (-(1/2:ℝ)) (3/2) := by
    rw [div_ofNat_re]; exact ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hI : |(z/2).im| = |z.im|/2 := by rw [div_ofNat_im, abs_div]; norm_num
  have hG := h (z/2) hhalf (by rw [hI]; linarith)
  rw [hI] at hG
  have hπ : ‖((Real.pi:ℂ)^(-z/2))⁻¹‖ ≤ Real.pi^2 := by
    rw [← cpow_neg, show -(-z/2) = z/2 by ring,norm_cpow_eq_rpow_re_of_pos Real.pi_pos,div_ofNat_re]
    rw [← Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) (by linarith [hz.2])
  rw [Gammaℝ_def, mul_inv, norm_mul]
  calc _ ≤ Real.pi^2*(B*Real.exp (Real.pi*(|z.im|/2))) :=
            mul_le_mul hπ hG (norm_nonneg _) (by positivity)
       _ ≤ Real.pi^2*(B*Real.exp (Real.pi*|z.im|)) := by
            gcongr; linarith [abs_nonneg z.im]
       _ = _ := by ring

variable (K : Type*) [Field K] [NumberField K]

theorem reciprocal_arch_growth :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ z : ℂ, z.re ∈ Icc (-(1/2:ℝ)) (3/2) → 1 ≤ |z.im| →
      ‖(arch K z)⁻¹‖ ≤ C*Real.exp (D*|z.im|) := by
  obtain ⟨B,hB,hGamma⟩ := inv_gammaR
  let l := Real.log (discr K).natAbs / 2
  let E := Real.exp (2*|l|)
  let d := nrRealPlaces K + 2*nrComplexPlaces K
  refine ⟨E*B^d,(d:ℝ)*Real.pi,mul_nonneg (Real.exp_pos _).le (pow_nonneg hB _),
    mul_nonneg (Nat.cast_nonneg _) Real.pi_pos.le,?_⟩
  intro z hz ht
  let W := B*Real.exp (Real.pi*|z.im|)
  have hW : 0 ≤ W := mul_nonneg hB (Real.exp_pos _).le
  have hR : ‖(Gammaℝ z)⁻¹‖ ≤ W := hGamma _ ⟨by linarith [hz.1],by linarith [hz.2]⟩ ht
  have hG : ‖(Gammaℝ (z+1))⁻¹‖ ≤ W := by
    have h := hGamma (z+1) (by rw [add_re,one_re]; exact ⟨by linarith [hz.1],by linarith [hz.2]⟩)
      (by simpa using ht)
    simpa [W] using h
  have hE : ‖(exp (z*(l:ℂ)))⁻¹‖ ≤ E := by
    rw [← exp_neg, norm_exp, neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    apply Real.exp_le_exp.mpr
    have hza : |z.re| ≤ 2 := abs_le.mpr ⟨by linarith [hz.1],by linarith [hz.2]⟩
    calc -(z.re*l) ≤ |z.re*l| := neg_le_abs _
         _ ≤ _ := by rw [abs_mul]; exact mul_le_mul_of_nonneg_right hza (abs_nonneg _)
  have hcomplex : ‖(Gammaℂ z)⁻¹‖ ≤ W*W := by
    rw [← Gammaℝ_mul_Gammaℝ_add_one, mul_inv, norm_mul]
    exact mul_le_mul hR hG (norm_nonneg _) hW
  rw [arch, mul_inv, mul_inv, norm_mul, norm_mul, ← inv_pow, ← inv_pow, norm_pow, norm_pow]
  apply le_trans (mul_le_mul (mul_le_mul hE (pow_le_pow_left₀ (norm_nonneg _) hR _)
    (by positivity) (Real.exp_pos _).le) (pow_le_pow_left₀ (norm_nonneg _) hcomplex _)
    (by positivity) (mul_nonneg (Real.exp_pos _).le (pow_nonneg hW _)))
  apply le_of_eq
  calc _ = E*W^d := by dsimp only [d]; rw [pow_add, pow_mul, sq]; ring
       _ = _ := by dsimp only [W]; rw [mul_pow, ← Real.exp_nat_mul, ← mul_assoc, ← mul_assoc]

private theorem gammaR_conj_norm (z : ℂ) : ‖Gammaℝ (conj z)‖ = ‖Gammaℝ z‖ := by
  rw [Gammaℝ_def, Gammaℝ_def, norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos Real.pi_pos,
    norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  have he : conj z/2 = conj (z/2) := by rw [map_div₀, Complex.conj_ofNat]
  rw [he, Gamma_conj, Complex.norm_conj]
  simp only [div_ofNat_re, neg_re, conj_re]

theorem arch_conj_norm (z : ℂ) : ‖arch K (conj z)‖ = ‖arch K z‖ := by
  simp only [arch, ← Gammaℝ_mul_Gammaℝ_add_one, norm_mul, norm_pow, norm_exp,
    mul_re, ofReal_im, ofReal_re, mul_zero, sub_zero, conj_re, gammaR_conj_norm]
  rw [show conj z+1=conj (z+1) by simp, gammaR_conj_norm]

theorem arch_shift_two {z : ℂ} (hz : z ≠ 0) (hz' : z+1 ≠ 0) :
    arch K (z+2) = arch K z * exp ((2:ℂ)*(Real.log (discr K).natAbs/2 : ℝ)) *
      (z/(2*Real.pi))^(nrRealPlaces K+nrComplexPlaces K) *
      ((z+1)/(2*Real.pi))^nrComplexPlaces K := by
  have hC : Gammaℂ (z+2) = Gammaℂ z*(z/(2*Real.pi))*((z+1)/(2*Real.pi)) := by
    rw [show z+2=z+1+1 by ring, Gammaℂ_add_one hz', Gammaℂ_add_one hz]; ring
  rw [arch, arch, add_mul, exp_add, Gammaℝ_add_two hz, hC,
    show Gammaℝ z*z/2/Real.pi = Gammaℝ z*(z/(2*Real.pi)) by ring,
    mul_pow, mul_pow, mul_pow, pow_add]; ring

#print axioms reciprocal_arch_growth
#print axioms arch_conj_norm
#print axioms arch_shift_two
end OMA.ArchGrowth
