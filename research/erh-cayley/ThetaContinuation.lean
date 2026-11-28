import DedekindThetaAudit

/-! A concrete pole-removed Dedekind zeta on Re(s)>0 from the audited theta
kernel. No prior continuation of the ideal Dirichlet series is assumed. -/
noncomputable section
namespace OMA.ThetaContinuation
open Complex Filter Set NumberField NumberField.InfinitePlace NumberField.Units MeasureTheory
open scoped NumberField Topology

variable (K : Type*) [Field K] [NumberField K]

def cst : ℂ := ((2 : ℝ) ^ (nrRealPlaces K + nrComplexPlaces K) * regulator K * classNumber K / torsionOrder K : ℝ)

theorem cst_ne : cst K ≠ 0 := by
  have h : 0 < (2 : ℝ) ^ (nrRealPlaces K + nrComplexPlaces K) * regulator K * classNumber K / torsionOrder K :=
    div_pos (mul_pos (mul_pos (by positivity) (regulator_pos K)) (Nat.cast_pos.mpr (classNumber_pos K)))
      (Nat.cast_pos.mpr (torsionOrder_pos K))
  exact ofReal_ne_zero.mpr h.ne'

def arch (s : ℂ) : ℂ := exp (s * (Real.log (discr K).natAbs / 2 : ℝ)) *
  Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K

theorem arch_ne {s : ℂ} (hs : 0 < s.re) : arch K s ≠ 0 := by
  have hs' : 0 < (s+1).re := by rw [add_re, one_re]; linarith
  have hC : Gammaℂ s ≠ 0 := by
    rw [← Gammaℝ_mul_Gammaℝ_add_one]
    exact mul_ne_zero (Gammaℝ_ne_zero_of_re_pos hs) (Gammaℝ_ne_zero_of_re_pos hs')
  exact mul_ne_zero (mul_ne_zero (exp_ne_zero _) (pow_ne_zero _ (Gammaℝ_ne_zero_of_re_pos hs))) (pow_ne_zero _ hC)

theorem analytic_arch_inv : Differentiable ℂ (fun s => (arch K s)⁻¹) := by
  simp only [arch, mul_inv, ← inv_pow, ← Complex.exp_neg]
  apply Differentiable.mul _ (differentiable_Gammaℂ_inv.pow _)
  apply Differentiable.mul _ (differentiable_Gammaℝ_inv.pow _)
  fun_prop

def pair : WeakFEPair ℂ where
  f := fun x => DedekindMellin.kernel K x + cst K
  g := fun x => DedekindMellin.kernel K x + cst K
  f₀ := cst K
  g₀ := cst K
  k := 1
  ε := 1
  hk := zero_lt_one
  hε := one_ne_zero
  hf_int := (DedekindMellin.kernel_local K).add (locallyIntegrableOn_const _)
  hg_int := (DedekindMellin.kernel_local K).add (locallyIntegrableOn_const _)
  hf_top := fun r => by simpa using DedekindMellin.kernel_decay K r
  hg_top := fun r => by simpa using DedekindMellin.kernel_decay K r
  h_feq := fun x hx => by
    have hk : HeckeExpansion.DedekindMellin.kernel K = DedekindMellin.kernel K := rfl
    simpa [cst, hk] using ThetaAudit.theta (K := K) hx

theorem completed_agrees {s : ℂ} (hs : 1 < s.re) :
    (pair K).Λ s = arch K s * dedekindZeta K s := by
  have he : mellin (DedekindMellin.kernel K) s = (pair K).Λ s := by
    simpa [pair] using ((pair K).hasMellin (s := s) hs).2
  exact he.symm.trans (DedekindMellin.kernel_hasMellin K hs).2

/-- Multiplying the completed Laurent expression by s(s-1) leaves
`s(s-1)Λ₀ + c`. Only s, not s-1, is divided out in this definition. -/
def reg (s : ℂ) : ℂ := ((s * (s-1) * (pair K).Λ₀ s + cst K) / s) * (arch K s)⁻¹

theorem reg_diff {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ (reg K) s := by
  have hn : s ≠ 0 := by rintro rfl; simp at hs
  have hnum : DifferentiableAt ℂ (fun z : ℂ => z * (z-1) * (pair K).Λ₀ z + cst K) s :=
    (((differentiableAt_id.mul (differentiableAt_id.sub_const (1:ℂ))).mul
      ((pair K).differentiable_Λ₀ s)).add_const (cst K))
  exact (hnum.div differentiableAt_id hn).mul (analytic_arch_inv K s)

theorem reg_one : reg K 1 ≠ 0 := by
  simpa [reg] using mul_ne_zero (cst_ne K) (inv_ne_zero (arch_ne K (s := 1) (by norm_num)))

theorem reg_agrees {s : ℂ} (hs : 1 < s.re) : reg K s = (s-1) * dedekindZeta K s := by
  have h0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have h1 : s ≠ 1 := by rintro rfl; norm_num at hs
  have hA := arch_ne K (zero_lt_one.trans hs)
  have he : (s * (s-1) * (pair K).Λ₀ s + cst K) / s = (s-1) * (pair K).Λ s := by
    rw [WeakFEPair.Λ]
    change _ = (s-1) * ((pair K).Λ₀ s - (1/s) * cst K - (1/(1-s)) * cst K)
    field_simp [h0, sub_ne_zero.mpr h1.symm]; ring
  rw [reg, he, completed_agrees K hs]
  field_simp [hA]

#print axioms OMA.ThetaContinuation.reg_diff
#print axioms OMA.ThetaContinuation.reg_one
#print axioms OMA.ThetaContinuation.reg_agrees
end OMA.ThetaContinuation
