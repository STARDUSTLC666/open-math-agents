import RadialProfile

/-! Positive heat and its discriminant-dependent contraction for every
number field. Unfolding by ideal class supplies genuine summability. -/
noncomputable section
namespace OMA.GeneralHeat
open Complex NumberField NumberField.InfinitePlace NumberField.Units
open OMA.HeckeExpansion RadialProfile
open DedekindIdealClasses DedekindGeneralTheta DedekindSignatureKernel
open scoped NumberField nonZeroDivisors Classical
variable (K : Type*) [Field K] [NumberField K]

def scale : ℝ := (Real.sqrt ((discr K).natAbs : ℝ))⁻¹
def rate : ℝ := Real.pi * degree K * (scale K)^(exponent K)

theorem scale_pos : 0 < scale K := inv_pos.mpr <| Real.sqrt_pos.mpr
  (by exact_mod_cast Int.natAbs_pos.mpr (discr_ne_zero K))
theorem rate_pos : 0 < rate K := mul_pos (mul_pos Real.pi_pos (degree_pos K))
  (Real.rpow_pos_of_pos (scale_pos K) _)

def term (x : ℝ) (n : ℕ) : ℝ := if n=0 then 0 else
  (HeckeExpansion.DedekindMellin.coeff K n : ℝ) * radial K (scale K * x * n)
def heat (x : ℝ) : ℝ := 2^(nrRealPlaces K + nrComplexPlaces K) * ∑' n, term K x n

theorem term_nonneg (x : ℝ) (n : ℕ) : 0 ≤ term K x n := by
  unfold term; split
  · exact le_rfl
  · exact mul_nonneg (Nat.cast_nonneg _) (radial_nonneg K _)
theorem heat_nonneg (x : ℝ) : 0 ≤ heat K x :=
  mul_nonneg (by positivity) (tsum_nonneg (term_nonneg K x))

private theorem term_cast {x : ℝ} (hx : 0 < x) (n : ℕ) :
    (term K x n : ℂ) = if n=0 then 0 else (HeckeExpansion.DedekindMellin.coeff K n : ℂ) *
    profile (nrRealPlaces K) (nrComplexPlaces K) (q K * x * n) := by
  by_cases hn : n=0
  · simp [hn, term]
  · have hp := mul_pos (mul_pos (scale_pos K) hx) (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
    simp only [term, hn, if_false, ofReal_mul, ofReal_natCast]
    rw [← profile_eq K hp]; rfl

theorem kernel_eq {x : ℝ} (hx : 0 < x) : _root_.DedekindMellin.kernel K x = (heat K x : ℂ) := by
  have hk := explicit_kernel K hx
  change _root_.DedekindMellin.kernel K x = _ at hk
  rw [hk, heat, ofReal_mul, ofReal_pow, ofReal_ofNat, ofReal_tsum]
  congr 1
  exact tsum_congr fun n => (term_cast K hx n).symm

theorem summable_term {x : ℝ} (hx : 0 < x) : Summable (term K x) := by
  let W : ℂ := torsionOrder K
  have hs : HasSum (fun n => W * (term K x n : ℂ)) (∑ C, (avg K C x - (regulator K : ℂ))) := by
    apply (hasSum_sum fun C _ => DedekindClassUnfold.unfolds K C x hx).congr_fun
    intro n
    rw [term_cast K hx]
    simp only [← Finset.sum_mul, ← Nat.cast_sum, ← Finset.sum_mul]
    by_cases hn : n=0
    · subst n
      have h0 (C : ClassGroup (𝓞 K)) : Nat.card (ClassFiber K C 0)=0 := by
        let : IsEmpty (ClassFiber K C 0) := ⟨fun I => (Ideal.absNorm_pos_of_nonZeroDivisors I.val).ne' I.prop.1⟩
        simp
      simp [h0]
    · rw [if_neg hn, ← coeff_eq_sum_classes K hn, Nat.cast_mul]
      dsimp only [W]; ring
  have hw : W ≠ 0 := Nat.cast_ne_zero.mpr (torsionOrder_ne_zero K)
  apply Complex.summable_ofReal.mp
  simpa only [← mul_assoc, inv_mul_cancel₀ hw, one_mul] using hs.summable.mul_left W⁻¹

theorem contraction {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    heat K y ≤ Real.exp (-(rate K * (y^(exponent K) - x^(exponent K)))) * heat K x := by
  let a := exponent K
  let m := Real.exp (-(rate K*(y^a-x^a)))
  have hy := hx.trans_le hxy
  have hq := scale_pos K
  have ha := (exponent_pos K).le
  have hd := sub_nonneg.mpr (Real.rpow_le_rpow hx.le hxy ha)
  have point (n : ℕ) : term K y n ≤ m * term K x n := by
    by_cases hn : n=0
    · simp [term,hn]
    · have hn0 : 0 < (n:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      have hn1 : (1:ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have hp := radial_contraction K (mul_pos (mul_pos hq hx) hn0)
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hxy hq.le) hn0.le)
      have hc : Real.exp (-(Real.pi*degree K*((scale K*y*n)^a-(scale K*x*n)^a))) ≤ m := by
        dsimp only [m]; rw [Real.exp_le_exp, neg_le_neg_iff]
        simp only [Real.mul_rpow (mul_pos hq hy).le hn0.le,
          Real.mul_rpow (mul_pos hq hx).le hn0.le, Real.mul_rpow hq.le hy.le, Real.mul_rpow hq.le hx.le]
        have hn' := Real.one_le_rpow hn1 ha
        have hleft := mul_nonneg (mul_nonneg Real.pi_pos.le (degree_pos K).le) (Real.rpow_nonneg hq.le a)
        change Real.pi*degree K*(scale K)^a*(y^a-x^a) ≤ _
        calc _ ≤ Real.pi*degree K*(scale K)^a*(y^a-x^a)*(n:ℝ)^a :=
                le_mul_of_one_le_right (mul_nonneg hleft hd) hn'
             _ = _ := by ring
      have hrad := hp.trans (mul_le_mul_of_nonneg_right hc (radial_nonneg K _))
      simp only [term, hn, if_false, mul_left_comm m]
      exact mul_le_mul_of_nonneg_left hrad (Nat.cast_nonneg _)
  have hs := (summable_term K hy).tsum_le_tsum point ((summable_term K hx).mul_left m)
  rw [tsum_mul_left] at hs
  unfold heat
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left hs (by positivity)

theorem heat_inversion {x : ℝ} (hx : 0 < x) :
    heat K x⁻¹ = x*heat K x + (x-1)*(ThetaContinuation.cst K).re := by
  have h := (ThetaContinuation.pair K).h_feq x hx
  change _root_.DedekindMellin.kernel K (1/x) + ThetaContinuation.cst K =
    (1*((x^(1:ℝ):ℝ):ℂ)) • (_root_.DedekindMellin.kernel K x + ThetaContinuation.cst K) at h
  rw [one_div, kernel_eq K (inv_pos.mpr hx), kernel_eq K hx, Real.rpow_one, one_mul, smul_eq_mul] at h
  have hr := congrArg Complex.re h
  simp only [add_re, ofReal_re, mul_re, ofReal_im, zero_mul, sub_zero] at hr
  linarith

#print axioms kernel_eq
#print axioms summable_term
#print axioms contraction
#print axioms heat_inversion
end OMA.GeneralHeat
