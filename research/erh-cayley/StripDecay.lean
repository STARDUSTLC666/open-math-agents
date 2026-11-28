import CompletedNumerator

/-! A Phragmén-Lindelöf argument for the entire completed numerator. On
-1 ≤ Re(s) ≤ 2 the symmetric quadratic weight dominates 1+Im(s)^2. -/
noncomputable section
namespace OMA.HighStrip
open Complex NumberField Filter Set MeasureTheory Asymptotics
open ThetaContinuation CompletedNumerator GeneralHeat FoldedPhase
open scoped Topology Filter
variable (K : Type*) [Field K] [NumberField K]

private theorem heat_moment : IntegrableOn (fun x : ℝ => x*heat K x) (Ioi 1) := by
  have h := (integrand_int K 2).mono_set (Ioi_subset_Ioi (zero_le_one : (0:ℝ) ≤ 1))
  have hr : IntegrableOn (fun x => (integrand K 2 x).re) (Ioi 1) := h.re
  apply hr.congr_fun _ measurableSet_Ioi
  intro x hx
  change 1 < x at hx
  simp [integrand, show (2:ℂ)-1=1 by norm_num, WeakFEPair.f_modif, hx, hx.not_gt,
    pair, kernel_eq K (zero_lt_one.trans hx), mul_re]

theorem lambda_wide_bounded :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ s : ℂ, s.re ∈ Icc (-1:ℝ) 2 → ‖(pair K).Λ₀ s‖ ≤ A := by
  let A := ∫ x in Ioi 1, 2*(x*heat K x)
  refine ⟨A,setIntegral_nonneg measurableSet_Ioi (fun x hx => mul_nonneg zero_le_two
    (mul_nonneg (zero_le_one.trans hx.le) (heat_nonneg K x))),?_⟩
  intro s hs
  have hi (z : ℂ) := (integrand_int K z).mono_set (Ioi_subset_Ioi (zero_le_one : (0:ℝ) ≤ 1))
  have bound (z : ℂ) (hz : z.re ≤ 2) {x : ℝ} (hx : 1 < x) :
      ‖integrand K z x‖ ≤ x*heat K x := by
    have h0 := zero_lt_one.trans hx
    have hv : (pair K).f_modif x = (heat K x:ℂ) := by
      simp [WeakFEPair.f_modif, hx, hx.not_gt, pair, kernel_eq K h0]
    rw [integrand, norm_mul, hv, Complex.norm_of_nonneg (heat_nonneg K x),
      norm_cpow_eq_rpow_re_of_pos h0]
    simp only [sub_re, one_re]
    apply mul_le_mul_of_nonneg_right _ (heat_nonneg K x)
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx.le (by linarith : z.re-1 ≤ 1)
  rw [folded K s]
  apply (norm_integral_le_integral_norm (μ := volume.restrict (Ioi 1)) _).trans
  apply setIntegral_mono_on ((hi s).add (hi (1-s))).norm ((heat_moment K).const_mul 2) measurableSet_Ioi
  intro x hx
  change ‖integrand K s x+integrand K (1-s) x‖ ≤ 2*(x*heat K x)
  apply (norm_add_le _ _).trans
  linarith [bound s hs.2 hx, bound (1-s) (by rw [sub_re, one_re]; linarith [hs.1]) hx]

def weight (s : ℂ) := (s+2)*(3-s)
def weighted (n : ℕ) (s : ℂ) := weight s ^ n * xi K s

private theorem reflected (n : ℕ) (s : ℂ) : weighted K n (1-s) = weighted K n s := by
  rw [weighted, weighted, xi_reflect]
  rw [show weight (1-s) = weight s by unfold weight; ring]

private theorem weight_lower {s : ℂ} (hs : s.re ∈ Icc (-1:ℝ) 2) :
    1+s.im^2 ≤ ‖weight s‖ := by
  have hA : 1+s.im^2 ≤ ‖s+2‖^2 := by
    rw [Complex.sq_norm, normSq_apply]
    simp only [add_re, re_ofNat, add_im, im_ofNat, add_zero]
    nlinarith [mul_self_le_mul_self zero_le_one (by linarith [hs.1] : 1 ≤ s.re+2)]
  have hB : 1+s.im^2 ≤ ‖3-s‖^2 := by
    rw [Complex.sq_norm, normSq_apply]
    simp only [sub_re, re_ofNat, sub_im, im_ofNat, zero_sub, neg_mul_neg]
    nlinarith [mul_self_le_mul_self zero_le_one (by linarith [hs.2] : 1 ≤ 3-s.re)]
  apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp
  rw [weight, norm_mul, mul_pow]
  simpa only [← sq] using mul_le_mul hA hB (by positivity) (sq_nonneg _)

private theorem weighted_boundary (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, s.re=2 → ‖weighted K n s‖ ≤ C := by
  obtain ⟨Z,hZ,hbound⟩ := right_boundary K (2*n)
  refine ⟨6^n*Z, mul_nonneg (by positivity) hZ, ?_⟩
  intro s hs
  have hpos : 2 ≤ ‖s‖ := hs ▸ re_le_norm s
  have hL : ‖s+2‖ ≤ 2*‖s‖ := by
    have h := norm_add_le s (2:ℂ); rw [Complex.norm_ofNat] at h; linarith
  have hR : ‖3-s‖ ≤ 3*‖s‖ := by
    have h := norm_sub_le (3:ℂ) s; rw [Complex.norm_ofNat] at h; linarith
  have hw : ‖weight s‖ ≤ 6*‖s‖^2 := by
    rw [weight, norm_mul]
    exact (mul_le_mul hL hR (norm_nonneg _) (by positivity)).trans_eq (by ring)
  rw [weighted, norm_mul, norm_pow]
  calc _ ≤ (6*‖s‖^2)^n*‖xi K s‖ := mul_le_mul_of_nonneg_right
              (pow_le_pow_left₀ (norm_nonneg _) hw n) (norm_nonneg _)
       _ = (6:ℝ)^n*(‖s‖^(2*n)*‖xi K s‖) := by rw [mul_pow, pow_mul, mul_assoc]
       _ ≤ _ := mul_le_mul_of_nonneg_left (hbound s hs) (by positivity)

private theorem polynomial_growth (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ s : ℂ, s.re ∈ Icc (-1:ℝ) 2 →
      ‖weighted K n s‖ ≤ A*(4+|s.im|)^(2*n+2) := by
  obtain ⟨B,hB,hBound⟩ := lambda_wide_bounded K
  refine ⟨B+‖cst K‖,add_nonneg hB (norm_nonneg _),?_⟩
  intro s hs
  let m := 4+|s.im|
  have hm : 1 ≤ m := by dsimp [m]; linarith [abs_nonneg s.im]
  have hm0 := zero_le_one.trans hm
  have hnn (z : ℂ) (hre : |z.re| ≤ 4) (him : |z.im|=|s.im|) : ‖z‖ ≤ m := by
    apply (norm_le_abs_re_add_abs_im z).trans
    rw [him]; exact add_le_add_left hre _
  have ha : ‖s‖ ≤ m := hnn s (abs_le.mpr ⟨by linarith [hs.1],by linarith [hs.2]⟩) rfl
  have hb : ‖s-1‖ ≤ m := hnn _ (by rw [sub_re, one_re]; exact abs_le.mpr ⟨by linarith [hs.1],by linarith [hs.2]⟩) (by simp)
  have hc : ‖s+2‖ ≤ m := hnn _ (by rw [add_re, re_ofNat]; exact abs_le.mpr ⟨by linarith [hs.1],by linarith [hs.2]⟩) (by simp)
  have hd : ‖3-s‖ ≤ m := hnn _ (by rw [sub_re, re_ofNat]; exact abs_le.mpr ⟨by linarith [hs.2],by linarith [hs.1]⟩) (by simp)
  have hw : ‖weight s‖ ≤ m^2 := by
    rw [weight,norm_mul,sq]; exact mul_le_mul hc hd (norm_nonneg _) hm0
  have hN : ‖xi K s‖ ≤ m^2*(B+‖cst K‖) := by
    apply (norm_add_le _ _).trans
    simp only [norm_mul]
    calc _ ≤ m*m*B + ‖cst K‖ := add_le_add_left
            (mul_le_mul (mul_le_mul ha hb (norm_nonneg _) hm0) (hBound s hs) (norm_nonneg _) (mul_nonneg hm0 hm0)) _
         _ ≤ m*m*B + m^2*‖cst K‖ := add_le_add_right
             (le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ hm)) _
         _ = _ := by ring
  rw [weighted,norm_mul,norm_pow]
  calc _ ≤ (m^2)^n*(m^2*(B+‖cst K‖)) := mul_le_mul
             (pow_le_pow_left₀ (norm_nonneg _) hw n) hN (norm_nonneg _) (by positivity)
       _ = _ := by change _ = (B+‖cst K‖)*m^(2*n+2); rw [pow_add,pow_mul]; ring

private theorem poly_le_pl (u : ℝ) (hu : 0 ≤ u) (p : ℕ) :
    (4+u)^p ≤ (4:ℝ)^p * Real.exp ((p:ℝ)*Real.exp u) := by
  have h := Real.add_one_le_exp u
  have h1 : 4+u ≤ 4*Real.exp u := by linarith
  calc _ ≤ (4*Real.exp u)^p := pow_le_pow_left₀ (by positivity) h1 p
       _ = (4:ℝ)^p * Real.exp ((p:ℝ)*u) := by rw [mul_pow, Real.exp_nat_mul]
       _ ≤ _ := by apply mul_le_mul_of_nonneg_left _ (by positivity)
                   apply Real.exp_le_exp.mpr
                   apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg p); linarith

/-- Uniform rapid decay of the entire numerator even on the closed strip
-1 ≤ Re(s) ≤ 2. Constants may depend on the field and the requested order. -/
theorem rapid_strip (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, s.re ∈ Icc (-1:ℝ) 2 →
        (1+s.im^2)^n * ‖xi K s‖ ≤ C := by
  obtain ⟨C,hC,hRight⟩ := weighted_boundary K n
  refine ⟨C,hC,?_⟩
  have hLeft (s : ℂ) (hs : s.re = -1) : ‖weighted K n s‖ ≤ C := by
    rw [← reflected K n s]
    exact hRight _ (by rw [sub_re,one_re,hs]; norm_num)
  have hdiff : Differentiable ℂ (weighted K n) := by
    apply Differentiable.mul _ (xi_diff K)
    exact (((differentiable_id.add_const (2:ℂ)).mul (differentiable_id.const_sub (3:ℂ))).pow n)
  obtain ⟨A,hA,hpoly⟩ := polynomial_growth K n
  let p := 2*n+2
  intro s hs
  have hb : ‖weighted K n s‖ ≤ C := by
    apply PhragmenLindelof.vertical_strip hdiff.diffContOnCl _ hLeft hRight hs.1 hs.2
    refine ⟨1, by linarith [Real.pi_gt_three], (p:ℝ), isBigO_iff.mpr ⟨A*4^p, ?_⟩⟩
    filter_upwards [mem_inf_of_right (mem_principal_self (Complex.re ⁻¹' Ioo (-1:ℝ) 2))] with z hz
    rw [Real.norm_eq_abs, Real.abs_exp]
    calc ‖weighted K n z‖ ≤ A*(4+|z.im|)^p := hpoly z ⟨le_of_lt hz.1,le_of_lt hz.2⟩
         _ ≤ A*((4:ℝ)^p*Real.exp ((p:ℝ)*Real.exp |z.im|)) :=
               mul_le_mul_of_nonneg_left (poly_le_pl _ (abs_nonneg _) _) hA
         _ = _ := by simp only [one_mul, mul_assoc]
  apply le_trans _ hb
  rw [weighted,norm_mul,norm_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (weight_lower hs) n) (norm_nonneg _)

#print axioms lambda_wide_bounded
#print axioms rapid_strip
end OMA.HighStrip
