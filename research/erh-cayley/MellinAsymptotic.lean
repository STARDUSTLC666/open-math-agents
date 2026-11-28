import StripDecay

/-! The rational principal term and uniform asymptotics of the modified
Mellin integral. The completed numerator is its rapidly decreasing error. -/
noncomputable section
namespace OMA.MellinAsymptotic
open Complex NumberField Set Filter
open CompletedNumerator HighStrip ThetaContinuation
open scoped Topology
variable (K : Type*) [Field K] [NumberField K]

def denominator (s : ℂ) := s*(s-1)

theorem normalized_error (s : ℂ) :
    s*(1-s)*(pair K).Λ₀ s - cst K = -xi K s := by
  rw [xi]; ring

theorem rational_error {s : ℂ} (hs : s ≠ 0) (hs' : s ≠ 1) :
    (pair K).Λ₀ s + cst K / denominator s = xi K s / denominator s := by
  rw [xi, denominator]
  field_simp [hs, sub_ne_zero.mpr hs']

theorem denominator_lower (s : ℂ) : s.im^2 ≤ ‖denominator s‖ := by
  have h1 := abs_im_le_norm s
  have h2 := abs_im_le_norm (s-1)
  rw [sub_im,one_im,sub_zero] at h2
  rw [denominator, norm_mul, ← sq_abs s.im, sq]
  exact mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)

theorem remainder (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ s : ℂ, s.re ∈ Icc (-1:ℝ) 2 → 1 ≤ |s.im| →
      (1+s.im^2)^(n+1) * ‖(pair K).Λ₀ s + cst K / denominator s‖ ≤ A := by
  obtain ⟨C,hC,h⟩ := rapid_strip K n
  refine ⟨2*C, mul_nonneg zero_le_two hC, ?_⟩
  intro s hS ht
  have hI : 1 ≤ s.im^2 := by simpa only [one_pow, sq_abs] using
    (sq_le_sq₀ zero_le_one (abs_nonneg _)).mpr ht
  have hn0 : s ≠ 0 := by rintro rfl; norm_num at ht
  have hn1 : s ≠ 1 := by rintro rfl; norm_num at ht
  have hd := denominator_lower s
  have hpos : 0 < ‖denominator s‖ := by linarith
  have hfac : (1+s.im^2)/‖denominator s‖ ≤ 2 := (div_le_iff₀ hpos).mpr (by linarith)
  rw [rational_error K hn0 hn1, norm_div]
  calc _ = ((1+s.im^2)/‖denominator s‖)*((1+s.im^2)^n*‖xi K s‖) := by rw [pow_succ]; ring
       _ ≤ _ := mul_le_mul hfac (h s hS) (by positivity) zero_le_two

private theorem cst_real : cst K = ((cst K).re:ℂ) := rfl

theorem cst_pos : 0 < (cst K).re := by
  unfold cst
  rw [ofReal_re]
  exact div_pos (mul_pos (mul_pos (by positivity) (Units.regulator_pos K))
      (Nat.cast_pos.mpr (classNumber_pos K))) (Nat.cast_pos.mpr (Units.torsionOrder_pos K))

private theorem denominator_expand (s : ℂ) :
    denominator s = (((s.re*(s.re-1)):ℝ):ℂ) - (s.im:ℂ)^2 +
      ((2*s.re-1:ℝ):ℂ)*(s.im:ℂ)*I := by
  rw [denominator]
  apply Complex.ext
  · simp [sq, mul_re, mul_im]
  · simp [sq, mul_re, mul_im]
    ring

private def correction (a t : ℝ) : ℂ := (a*(a-1)-(2*a-1)^2 : ℝ) +
  ((2*a-1:ℝ):ℂ)*((a*(a-1):ℝ):ℂ)*I/(t:ℂ)

private theorem correction_bound {a t : ℝ} (ha : a ∈ Icc (0:ℝ) 1) (ht : 1 ≤ |t|) :
    ‖correction a t‖ ≤ 3 := by
  let d := a*(a-1)
  let b := 2*a-1
  have hb : |b| ≤ 1 := abs_le.mpr ⟨by dsimp [b];linarith [ha.1], by dsimp [b];linarith [ha.2]⟩
  have hd : |d| ≤ 1 := by
    apply abs_le.mpr
    constructor
    · dsimp [d]; nlinarith [sq_nonneg (a-1/2)]
    · exact (mul_nonpos_of_nonneg_of_nonpos ha.1 (sub_nonpos.mpr ha.2)).trans zero_le_one
  have hb2 : b^2 ≤ 1 := by simpa only [sq_abs, one_pow] using (sq_le_sq₀ (abs_nonneg _) zero_le_one).mpr hb
  have hpos : 0 < |t| := zero_lt_one.trans_le ht
  have him : |b| * |d| / |t| ≤ 1 := by
    apply (div_le_iff₀ hpos).mpr
    simpa only [one_mul] using (mul_le_mul hb hd (abs_nonneg _) zero_le_one).trans (by simpa using ht)
  change ‖((d-b^2:ℝ):ℂ)+(b:ℂ)*(d:ℂ)*I/(t:ℂ)‖ ≤ 3
  apply (norm_add_le _ _).trans
  simp only [norm_div,norm_mul,norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs]
  have hreal : |d-b^2| ≤ |d| + b^2 := by
    calc |d-b^2| ≤ |d| + |b^2| := by simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le d 0 (b^2)
         _ = _ := by rw [abs_of_nonneg (sq_nonneg b)]
  linarith

private theorem principal_second {s : ℂ} (ht : 1 ≤ |s.im|) :
    (s.im:ℂ)^2*(pair K).Λ₀ s - cst K - I*((2*s.re-1:ℝ):ℂ)*cst K/(s.im:ℂ) =
      (s.im:ℂ)^2*((pair K).Λ₀ s + cst K/denominator s) -
        cst K*correction s.re s.im/denominator s := by
  have ht0 : s.im ≠ 0 := by intro h; rw [h] at ht; norm_num at ht
  have hD : denominator s ≠ 0 := mul_ne_zero (by rintro rfl; simp at ht0)
    (sub_ne_zero.mpr (by rintro rfl; simp at ht0))
  field_simp [ofReal_ne_zero.mpr ht0, hD]
  rw [denominator_expand, correction]
  push_cast
  field_simp [ofReal_ne_zero.mpr ht0]
  ring_nf
  simp only [I_sq]
  ring

/-- The first two coefficients, with a uniform fourth-order error after
dividing by t^2. Complex notation packages the real and imaginary parts. -/
theorem two_terms :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (s : ℂ), s.re ∈ Icc (0:ℝ) 1 → 1 ≤ |s.im| →
      s.im^2 * ‖(s.im:ℂ)^2*(pair K).Λ₀ s - cst K -
        I*((2*s.re-1:ℝ):ℂ)*cst K/(s.im:ℂ)‖ ≤ A := by
  obtain ⟨C,hC,hr⟩ := remainder K 1
  refine ⟨C+3*‖cst K‖,by positivity,?_⟩
  intro s hs ht
  have hR := hr s ⟨by linarith [hs.1],by linarith [hs.2]⟩ ht
  have hD := denominator_lower s
  have ht0 : s.im ≠ 0 := by intro h; rw [h] at ht; norm_num at ht
  have hpos : 0 < ‖denominator s‖ := (sq_pos_of_ne_zero ht0).trans_le hD
  have hr1 : s.im^2 * ‖(s.im:ℂ)^2*((pair K).Λ₀ s+cst K/denominator s)‖ ≤ C := by
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,← mul_assoc,← sq]
    apply le_trans _ hR
    exact mul_le_mul_of_nonneg_right ((sq_le_sq₀ (sq_nonneg _) (by positivity)).mpr (by linarith)) (norm_nonneg _)
  have hr2 : s.im^2 * ‖cst K*correction s.re s.im/denominator s‖ ≤ 3*‖cst K‖ := by
    rw [norm_div,norm_mul,← mul_div_assoc,div_le_iff₀ hpos]
    calc _ = ‖cst K‖*(s.im^2*‖correction s.re s.im‖) := by ring
         _ ≤ ‖cst K‖*(‖denominator s‖*3) := mul_le_mul_of_nonneg_left
              (mul_le_mul hD (correction_bound hs ht) (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
         _ = _ := by ring
  rw [principal_second K ht]
  apply (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (sq_nonneg _)).trans
  rw [mul_add]
  exact add_le_add hr1 hr2

#print axioms normalized_error
#print axioms rational_error
#print axioms remainder
#print axioms two_terms
end OMA.MellinAsymptotic
