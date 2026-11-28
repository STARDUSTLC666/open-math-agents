import ArchGrowth

/-! A polynomial bound for the pole-removed Dedekind zeta on a closed
strip crossing the line of absolute convergence. -/
noncomputable section
namespace OMA.ZetaGrowth
open Complex NumberField NumberField.InfinitePlace Filter Set Asymptotics
open ThetaContinuation CompletedNumerator ExactRadius
open scoped ComplexConjugate Topology
variable (K : Type*) [Field K] [NumberField K]

abbrev power := Module.finrank ℚ K + 1
private def quotient (s : ℂ) := entireReg K s / (s+2)^power K

private theorem shift_ge {s : ℂ} (hs : -(1/2:ℝ) ≤ s.re) : 1 ≤ ‖s+2‖ := by
  have h := re_le_norm (s+2)
  rw [add_re, re_ofNat] at h
  linarith

private theorem mirror {s : ℂ} (hs : s.re = -(1/2:ℝ)) : 1-s = conj s+2 := by
  apply Complex.ext <;> norm_num [hs]

private theorem arch_ratio {s : ℂ} (hs : s.re = -(1/2:ℝ)) :
    ‖arch K (1-s) * (arch K s)⁻¹‖ ≤
      ‖exp ((2:ℂ)*(Real.log (discr K).natAbs/2 : ℝ))‖ * ‖s+2‖^(Module.finrank ℚ K) := by
  have h0 : conj s ≠ 0 := by intro h; have := congrArg Complex.re h; simp [hs] at this
  have h1 : conj s+1 ≠ 0 := by intro h; have := congrArg Complex.re h; norm_num [hs] at this
  have hnorm (u : ℂ) (hu : u.re^2 ≤ (s+2).re^2) (ht : u.im^2=(s+2).im^2) :
      ‖u‖ ≤ ‖s+2‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [Complex.sq_norm, normSq_apply, ← sq]
    linarith
  have den : 1 ≤ ‖(2:ℂ)*Real.pi‖ := by
    rw [norm_mul, Complex.norm_ofNat, Complex.norm_of_nonneg Real.pi_pos.le]
    linarith [Real.pi_gt_three]
  have hf (u : ℂ) (hu : ‖u‖ ≤ ‖s+2‖) : ‖u/(2*Real.pi)‖ ≤ ‖s+2‖ := by
    rw [norm_div]; exact (div_le_self (norm_nonneg _) den).trans hu
  have ha := hf (conj s) (hnorm _ (by norm_num [hs]) (by simp))
  have hb := hf (conj s+1) (hnorm _ (by norm_num [hs]) (by simp))
  let E := exp ((2:ℂ)*(Real.log (discr K).natAbs/2 : ℝ))
  let r := nrRealPlaces K + nrComplexPlaces K
  let c := nrComplexPlaces K
  have hd : r+c = Module.finrank ℚ K := by
    dsimp [r,c]; rw [← card_add_two_mul_card_eq_rank]; omega
  rw [mirror hs, ArchGrowth.arch_shift_two K h0 h1]
  simp only [norm_mul, norm_pow, ArchGrowth.arch_conj_norm, norm_inv]
  by_cases hz : ‖arch K s‖ = 0
  · simp [hz]
  have hcancel := mul_inv_cancel₀ hz
  calc _ = (‖arch K s‖ * ‖arch K s‖⁻¹) *
            (‖E‖ * ‖conj s/(2*Real.pi)‖^r * ‖(conj s+1)/(2*Real.pi)‖^c) := by
              dsimp only [E,r,c]; ring
       _ ≤ ‖E‖ * ‖s+2‖^r * ‖s+2‖^c := by rw [hcancel, one_mul]; gcongr
       _ = _ := by rw [mul_assoc, ← pow_add, hd]

theorem strip_edges :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, s.re = -(1/2:ℝ) ∨ s.re = 3/2 →
      ‖entireReg K s‖ ≤ C * ‖s+2‖^power K := by
  obtain ⟨B,hB⟩ := DedekindMellin.bounded K (a := 3/2) (by norm_num)
  let Z := max B 0
  let E := ‖exp ((2:ℂ)*(Real.log (discr K).natAbs/2 : ℝ))‖
  let C := max (Z*E) (4*Z)
  have hZ : 0 ≤ Z := le_max_right _ _
  have hc : 0 ≤ C := (mul_nonneg hZ (norm_nonneg _)).trans (le_max_left _ _)
  refine ⟨C,hc,?_⟩
  intro s hs
  rcases hs with hl | hr
  · have hn : s ≠ 0 := by rintro rfl; norm_num at hl
    have hw : (1-s).re = 3/2 := by rw [sub_re,one_re,hl]; norm_num
    have hζ : ‖dedekindZeta K (1-s)‖ ≤ Z := (hB _ hw.ge).trans (le_max_left _ _)
    have he : entireReg K s = -(1-s)*dedekindZeta K (1-s) * (arch K (1-s)*(arch K s)⁻¹) := by
      rw [entireReg_eq_reg K hn, reg]
      change xi K s / s * _ = _
      rw [← xi_reflect K s, xi_agrees K (by rw [hw]; norm_num)]
      field_simp [hn]
      ring
    have hm : ‖1-s‖ = ‖s+2‖ := by
      rw [mirror hl, show conj s+2=conj (s+2) by rw [map_add,Complex.conj_ofNat],Complex.norm_conj]
    rw [he,norm_mul,norm_mul,norm_neg,hm]
    calc _ ≤ (‖s+2‖*Z)*(E*‖s+2‖^(Module.finrank ℚ K)) := mul_le_mul
               (mul_le_mul_of_nonneg_left hζ (norm_nonneg _)) (arch_ratio K hl)
               (norm_nonneg _) (mul_nonneg (norm_nonneg _) hZ)
         _ = (Z*E)*‖s+2‖^power K := by rw [pow_succ]; ring
         _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · have hn : s ≠ 0 := by rintro rfl; norm_num at hr
    have hζ : ‖dedekindZeta K s‖ ≤ Z := (hB _ hr.ge).trans (le_max_left _ _)
    have hm := shift_ge (s := s) (by rw [hr]; norm_num)
    have hu : ‖s-1‖ ≤ 4*‖s+2‖ := by
      have h := norm_sub_le (s+2) (3:ℂ)
      rw [show s+2-3=s-1 by ring, Complex.norm_ofNat] at h
      linarith
    have hp : ‖s+2‖ ≤ ‖s+2‖^power K := le_self_pow₀ hm (Nat.succ_ne_zero _)
    rw [entireReg_eq_reg K hn, reg_agrees K (by rw [hr]; norm_num), norm_mul]
    calc _ ≤ (4*‖s+2‖)*Z := mul_le_mul hu hζ (norm_nonneg _) (by positivity)
         _ = (4*Z)*‖s+2‖ := by ring
         _ ≤ _ := mul_le_mul (le_max_right _ _) hp (norm_nonneg _) hc

private theorem quotient_growth :
    ∃ A D : ℝ, 0 ≤ A ∧ 0 ≤ D ∧ ∀ s : ℂ, s.re ∈ Icc (-(1/2:ℝ)) (3/2) →
      1 ≤ |s.im| → ‖quotient K s‖ ≤ A * Real.exp (D*|s.im|) := by
  obtain ⟨X,hX,hxi⟩ := HighStrip.rapid_strip K 0
  obtain ⟨B,D,hB,hD,harch⟩ := ArchGrowth.reciprocal_arch_growth K
  refine ⟨X*B,D,mul_nonneg hX hB,hD,?_⟩
  intro s hs ht
  have hx : ‖xi K s‖ ≤ X := by simpa using hxi s ⟨by linarith [hs.1],by linarith [hs.2]⟩
  have hn : 1 ≤ ‖s‖ := ht.trans (abs_im_le_norm _)
  have hn' : s ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans_le hn)
  have hq : ‖quotient K s‖ ≤ ‖entireReg K s‖ := by
    rw [quotient,norm_div,norm_pow]
    exact div_le_self (norm_nonneg _) (one_le_pow₀ (shift_ge hs.1))
  apply hq.trans
  rw [entireReg_eq_reg K hn', reg, norm_mul, norm_div]
  calc _ ≤ X * (B*Real.exp (D*|s.im|)) := mul_le_mul
              ((div_le_self (norm_nonneg _) hn).trans hx) (harch s hs ht) (norm_nonneg _) hX
       _ = _ := by ring

/-- Degree d+1 controls the pole-removed function on -1/2 ≤ Re(s) ≤ 3/2. -/
theorem polynomial_strip :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ s : ℂ, s.re ∈ Icc (-(1/2:ℝ)) (3/2) →
      ‖entireReg K s‖ ≤ C*(4+|s.im|)^power K := by
  obtain ⟨B,hB,hE⟩ := strip_edges K
  let C := max B 1
  have hC : 1 ≤ C := le_max_right _ _
  refine ⟨C,hC,?_⟩
  have edge (z : ℂ) (hz : z.re = -(1/2:ℝ) ∨ z.re = 3/2) : ‖quotient K z‖ ≤ C := by
    have hr : -(1/2:ℝ) ≤ z.re := hz.elim (fun h => h.ge) (fun h => by rw [h]; norm_num)
    rw [quotient, norm_div, norm_pow, div_le_iff₀ (pow_pos (zero_lt_one.trans_le (shift_ge hr)) _)]
    exact (hE z hz).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hd : DiffContOnCl ℂ (quotient K) (re ⁻¹' Ioo (-(1/2:ℝ)) (3/2)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_preimage_re, closure_Ioo (by norm_num)]
    intro z hz
    exact ((entireReg_diff K z).div (((differentiableAt_id.add_const (2:ℂ)).pow _))
      (pow_ne_zero _ (norm_pos_iff.mp (zero_lt_one.trans_le (shift_ge hz.1))))).differentiableWithinAt
  obtain ⟨A,D,hA,hD,hgrow⟩ := quotient_growth K
  intro s hs
  have hq : ‖quotient K s‖ ≤ C := by
    apply PhragmenLindelof.vertical_strip hd _ (fun z h => edge z (.inl h))
      (fun z h => edge z (.inr h)) hs.1 hs.2
    refine ⟨1,by linarith [Real.pi_gt_three],D,isBigO_iff.mpr ⟨A,?_⟩⟩
    have he : ∀ᶠ z in comap (_root_.abs ∘ im) atTop, 1 ≤ |z.im| :=
      (eventually_ge_atTop (1:ℝ)).comap _
    filter_upwards [he.filter_mono inf_le_left,
      mem_inf_of_right (mem_principal_self (re ⁻¹' Ioo (-(1/2:ℝ)) (3/2)))] with z ht hz
    rw [Real.norm_eq_abs, Real.abs_exp, one_mul]
    apply (hgrow z ⟨hz.1.le,hz.2.le⟩ ht).trans
    apply mul_le_mul_of_nonneg_left _ hA
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp |z.im|]) hD
  rw [quotient,norm_div,norm_pow,div_le_iff₀ (pow_pos (zero_lt_one.trans_le (shift_ge hs.1)) _)] at hq
  apply hq.trans
  apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hC)
  apply pow_le_pow_left₀ (norm_nonneg _)
  apply (norm_le_abs_re_add_abs_im (s+2)).trans
  simp only [add_re,re_ofNat,add_im,im_ofNat,add_zero]
  apply add_le_add_left
  exact abs_le.mpr ⟨by linarith [hs.1],by linarith [hs.2]⟩

#print axioms strip_edges
#print axioms polynomial_strip
end OMA.ZetaGrowth
