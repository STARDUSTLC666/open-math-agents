import CyclotomicDisks

/-! The trivial zeros on the left and the distance to the first such zero.
At zero the divided difference in the entire regularization needs a separate
limit: for imaginary quadratic fields its value is C/2. -/
noncomputable section
namespace OMA.CentralRadius
open Complex NumberField NumberField.InfinitePlace Filter Set Metric
open ExactRadius ThetaContinuation
open scoped Topology
variable (K : Type*) [Field K] [NumberField K]

private def numerator (z : ℂ) := z*(z-1)*(pair K).Λ₀ z + cst K

private theorem numerator_reflect (z : ℂ) : numerator K (1-z) = numerator K z := by
  have hsym : (pair K).symm = pair K := by unfold WeakFEPair.symm pair; congr 1; simp
  have h := (pair K).functional_equation₀ z
  rw [hsym] at h
  change (pair K).Λ₀ (1-z) = (1:ℂ) • (pair K).Λ₀ z at h
  rw [one_smul] at h
  rw [numerator, numerator, h]; ring

/-- Away from zero, the archimedean factor detects all left-half-plane
zeros, for every number field. -/
theorem left_zero_iff_arch {z : ℂ} (hne : z ≠ 0) (hle : z.re ≤ 0) :
    z ∈ zeros K ↔ arch K z = 0 := by
  have hright : 1 ≤ (1-z).re := by rw [sub_re, one_re]; linarith
  have hnum : numerator K z ≠ 0 := by
    intro h
    have href := (numerator_reflect K z).trans h
    apply AllFieldRadius.nonzero_on_closed_halfplane K hright
    change (numerator K (1-z)/(1-z))*(arch K (1-z))⁻¹ = 0
    rw [href, zero_div, zero_mul]
  change entireReg K z = 0 ↔ _
  rw [entireReg_eq_reg K hne]
  change (numerator K z/z)*(arch K z)⁻¹ = 0 ↔ _
  simp [div_ne_zero hnum hne]

private theorem arch_limit (hr : nrRealPlaces K = 0) (hc : nrComplexPlaces K = 1) :
    Tendsto (fun z : ℂ => z*arch K z) (𝓝[≠] 0) (𝓝 2) := by
  let f := fun z : ℂ => exp (z * (Real.log (discr K).natAbs / 2 : ℝ)) *
    (2 * (2 * (Real.pi:ℂ)) ^ (-z))
  have hπ : (2*(Real.pi:ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hcont : ContinuousAt f 0 := by
    dsimp [f]
    exact (by fun_prop : ContinuousAt (fun z : ℂ => exp (z * (Real.log (discr K).natAbs / 2 : ℝ))) 0).mul
      (continuousAt_const.mul ((continuousAt_const_cpow hπ).comp continuousAt_neg))
  have hlim := (hcont.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0:ℂ) ≤ 𝓝 0)).mul
    tendsto_self_mul_Gamma_nhds_zero
  have hzero : f 0 = 2 := by simp [f]
  rw [hzero, mul_one] at hlim
  apply hlim.congr'
  exact Eventually.of_forall (fun z => by dsimp [f, arch]; rw [hr, hc, pow_zero, pow_one, Gammaℂ_def]; ring)

theorem value_at_zero (hr : nrRealPlaces K = 0) (hc : nrComplexPlaces K = 1) :
    entireReg K 0 = cst K / 2 := by
  have hnum : ContinuousAt (numerator K) 0 :=
    ((((continuousAt_id.mul (continuousAt_id.sub continuousAt_const)).mul
      ((pair K).differentiable_Λ₀ 0).continuousAt)).add continuousAt_const)
  have hn := hnum.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0:ℂ) ≤ 𝓝 0)
  have hf := hn.div (arch_limit K hr hc) (by norm_num : (2:ℂ) ≠ 0)
  have hcst : numerator K 0 = cst K := by simp [numerator]
  rw [hcst] at hf
  have hreg := ((entireReg_diff K 0).continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[≠] (0:ℂ) ≤ 𝓝 0))
  apply tendsto_nhds_unique hreg
  apply hf.congr'
  filter_upwards [self_mem_nhdsWithin (s := ({0}ᶜ : Set ℂ))] with z hz
  have hne : z ≠ 0 := hz
  change (z*(z-1)*(pair K).Λ₀ z+cst K)/(z*arch K z) = entireReg K z
  rw [entireReg_eq_reg K hne, reg]
  simp only [div_eq_mul_inv, mul_inv]
  ring

private theorem gammaC_zero {z : ℂ} : Gammaℂ z = 0 ↔ ∃ n : ℕ, z = -(n:ℂ) := by
  simp [Gammaℂ_def, Complex.Gamma_eq_zero_iff, Real.pi_ne_zero]

theorem left_zero_cases (hr : nrRealPlaces K = 0) (hc : nrComplexPlaces K = 1)
    {z : ℂ} (hle : z.re ≤ 0) :
    z ∈ zeros K ↔ ∃ n : ℕ, z = -((n:ℂ)+1) := by
  by_cases hz : z = 0
  · subst z
    have hn : entireReg K 0 ≠ 0 := by rw [value_at_zero K hr hc]; exact div_ne_zero (cst_ne K) two_ne_zero
    constructor
    · exact fun h => (hn h).elim
    · rintro ⟨n,he⟩
      have ha := congrArg Complex.re he
      simp at ha
      linarith [Nat.cast_nonneg (α := ℝ) n]
  rw [left_zero_iff_arch K hz hle, arch, hr, hc, pow_zero, mul_one, pow_one,
    mul_eq_zero, or_iff_right (exp_ne_zero _), gammaC_zero]
  constructor
  · rintro ⟨n,he⟩
    cases n with
    | zero => simp at he; exact (hz he).elim
    | succ n => exact ⟨n, by simpa using he⟩
  · rintro ⟨n,rfl⟩
    exact ⟨n+1, by push_cast; rfl⟩

private theorem real_dist_sq (t x : ℝ) :
    dist (center t) (x:ℂ)^2 = (2-x)^2 + t^2 := by
  rw [dist_eq_norm, Complex.sq_norm, normSq_apply]
  simp [ExactRadius.center, sq]

/-- If the critical-strip zeros are high enough, -1 is a nearest zero. -/
theorem exact_from_height (hr : nrRealPlaces K = 0) (hc : nrComplexPlaces K = 1)
    {T t : ℝ} (hzeros : ∀ z ∈ zeros K, 0 < z.re → T < |z.im|)
    (ht : |t| ≤ T) (hgap : 9+t^2 ≤ 1+(T-|t|)^2) :
    zeroDistance K t = Real.sqrt (9+t^2) := by
  have hfirst : (-1:ℂ) ∈ zeros K := (left_zero_cases K hr hc (by norm_num)).mpr ⟨0, by norm_num⟩
  have hfirstDist : dist (center t) (-1) = Real.sqrt (9+t^2) := by
    have he := real_dist_sq t (-1)
    norm_num at he
    rw [← he, Real.sqrt_sq dist_nonneg]
  rw [← hfirstDist]
  refine le_antisymm (infDist_le_dist_of_mem hfirst) ?_
  obtain ⟨z,hz,he⟩ := nearest K t
  rw [he]
  apply (sq_le_sq₀ dist_nonneg dist_nonneg).mp
  have hfirstSq := real_dist_sq t (-1)
  norm_num at hfirstSq
  rw [hfirstSq]
  rcases le_or_gt z.re 0 with h | h
  · obtain ⟨n,rfl⟩ := (left_zero_cases K hr hc h).mp hz
    have hsq := real_dist_sq t (-((n:ℝ)+1))
    push_cast at hsq
    rw [hsq]
    nlinarith [Nat.cast_nonneg (α := ℝ) n, sq_nonneg (n:ℝ)]
  · have hhor : 1 < 2-z.re := by linarith [zeros_left K hz]
    have hvert : T-|t| ≤ |t-z.im| := by
      have htri : |z.im| ≤ |t|+|t-z.im| := by
        simpa only [add_sub_cancel, abs_sub_comm z.im t] using abs_add_le t (z.im-t)
      linarith [hzeros z hz h]
    have hvsq := (sq_le_sq₀ (sub_nonneg.mpr ht) (abs_nonneg _)).mpr hvert
    rw [sq_abs] at hvsq
    have hhsq := (sq_le_sq₀ zero_le_one (zero_le_one.trans hhor.le)).mpr hhor.le
    have hs : dist (center t) z ^ 2 = (2-z.re)^2 + (t-z.im)^2 := by
      rw [dist_eq_norm, Complex.sq_norm, normSq_apply, sq, sq]; rfl
    rw [hs]; linarith

theorem eisenstein_exact {t : ℝ} (ht : |t| ≤ 1/3) :
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ, p.radius = ENNReal.ofReal (Real.sqrt (9+t^2)) ∧
      ReciprocalRadius.InverseGerm (CyclotomicField 3 ℚ) t p := by
  let F := CyclotomicField 3 ℚ
  obtain ⟨hr,hc,hd⟩ := CyclotomicDisks.eisenstein_invariants
  have hrate : 18/5 ≤ HeatDecay.rate F := by
    change 18/5 ≤ 2*Real.pi / Real.sqrt (((discr (CyclotomicField 3 ℚ)).natAbs:ℕ):ℝ)
    rw [hd]
    change 18/5 ≤ 2*Real.pi / Real.sqrt 3
    rw [le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num))]
    have hroot : Real.sqrt 3 ≤ 26/15 := by
      apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp
      rw [Real.sq_sqrt (by norm_num)]; norm_num
    linarith [Real.pi_gt_d2]
  have hzeros (z : ℂ) (hz : z ∈ zeros F) (hz0 : 0 < z.re) : 13/4 < |z.im| := by
    have hprod : (18/5-1)*(18/5+1/2) ≤ (HeatDecay.rate F-1)*(HeatDecay.rate F+1/2) :=
      mul_le_mul (by linarith) (by linarith) (by norm_num) (by linarith)
    have hH := StripHeat.zero_height_rate F hr hc hz hz0
    apply (sq_lt_sq₀ (by norm_num) (abs_nonneg _)).mp
    rw [sq_abs]; linarith
  have hgap : 9+t^2 ≤ 1+(13/4-|t|)^2 := by nlinarith [sq_abs t]
  have hdist := exact_from_height F hr hc hzeros (t := t) (by linarith) hgap
  obtain ⟨p,hp,hg⟩ := AllFieldRadius.all_fields_radius_gt_one F t
  exact ⟨p, (radius_eq_zeroDistance F t (zero_lt_one.trans hp) hg).trans (congrArg ENNReal.ofReal hdist), hg⟩

#print axioms left_zero_iff_arch
#print axioms value_at_zero
#print axioms left_zero_cases
#print axioms exact_from_height
#print axioms eisenstein_exact
end OMA.CentralRadius
