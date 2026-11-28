import OMAReductions.R_ERH_extended_riemann_hypothesis_R3_H2_R2

/-! Closed rectangles and Taylor grids of an entire function. Both boundary coordinates
are rounded up inside the original box. The estimate is uniform in the real cutoff q. -/
noncomputable section
namespace OMA.RectangleTest
open Complex Metric Set Filter
open scoped Topology
variable (F : ℂ → ℂ)

def poly (n : ℕ) (z : ℂ) :=
  ∑ k ∈ Finset.range (n+1), (k.factorial:ℂ)⁻¹ * iteratedDeriv k F 2*(z-2)^k

def rectangle (q B H : ℝ) := {z : ℂ | q ≤ z.re ∧ |z.re| ≤ B ∧ |z.im| ≤ H}

def passes (q B H : ℝ) (n : ℕ) : Prop := ∀ j k : ℤ,
  let D := ((2:ℝ)^n)^2
  let x := (j:ℝ)/D
  let y := (k:ℝ)/D
  q ≤ x → |x| ≤ B → |y| ≤ H → ((2:ℝ)^n)⁻¹ ≤ ‖poly F n ((x:ℂ)+(y:ℂ)*I)‖

theorem rectangle_compact (q B H : ℝ) : IsCompact (rectangle q B H) := by
  apply (isCompact_closedBall (0:ℂ) (B+H)).of_isClosed_subset
  · exact (isClosed_le continuous_const Complex.continuous_re).inter
      ((isClosed_le Complex.continuous_re.abs continuous_const).inter
        (isClosed_le Complex.continuous_im.abs continuous_const))
  · intro z hz
    apply mem_closedBall_zero_iff.mpr
    exact (norm_le_abs_re_add_abs_im z).trans (add_le_add hz.2.1 hz.2.2)

theorem eventual_compact (hF : Differentiable ℂ F) {S : Set ℂ} (hs : IsCompact S)
    (hn : ∀ z ∈ S, F z ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ z ∈ S, c ≤ ‖poly F n z‖ := by
  obtain ⟨R0, hR0⟩ := hs.bddAbove_image continuous_norm.continuousOn
  let R := max R0 1
  have hR (z : ℂ) (hz : z ∈ S) : ‖z‖ ≤ R := (hR0 (mem_image_of_mem _ hz)).trans (le_max_left _ _)
  have hc : ContinuousOn (fun z => (F z)⁻¹) S := hF.continuous.continuousOn.inv₀ hn
  obtain ⟨B0,hB0⟩ := hs.bddAbove_image hc.norm
  let B := max B0 1
  have hB : 0 < B := zero_lt_one.trans_le (le_max_right _ _)
  have hlow (z : ℂ) (hz : z ∈ S) : B⁻¹ ≤ ‖F z‖ := by
    have h : ‖(F z)⁻¹‖ ≤ B := (hB0 (mem_image_of_mem _ hz)).trans (le_max_left _ _)
    rw [norm_inv,inv_eq_one_div,div_le_iff₀ (norm_pos_iff.mpr (hn z hz))] at h
    rwa [inv_eq_one_div,div_le_iff₀ hB,mul_comm]
  obtain ⟨C,hC,hest⟩ := R_ERH_extended_riemann_hypothesis_R3_H2_R2.section_estimate
    F hF R (le_max_right _ _)
  let c := B⁻¹/2
  have hcpos : 0 < c := half_pos (inv_pos.mpr hB)
  have hpow := tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)
  have hinv := tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (by decide : (2:ℕ)≠0)).comp hpow)
  have hlim : Tendsto (fun n : ℕ => C*(((2:ℝ)^n)^2)⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def,mul_zero] using hinv.const_mul C
  refine ⟨c,hcpos,?_⟩
  filter_upwards [hlim.eventually_le_const hcpos] with n hn'
  intro z hz
  have he : ‖F z-poly F n z‖ ≤ C*(((2:ℝ)^n)^2)⁻¹ := by
    simpa only [poly,sub_self,norm_zero,zero_add] using hest n z z (hR z hz) (hR z hz)
  have htri := norm_add_le (F z-poly F n z) (poly F n z)
  rw [sub_add_cancel] at htri
  dsimp only [c] at hn' ⊢
  linarith [hlow z hz]

theorem eventual_grid (hF : Differentiable ℂ F) {q B H : ℝ} (hn : ∀ z ∈ rectangle q B H, F z ≠ 0) :
    ∀ᶠ n : ℕ in atTop, passes F q B H n := by
  obtain ⟨c,hc,hpoly⟩ := eventual_compact F hF (rectangle_compact q B H) hn
  have hlim : Tendsto (fun n : ℕ => ((2:ℝ)^n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have hmem (x y : ℝ) (hx : q ≤ x) (hb : |x| ≤ B) (hh : |y| ≤ H) :
      (x:ℂ)+(y:ℂ)*I ∈ rectangle q B H := by
    simpa [rectangle] using And.intro hx (And.intro hb hh)
  filter_upwards [hlim.eventually_le_const hc,hpoly] with n hlo hp
  intro j k
  dsimp only
  intro hq hB hH
  exact hlo.trans (hp _ (hmem _ _ hq hB hH))

private theorem round_coordinate (T n : ℕ) {x : ℝ} (hx : |x| ≤ T) :
    ∃ j : ℤ, let D := ((2:ℝ)^n)^2
             let u := (j:ℝ)/D
             x ≤ u ∧ u ≤ x+D⁻¹ ∧ |u| ≤ T := by
  let D := ((2:ℝ)^n)^2
  have hD : 0 < D := by positivity
  let j := ⌈x*D⌉
  obtain ⟨hlo,hhi⟩ := R_ERH_extended_riemann_hypothesis_R3_H2_R2.grid_round_up x hD
  have hcap : j ≤ (T:ℤ)*(((2:ℤ)^n)^2) := by
    apply Int.ceil_le.mpr
    push_cast
    exact mul_le_mul_of_nonneg_right (abs_le.mp hx).2 hD.le
  have hreal : (j:ℝ) ≤ (T:ℝ)*(((2:ℝ)^n)^2) := by exact_mod_cast hcap
  exact ⟨j,hlo,hhi,abs_le.mpr ⟨(abs_le.mp hx).1.trans hlo,(div_le_iff₀ hD).mpr hreal⟩⟩

theorem uniform_grid_bound (hF : Differentiable ℂ F) (B H : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℝ) (n : ℕ),
    passes F q B H n → ∀ z ∈ rectangle q B H,
      ((2:ℝ)^n)⁻¹ - C*(((2:ℝ)^n)^2)⁻¹ ≤ ‖F z‖ := by
  let R : ℝ := B+H+1
  have hR : 1 ≤ R := by
    dsimp [R]
    linarith [Nat.cast_nonneg (α := ℝ) B, Nat.cast_nonneg (α := ℝ) H]
  obtain ⟨A,hA,herr⟩ := R_ERH_extended_riemann_hypothesis_R3_H2_R2.section_estimate
    F hF R hR
  refine ⟨3*A,by positivity,?_⟩
  intro q n hgrid z hz
  let D := ((2:ℝ)^n)^2
  obtain ⟨j,hx0,hx1,hxB⟩ := round_coordinate B n hz.2.1
  obtain ⟨k,hy0,hy1,hyH⟩ := round_coordinate H n hz.2.2
  let x := (j:ℝ)/D
  let y := (k:ℝ)/D
  let w : ℂ := (x:ℂ)+(y:ℂ)*I
  have hwr : w.re = x := by simp [w]
  have hwi : w.im = y := by simp [w]
  have hgridw : ((2:ℝ)^n)⁻¹ ≤ ‖poly F n w‖ :=
    hgrid j k (hz.1.trans hx0) hxB hyH
  have hwR : ‖w‖ ≤ R := by
    apply (norm_le_abs_re_add_abs_im w).trans
    rw [hwr,hwi]
    exact (add_le_add hxB hyH).trans (le_add_of_nonneg_right zero_le_one)
  have hzR : ‖z‖ ≤ R := (norm_le_abs_re_add_abs_im z).trans
    ((add_le_add hz.2.1 hz.2.2).trans (le_add_of_nonneg_right zero_le_one))
  have hdist : ‖z-w‖ ≤ 2*D⁻¹ := by
    apply (norm_le_abs_re_add_abs_im _).trans
    rw [sub_re,sub_im,hwr,hwi,abs_of_nonpos (sub_nonpos.mpr hx0),abs_of_nonpos (sub_nonpos.mpr hy0)]
    change x ≤ z.re+D⁻¹ at hx1
    change y ≤ z.im+D⁻¹ at hy1
    linarith
  have he : ‖F z-poly F n w‖ ≤ A*(‖z-w‖+D⁻¹) := by
    simpa only [poly] using herr n z w hzR hwR
  have hdiff : ‖F z-poly F n w‖ ≤ (3*A)*D⁻¹ := calc
    _ ≤ A*(‖z-w‖+D⁻¹) := he
    _ ≤ A*(2*D⁻¹+D⁻¹) := mul_le_mul_of_nonneg_left (add_le_add hdist le_rfl) hA
    _ = _ := by ring
  have htri := norm_add_le (poly F n w-F z) (F z)
  rw [sub_add_cancel,norm_sub_rev] at htri
  change ((2:ℝ)^n)⁻¹-(3*A)*D⁻¹ ≤ _
  linarith only [hgridw,htri,hdiff]

theorem eventually_iff_zero_free (hF : Differentiable ℂ F) (q : ℝ) (B H : ℕ) :
    ∀ᶠ n : ℕ in atTop, passes F q B H n ↔ ∀ z ∈ rectangle q B H, F z ≠ 0 := by
  by_cases hf : ∀ z ∈ rectangle q B H, F z ≠ 0
  · filter_upwards [eventual_grid F hF hf] with n hn
    exact iff_of_true hn hf
  obtain ⟨C,_,hbound⟩ := uniform_grid_bound F hF B H
  have ht := tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)
  filter_upwards [ht.eventually_gt_atTop C] with n hn
  refine ⟨fun hp z hz he => ?_,fun h => (hf h).elim⟩
  have h := hbound q n hp z hz
  rw [he,norm_zero] at h
  let d := (2:ℝ)^n
  have hd : 0 < d := by positivity
  have hle : d⁻¹ ≤ C/(d^2) := by
    simpa only [div_eq_mul_inv] using sub_nonpos.mp h
  have hC := (le_div_iff₀ (sq_pos_of_pos hd)).mp hle
  rw [pow_two,inv_mul_cancel_left₀ hd.ne'] at hC
  exact hn.not_ge hC

#print axioms eventual_compact
#print axioms eventual_grid
#print axioms uniform_grid_bound
#print axioms eventually_iff_zero_free
end OMA.RectangleTest
