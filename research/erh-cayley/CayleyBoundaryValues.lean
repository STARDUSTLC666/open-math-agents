import CayleyReturn
import CayleyDifference

/-! The linear normalization has a finite radial limit and unbounded tangential
values at the same boundary point. This obstructs absolute summability of the
first differences of the forward coefficients for every number field. -/
noncomputable section
namespace OMA.CayleyBoundaryValues
open Complex Filter Set Metric NumberField CayleyBounds CayleyDifference CayleyReturn
open scoped Topology

def coordinate (s : ℂ) := (s-2)/(s+1/16)

private theorem coord_formula {s : ℂ} (hs : 1 < s.re) :
    coordinate s = 1-(33/16)*(s+1/16)⁻¹ := by
  have hd : s+1/16 ≠ 0 := ne_zero_of_re_pos (by norm_num; linarith)
  unfold coordinate
  rw [div_eq_mul_inv,show s-2 = (s+1/16)-(33/16) by ring,sub_mul,mul_inv_cancel₀ hd]

private theorem coord_disk {s : ℂ} (hs : 1 < s.re) :
    ‖coordinate s‖ < 1 ∧ point (coordinate s) = s :=
  R_ERH_extended_riemann_hypothesis_R3_H2_R1_H2_R1.inverse_coordinate (by linarith)

theorem normalized_at (K : Type*) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    normalized K (coordinate s) =
      (33/16)*(1-(17/16)*(s+1/16)⁻¹)*dedekindZeta K s := by
  have hd : s+1/16 ≠ 0 := ne_zero_of_re_pos (by norm_num; linarith)
  rw [normalized,forward,(coord_disk hs).2,(CayleyFields.boundary K).1 _ hs,coord_formula hs]
  calc _ = (33/16)*(((s+1/16)-(17/16))*(s+1/16)⁻¹)*dedekindZeta K s := by ring
       _ = _ := by rw [sub_mul,mul_inv_cancel₀ hd]

private theorem limit_factors {α : Type*} {l : Filter α} {s : α → ℂ}
    (hpos : ∀ᶠ n in l, 1 < (s n).re) (hnorm : Tendsto (fun n => ‖s n+1/16‖) l atTop) :
    Tendsto (fun n => coordinate (s n)) l (𝓝 1) ∧
    Tendsto (fun n => (33/16:ℂ)*(1-(17/16)*(s n+1/16)⁻¹)) l (𝓝 (33/16)) := by
  have hinv : Tendsto (fun n => (s n+1/16)⁻¹) l (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [norm_inv,Function.comp_def] using tendsto_inv_atTop_zero.comp hnorm
  constructor
  · apply Tendsto.congr' (f₁ := fun n => 1-(33/16)*(s n+1/16)⁻¹)
    · exact hpos.mono fun n hn => (coord_formula hn).symm
    · simpa using (hinv.const_mul (33/16:ℂ)).const_sub 1
  · simpa using ((hinv.const_mul (17/16:ℂ)).const_sub 1).const_mul (33/16:ℂ)

theorem radial_limit (K : Type*) [Field K] [NumberField K] :
    Tendsto (fun x : ℝ => coordinate (x:ℂ)) atTop (𝓝 1) ∧
    Tendsto (fun x : ℝ => normalized K (coordinate (x:ℂ))) atTop (𝓝 (33/16)) := by
  have hx : ∀ᶠ x : ℝ in atTop, 1 < (x:ℂ).re := eventually_gt_atTop 1
  have hn : Tendsto (fun x : ℝ => ‖(x:ℂ)+1/16‖) atTop atTop := by
    apply tendsto_atTop_mono _ (tendsto_id : Tendsto id atTop (atTop : Filter ℝ))
    intro x
    have hh := re_le_norm ((x:ℂ)+1/16)
    norm_num at hh
    change x ≤ _
    linarith
  obtain ⟨hw,hf⟩ := limit_factors hx hn
  refine ⟨hw,Tendsto.congr' (hx.mono (fun x h => (normalized_at K h).symm)) ?_⟩
  simpa only [mul_one] using hf.mul (real_limit K)

theorem vertical_limits :
    ∃ u : ℕ → ℕ, StrictMono u ∧ ∀ (K : Type) [Field K] [NumberField K] (x : ℝ), 1 < x →
      (∀ n, ‖coordinate (shift x (u n))‖ < 1) ∧
      Tendsto (fun n => coordinate (shift x (u n))) atTop (𝓝 1) ∧
      Tendsto (fun n => normalized K (coordinate (shift x (u n)))) atTop (𝓝 ((33/16)*dedekindZeta K (x:ℂ))) := by
  obtain ⟨u,hu,hz⟩ := common_heights
  refine ⟨u,hu,?_⟩
  intro K _ _ x hx
  have hp (n : ℕ) : 1 < (shift x (u n)).re := by simpa [shift] using hx
  have hn : Tendsto (fun n => ‖shift x (u n)+1/16‖) atTop atTop := by
    apply tendsto_atTop_mono _ (tendsto_natCast_atTop_atTop (R := ℝ) |>.comp hu.tendsto_atTop)
    intro n
    have hi := im_le_norm (shift x (u n)+1/16)
    simpa [shift,Function.comp_def] using hi
  obtain ⟨hw,hf⟩ := limit_factors (Eventually.of_forall hp) hn
  refine ⟨fun n => (coord_disk (hp n)).1,hw,?_⟩
  exact (hf.mul (hz K x hx)).congr fun n => (normalized_at K (hp n)).symm

theorem unbounded_at_one (K : Type) [Field K] [NumberField K] (A ε : ℝ) (hε : 0 < ε) :
    ∃ w : ℂ, ‖w‖ < 1 ∧ ‖w-1‖ < ε ∧ A < ‖normalized K w‖ := by
  obtain ⟨x,hx,hlarge⟩ := large_real K (max A 0 + 1)
  obtain ⟨u,_,hall⟩ := vertical_limits
  obtain ⟨hdisk,hcoord,hval⟩ := hall K x hx
  have hM : A < ‖(33/16:ℂ)*dedekindZeta K (x:ℂ)‖ := by
    rw [norm_mul]
    norm_num
    linarith [le_max_left A 0, norm_nonneg (dedekindZeta K (x:ℂ))]
  have hclose : ∀ᶠ n in atTop, coordinate (shift x (u n)) ∈ ball (1:ℂ) ε :=
    hcoord (ball_mem_nhds (1:ℂ) hε)
  obtain ⟨n,h1,h2⟩ := (hclose.and (hval.norm.eventually_const_lt hM)).exists
  exact ⟨_,hdisk n,mem_ball_iff_norm.mp h1,h2⟩

theorem absolute_mass (K : Type) [Field K] [NumberField K] (A : ℝ) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∃ N : ℕ, A < ∑ n ∈ Finset.range N, ‖c K n‖*r^n := by
  obtain ⟨w,hw,hclose,hlarge⟩ := unbounded_at_one K A (1/2) (by norm_num)
  have hne : w ≠ 0 := by rintro rfl; norm_num at hclose
  refine ⟨‖w‖,norm_pos_iff.mpr hne,hw,?_⟩
  by_contra! h
  apply hlarge.not_ge
  apply le_of_tendsto (normalized_sum K hw).tendsto_sum_nat.norm
  apply Eventually.of_forall
  intro N
  have hl := norm_sum_le (Finset.range N) (fun n => c K n*w^n)
  exact hl.trans (by simpa only [norm_mul,norm_pow] using h N)

theorem difference_prefix_violation (K : Type) [Field K] [NumberField K] :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∃ n : ℕ,
      ‖c K 0‖ < ∑ j ∈ Finset.range (n+1), ‖c K (j+1)‖*r^(j+1) := by
  obtain ⟨r,hr,h1,N,h⟩ := absolute_mass K (2*‖c K 0‖)
  refine ⟨r,hr,h1,?_⟩
  cases N with
  | zero => simp at h; linarith [norm_nonneg (c K 0)]
  | succ n =>
    rw [Finset.sum_range_succ'] at h
    simp only [pow_zero,mul_one] at h
    cases n with
    | zero => simp at h; linarith [norm_nonneg (c K 0)]
    | succ n => exact ⟨n,by linarith⟩

theorem not_absolutely_summable (K : Type) [Field K] [NumberField K] :
    ¬ Summable fun n => ‖c K n‖ := by
  intro hs
  obtain ⟨r,hr,h1,N,h⟩ := absolute_mass K (∑' n, ‖c K n‖)
  apply h.not_ge
  calc _ ≤ ∑ n ∈ Finset.range N, ‖c K n‖ := by
         apply Finset.sum_le_sum
         intro n _
         exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ hr.le h1.le)
       _ ≤ _ := hs.sum_le_tsum _ (fun n _ => norm_nonneg _)

#print axioms normalized_at
#print axioms radial_limit
#print axioms vertical_limits
#print axioms unbounded_at_one
#print axioms absolute_mass
#print axioms difference_prefix_violation
#print axioms not_absolutely_summable
end OMA.CayleyBoundaryValues
