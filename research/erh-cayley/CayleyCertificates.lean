import CayleyCritical

/-! Grid denominators fixed in advance. For a zero-free closed disk every
sufficiently late test passes with this choice. -/
noncomputable section
namespace OMA.CayleyCertificates
open Complex Set Filter Metric NumberField ExactRadius CayleyHigher CayleySections CayleyFiniteGrid CayleyCritical
open scoped Topology

def length (n : ℕ) := (n+1)^2+2
def mesh (n : ℕ) := length n*(n+1)
def passesAt (K : Type*) [Field K] [NumberField K] (r : ℝ) (n : ℕ) :=
  passes (a K) r (1/((n:ℝ)+1)) (length n) (mesh n)

private theorem length_pos (n : ℕ) : 0 < length n := by unfold length; omega
private theorem mesh_pos (n : ℕ) : 0 < mesh n := Nat.mul_pos (length_pos n) (Nat.succ_pos n)

private theorem square_margin {M : ℝ} {n : ℕ} (hn : M ≤ (n:ℝ)) :
    M/((((n+1)^2 : ℕ):ℝ)+1) ≤ 1/((n:ℝ)+1) := by
  push_cast
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h := mul_le_mul_of_nonneg_right hn (show 0 ≤ (n:ℝ)+1 by positivity)
  nlinarith only [h,Nat.cast_nonneg (α := ℝ) n]

variable (K : Type*) [Field K] [NumberField K]

theorem slope_le (l : ℕ) : slope (a K) l ≤ (∑' j, ‖a K j‖)*(l:ℝ) := by
  have h := (critical_summable K).sum_le_tsum (Finset.range l) (fun _ _ => norm_nonneg _)
  unfold CayleyFiniteGrid.slope
  calc _ ≤ ∑ j ∈ Finset.range l, ‖a K j‖*(l:ℝ) := by
           apply Finset.sum_le_sum
           intro j hj
           exact mul_le_mul_of_nonneg_left (by exact_mod_cast (Finset.mem_range.mp hj).le) (norm_nonneg _)
       _ = (∑ j ∈ Finset.range l, ‖a K j‖)*(l:ℝ) := (Finset.sum_mul ..).symm
       _ ≤ _ := mul_le_mul_of_nonneg_right h (by positivity)

private theorem H_cont : ContinuousOn (H K) (ball 0 1) := by
  intro w hw
  have hpoint := CayleyDifference.point_analytic (mem_ball_zero_iff.mp hw)
  have haff : AnalyticAt ℂ affine (CayleyBounds.point w) :=
    ((analyticAt_const.mul analyticAt_id).sub analyticAt_const).div_const
  have hW := (entireReg_diff K).continuous.continuousAt (x := criticalPoint w)
  exact (((continuousAt_const.sub continuousAt_id).pow _).mul
    (hW.comp (haff.comp hpoint).continuousAt)).continuousWithinAt

private theorem H_ne {w : ℂ} (hw : ‖w‖ < 1) :
    H K w ≠ 0 ↔ entireReg K (criticalPoint w) ≠ 0 := by
  have hn : 1-w ≠ 0 := sub_ne_zero.mpr (fun e => by rw [← e,norm_one] at hw; exact lt_irrefl _ hw)
  simp [H,CayleySmoothing.damp,W,criticalPoint,hn]

theorem eventually_passes_iff {r : ℝ} (hr : 0 ≤ r) (h1 : r < 1) :
    (∀ᶠ n : ℕ in atTop, passesAt K r n) ↔
      ∀ w : ℂ, ‖w‖ ≤ r → entireReg K (criticalPoint w) ≠ 0 := by
  constructor
  · intro h w hw
    obtain ⟨L,hL⟩ := exists_nat_gt (major K)
    obtain ⟨n,hn,ht⟩ := (h.and (eventually_ge_atTop L)).exists
    have hp := (finite_lower_test (a K) hr h1.le (1/((n:ℝ)+1)) (length n)).mpr
      ⟨mesh n,mesh_pos n,hn⟩ w hw
    apply (H_ne K (hw.trans_lt h1)).mp
    intro hz
    have e := critical_tail K ((n+1)^2) (hw.trans_lt h1)
    rw [hz,zero_sub,norm_neg] at e
    exact hp.not_ge (e.trans (square_margin (hL.le.trans (by exact_mod_cast ht))))
  · intro h
    have hc := ((H_cont K).mono (closedBall_subset_ball h1)).norm
    obtain ⟨v,hv,hmin⟩ := (isCompact_closedBall (0:ℂ) r).exists_isMinOn
      ⟨0,mem_closedBall_self hr⟩ hc
    have hv' := mem_closedBall_zero_iff.mp hv
    have hv0 : 0 < ‖H K v‖ := norm_pos_iff.mpr ((H_ne K (hv'.trans_lt h1)).mpr (h v hv'))
    let S := ∑' j, ‖a K j‖
    obtain ⟨L,hL⟩ := exists_nat_gt (max (major K) ((2+2*S)/‖H K v‖))
    filter_upwards [eventually_ge_atTop L] with n hn
    have hn' : (L:ℝ) ≤ n := by exact_mod_cast hn
    have hM := (le_max_left _ _).trans (hL.le.trans hn')
    have hmargin : (2+2*S)/((n:ℝ)+1) < ‖H K v‖ := by
      have hbig := (div_lt_iff₀ hv0).mp (((le_max_right _ _).trans_lt hL).trans_le hn')
      apply (div_lt_iff₀ (by positivity)).mpr
      nlinarith only [hbig,hv0]
    intro j _ k _ hw
    let u := node (mesh n) j k
    have he : ‖H K u-taylorPoly (a K) (length n) u‖ ≤ 1/((n:ℝ)+1) :=
      (critical_tail K ((n+1)^2) (hw.trans_lt h1)).trans (square_margin hM)
    have htri := norm_add_le (H K u-taylorPoly (a K) (length n) u) (taylorPoly (a K) (length n) u)
    rw [sub_add_cancel] at htri
    have hmin' : ‖H K v‖ ≤ ‖H K u‖ := isMinOn_iff.mp hmin _ (mem_closedBall_zero_iff.mpr hw)
    have hmesh : 2*slope (a K) (length n)/(mesh n:ℝ) ≤ 2*S/((n:ℝ)+1) := by
      have hl : 0 < (length n:ℝ) := by exact_mod_cast length_pos n
      have hn0 : 0 < (n:ℝ)+1 := by positivity
      rw [mesh,Nat.cast_mul,Nat.cast_add,Nat.cast_one,div_le_div_iff₀ (mul_pos hl hn0) hn0]
      have hsl : slope (a K) (length n) ≤ S*(length n:ℝ) := slope_le K _
      nlinarith only [mul_le_mul_of_nonneg_right hsl hn0.le]
    change 1/((n:ℝ)+1)+2*slope (a K) (length n)/(mesh n:ℝ) < ‖taylorPoly (a K) (length n) u‖
    rw [add_div,show 2/((n:ℝ)+1) = 1/((n:ℝ)+1)+1/((n:ℝ)+1) by ring] at hmargin
    linarith only [hmin',he,htri,hmesh,hmargin]

theorem fixed_mesh_iff_erh :
    (∀ (L : Type) [Field L] [NumberField L] (m : ℕ), ∀ᶠ n : ℕ in atTop, passesAt L (subradius m) n) ↔
      ∀ (L : Type) [Field L] [NumberField L], ERH.ExtendedRiemannHypothesis L := by
  rw [← tests_iff_erh]
  have hr (m : ℕ) : 0 ≤ subradius m ∧ subradius m < 1 := by
    dsimp [subradius]
    exact ⟨by positivity,(div_lt_one (by positivity)).mpr (by linarith)⟩
  constructor
  · intro h L _ _ m
    exact (grid_iff_subdisk L (hr m).1 (hr m).2).mp ((eventually_passes_iff L (hr m).1 (hr m).2).mp (h L m))
  · intro h L _ _ m
    exact (eventually_passes_iff L (hr m).1 (hr m).2).mpr ((grid_iff_subdisk L (hr m).1 (hr m).2).mpr (h L m))

theorem left_height {r : ℝ} (h1 : r < 1) {w : ℂ} (hw : ‖w‖ ≤ r) (hx : (criticalPoint w).re < 1) :
    1+(1-r^2)*(criticalPoint w).im^2 < 4*r^2 := by
  let z := criticalPoint w
  have hw1 : w ≠ 1 := by rintro rfl; simp at hw; linarith
  have he := (eq_div_iff (sub_ne_zero.mpr hw1.symm)).mp (critical_formula (hw.trans_lt h1))
  have hrel : z-2 = w*(z+1) := by change criticalPoint w-2 = _; linear_combination he
  have hn := congrArg norm hrel
  rw [norm_mul] at hn
  have hsq := pow_le_pow_left₀ (norm_nonneg _) (hn.trans_le (mul_le_mul_of_nonneg_right hw (norm_nonneg _))) 2
  rw [mul_pow,Complex.sq_norm,Complex.sq_norm,Complex.normSq_apply,Complex.normSq_apply] at hsq
  norm_num [sub_re,sub_im,add_re,add_im] at hsq
  have hp : 1/2 < z.re := image_halfplane.mp ⟨w,hw.trans_lt h1,rfl⟩
  change z.re < 1 at hx
  have hl : 1 < (z.re-2)^2 := by nlinarith [sq_nonneg (1-z.re)]
  have hu : (z.re+1)^2 ≤ 4 := by nlinarith [mul_nonneg (show 0 ≤ 1-z.re by linarith) (show 0 ≤ z.re+3 by linarith)]
  change 1+(1-r^2)*z.im^2 < 4*r^2
  nlinarith only [hl,hsq,mul_le_mul_of_nonneg_left hu (sq_nonneg r)]

theorem all_fields_half : ∀ᶠ n : ℕ in atTop, passesAt K (1/2) n := by
  apply (eventually_passes_iff K (by norm_num) (by norm_num)).mpr
  intro w hw
  apply (CayleyFields.boundary K).2
  by_contra! hx
  have h := left_height (by norm_num : (1/2:ℝ)<1) hw hx
  nlinarith [sq_nonneg (criticalPoint w).im]

theorem from_height {r A : ℝ} (hr : 0 ≤ r) (h1 : r < 1) (hA : 0 ≤ A)
    (hsize : r^2*(4+A^2) ≤ 1+A^2)
    (hz : ∀ z ∈ zeros K, 0 < z.re → A < |z.im|) :
    ∀ᶠ n : ℕ in atTop, passesAt K r n := by
  apply (eventually_passes_iff K hr h1).mpr
  intro w hw he
  let z := criticalPoint w
  have hx : z.re < 1 := zeros_left K he
  have hp : 1/2 < z.re := image_halfplane.mp ⟨w,hw.trans_lt h1,rfl⟩
  have hlt := hz z he (by linarith)
  have hg := left_height h1 hw hx
  have hs := pow_le_pow_left₀ hA hlt.le 2
  rw [sq_abs] at hs
  have hpos : 0 ≤ 1-r^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr h1.le) (add_nonneg hr zero_le_one)]
  change 1+(1-r^2)*z.im^2 < 4*r^2 at hg
  nlinarith only [hsize,hg,mul_le_mul_of_nonneg_left hs hpos]

theorem degree_one (hk : Module.finrank ℚ K = 1) :
    ∀ᶠ n : ℕ in atTop, passesAt K (subradius 25) n := by
  apply from_height K (A := 6) (by norm_num [subradius]) (by norm_num [subradius]) (by norm_num) (by norm_num [subradius])
  intro z hz hp
  have hlt := zeros_left K hz
  have hne : z ≠ 1 := by rintro rfl; norm_num at hlt
  have hQ := R_ERH_extended_riemann_hypothesis_R1_H1_R1.isDedekindZeta_rat_of_finrank_one hk
    (canonical_isDedekindZeta K)
  by_contra! h
  apply LowHeight.zero_free_six hp hlt h
  rw [← R_ERH_extended_riemann_hypothesis_R1_H1_R1.agrees_off_one hQ hne,canonicalZeta,
    show entireReg K z = 0 from hz,zero_div]

theorem gaussian : ∀ᶠ n : ℕ in atTop, passesAt (CyclotomicField 4 ℚ) (subradius 6) n := by
  apply from_height _ (A := 23/8) (by norm_num [subradius]) (by norm_num [subradius]) (by norm_num) (by norm_num [subradius])
  exact fun _ hz hp => SharpStrip.gaussian_zero_height hz hp

theorem small_cubic (hk : Module.finrank ℚ K = 3) (hD : (discr K).natAbs ≤ 23) :
    ∀ᶠ n : ℕ in atTop, passesAt K (subradius 3) n := by
  apply from_height _ (A := 89/50) (by norm_num [subradius]) (by norm_num [subradius]) (by norm_num) (by norm_num [subradius])
  intro z hz hp
  have h := CubicDisk.small_cubic_height K hk hD hz hp
  by_contra! hle
  nlinarith only [h,sq_abs z.im,pow_le_pow_left₀ (abs_nonneg z.im) hle 2]

theorem fifth : ∀ᶠ n : ℕ in atTop, passesAt (CyclotomicField 5 ℚ) (subradius 2) n := by
  apply from_height _ (A := 21/16) (by norm_num [subradius]) (by norm_num [subradius]) (by norm_num) (by norm_num [subradius])
  intro z hz hp
  have h := QuarticDisk.fifth_zero_height hz hp
  by_contra! hle
  nlinarith only [h,sq_abs z.im,pow_le_pow_left₀ (abs_nonneg z.im) hle 2]

#print axioms slope_le
#print axioms eventually_passes_iff
#print axioms fixed_mesh_iff_erh
#print axioms left_height
#print axioms all_fields_half
#print axioms from_height
#print axioms degree_one
#print axioms gaussian
#print axioms small_cubic
#print axioms fifth
end OMA.CayleyCertificates
