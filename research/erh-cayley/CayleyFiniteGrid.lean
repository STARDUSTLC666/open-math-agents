import CayleySections

/-! Finite lattice checks for the smoothed Cayley Taylor polynomials.
Both coordinates are rounded toward zero to stay in the same closed disk. -/
noncomputable section
namespace OMA.CayleyFiniteGrid
open Complex Set Filter Metric NumberField CayleyBounds CayleyRecurrence CayleyHigher CayleySections ExactRadius
open scoped Topology

def node (D : ℕ) (j k : ℤ) : ℂ := ⟨(j:ℝ)/D,(k:ℝ)/D⟩

private theorem round_axis (x : ℝ) {D : ℕ} (hD : 0 < D) :
    ∃ j : ℤ, |(j:ℝ)/D| ≤ |x| ∧ |x-(j:ℝ)/D| ≤ (D:ℝ)⁻¹ := by
  have hpos : 0 < (D:ℝ) := by exact_mod_cast hD
  have positive (y : ℝ) (hy : 0 ≤ y) :
      ∃ j : ℤ, |(j:ℝ)/D| ≤ |y| ∧ |y-(j:ℝ)/D| ≤ (D:ℝ)⁻¹ := by
    let j := ⌊y*(D:ℝ)⌋
    have hj : 0 ≤ (j:ℝ) := by exact_mod_cast (Int.floor_nonneg.mpr (mul_nonneg hy hpos.le))
    have hlo : (j:ℝ)/D ≤ y := (div_le_iff₀ hpos).mpr (Int.floor_le _)
    refine ⟨j,by simpa [abs_of_nonneg hy,abs_of_nonneg (div_nonneg hj hpos.le)] using hlo,?_⟩
    rw [abs_of_nonneg (sub_nonneg.mpr hlo),inv_eq_one_div,sub_le_iff_le_add,← add_div]
    exact (le_div_iff₀ hpos).mpr (by linarith [Int.lt_floor_add_one (y*(D:ℝ))])
  by_cases hx : 0 ≤ x
  · exact positive x hx
  · obtain ⟨j,hlo,hhi⟩ := positive (-x) (neg_nonneg.mpr (le_of_not_ge hx))
    refine ⟨-j,by simpa [neg_div] using hlo,?_⟩
    have he : x-((-j:ℤ):ℝ)/D = -(-x-(j:ℝ)/D) := by push_cast; ring
    simpa only [he,abs_neg] using hhi

theorem inward_node {D : ℕ} (hD : 0 < D) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ∃ j ∈ Finset.Icc (-(D:ℤ)) D, ∃ k ∈ Finset.Icc (-(D:ℤ)) D,
      ‖node D j k‖ ≤ ‖w‖ ∧ ‖w-node D j k‖ ≤ 2/(D:ℝ) := by
  obtain ⟨j,hx,hdx⟩ := round_axis w.re hD
  obtain ⟨k,hy,hdy⟩ := round_axis w.im hD
  have hpos : 0 < (D:ℝ) := by exact_mod_cast hD
  have hbox (i : ℤ) (h : |(i:ℝ)/D| ≤ 1) : i ∈ Finset.Icc (-(D:ℤ)) D := by
    rw [abs_div,abs_of_pos hpos,(div_le_one hpos)] at h
    have hi : |i| ≤ (D:ℤ) := by exact_mod_cast h
    exact Finset.mem_Icc.mpr (abs_le.mp hi)
  refine ⟨j,hbox _ (hx.trans ((abs_re_le_norm w).trans hw)),
    k,hbox _ (hy.trans ((abs_im_le_norm w).trans hw)),?_,?_⟩
  · apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [Complex.sq_norm,Complex.sq_norm,Complex.normSq_apply,Complex.normSq_apply]
    have hx' := pow_le_pow_left₀ (abs_nonneg _) hx 2
    have hy' := pow_le_pow_left₀ (abs_nonneg _) hy 2
    simp only [sq_abs] at hx' hy'
    dsimp only [node]
    nlinarith only [hx',hy']
  · apply (norm_le_abs_re_add_abs_im _).trans
    change |w.re-(j:ℝ)/D|+|w.im-(k:ℝ)/D| ≤ _
    exact (add_le_add hdx hdy).trans_eq (by ring)

private theorem pow_lipschitz (n : ℕ) {u v : ℂ} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    ‖u^n-v^n‖ ≤ (n:ℝ)*‖u-v‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : u^(n+1)-v^(n+1) = (u^n-v^n)*u+v^n*(u-v) := by rw [pow_succ,pow_succ]; ring
    rw [he]
    apply (norm_add_le _ _).trans
    rw [norm_mul,norm_mul,norm_pow,Nat.cast_succ,add_mul,one_mul]
    exact add_le_add ((mul_le_of_le_one_right (norm_nonneg _) hu).trans ih)
      (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hv))

variable (a : ℕ → ℂ)

def slope (L : ℕ) := ∑ j ∈ Finset.range L, ‖a j‖*(j:ℝ)

theorem polynomial_lipschitz (L : ℕ) {u v : ℂ} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    ‖taylorPoly a L u-taylorPoly a L v‖ ≤ slope a L * ‖u-v‖ := by
  rw [taylorPoly,taylorPoly,← Finset.sum_sub_distrib,slope,Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [← mul_sub,norm_mul,mul_assoc]
  exact mul_le_mul_of_nonneg_left (pow_lipschitz j hu hv) (norm_nonneg _)

def passes (r t : ℝ) (L D : ℕ) := ∀ j ∈ Finset.Icc (-(D:ℤ)) D, ∀ k ∈ Finset.Icc (-(D:ℤ)) D,
  ‖node D j k‖ ≤ r → t + 2*slope a L / (D:ℝ) < ‖taylorPoly a L (node D j k)‖

theorem finite_lower_test {r : ℝ} (hr : 0 ≤ r) (h1 : r ≤ 1) (t : ℝ) (L : ℕ) :
    (∀ w : ℂ, ‖w‖ ≤ r → t < ‖taylorPoly a L w‖) ↔ ∃ D : ℕ, 0 < D ∧ passes a r t L D := by
  have hs : 0 ≤ slope a L := Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (by positivity)
  constructor
  · intro h
    have hc : Continuous (fun w => taylorPoly a L w) := by unfold taylorPoly; fun_prop
    obtain ⟨v,hv,hm⟩ := (isCompact_closedBall (0:ℂ) r).exists_isMinOn
      ⟨0,mem_closedBall_self hr⟩ hc.norm.continuousOn
    have hgap := sub_pos.mpr (h v (mem_closedBall_zero_iff.mp hv))
    obtain ⟨D,hD⟩ := exists_nat_gt (max (2*slope a L/(‖taylorPoly a L v‖-t)) 0)
    have hpos : 0 < (D:ℝ) := (le_max_right _ _).trans_lt hD
    have hd := (div_lt_iff₀ hgap).mp ((le_max_left _ _).trans_lt hD)
    have hstrict : 2*slope a L/(D:ℝ) < ‖taylorPoly a L v‖-t :=
      (div_lt_iff₀ hpos).mpr (by linarith only [hd])
    refine ⟨D,by exact_mod_cast hpos,?_⟩
    intro j _ k _ hn
    have hmin := isMinOn_iff.mp hm _ (mem_closedBall_zero_iff.mpr hn)
    change ‖taylorPoly a L v‖ ≤ ‖taylorPoly a L (node D j k)‖ at hmin
    linarith
  · rintro ⟨D,hD,hg⟩ w hw
    obtain ⟨j,hj,k,hk,hn,hnear⟩ := inward_node hD (hw.trans h1)
    have hlarge := hg j hj k hk (hn.trans hw)
    have hp := polynomial_lipschitz a L (hw.trans h1) ((hn.trans hw).trans h1)
    have htri := norm_add_le (taylorPoly a L (node D j k)-taylorPoly a L w) (taylorPoly a L w)
    rw [sub_add_cancel,norm_sub_rev] at htri
    have hnear' := mul_le_mul_of_nonneg_left hnear hs
    rw [show slope a L*(2/(D:ℝ)) = 2*slope a L/D by ring] at hnear'
    linarith

theorem zero_free_finite_grid (K : Type*) [Field K] [NumberField K] : ∃ M : ℝ, 0 ≤ M ∧ ∀ r : ℝ, 0 ≤ r → r < 1 →
    ((∀ w : ℂ, ‖w‖ ≤ r → entireReg K (point w) ≠ 0) ↔
      ∃ N D : ℕ, 0 < D ∧ passes (difference^[order K] (b K)) r (M/((N:ℝ)+1)) (N+2) D) := by
  obtain ⟨M,hM,h⟩ := subdisk_certificate K
  refine ⟨M,hM,fun r hr h1 => ?_⟩
  rw [h r hr h1]
  exact exists_congr fun N => finite_lower_test _ hr h1.le _ _

#print axioms inward_node
#print axioms polynomial_lipschitz
#print axioms finite_lower_test
#print axioms zero_free_finite_grid
end OMA.CayleyFiniteGrid
