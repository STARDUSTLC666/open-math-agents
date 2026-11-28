import CayleyCertificates
import CayleyReturn

/-! A necessary growth rate for the truncation parameter of every sufficiently
late passing grid. The bound uses the positive real endpoint of each disk. -/
noncomputable section
namespace OMA.CayleyCost
open Complex Set Filter Metric NumberField CayleyCritical CayleyCertificates CayleySections ExactRadius
open scoped Topology

def ray (m : ℕ) : ℂ := (subradius m : ℂ)
def exponent (K : Type*) [Field K] [NumberField K] := Module.finrank ℚ K + 4

private theorem rad (m : ℕ) : 0 ≤ subradius m ∧ subradius m < 1 := by
  dsimp [subradius]
  exact ⟨by positivity,(div_lt_one (by positivity)).mpr (by linarith)⟩

private theorem ray_norm (m : ℕ) : ‖ray m‖ = subradius m :=
  Complex.norm_of_nonneg (rad m).1

theorem ray_coordinate (m : ℕ) : criticalPoint (ray m) = ((3*(m:ℝ)+2:ℝ):ℂ) := by
  rw [critical_formula ((ray_norm m).trans_lt (rad m).2)]
  have hn : 1-ray m ≠ 0 := sub_ne_zero.mpr (fun he => by
    have h := (ray_norm m).trans_lt (rad m).2
    rw [← he,norm_one] at h
    exact lt_irrefl _ h)
  apply (div_eq_iff hn).mpr
  unfold ray subradius
  push_cast
  have hpos : (m:ℂ)+1 ≠ 0 := by exact_mod_cast (show (m:ℝ)+1 ≠ 0 by positivity)
  field_simp [hpos]
  <;> ring

variable (K : Type*) [Field K] [NumberField K]

theorem scaled_value (m : ℕ) :
    ((m:ℝ)+1)^(exponent K)*‖H K (ray m)‖ =
      (3-2/((m:ℝ)+1))*‖dedekindZeta K ((3*(m:ℝ)+2:ℝ):ℂ)‖ := by
  let x : ℝ := (m:ℝ)+1
  have hx : 0 < x := by dsimp [x]; positivity
  have hreal : 1-(m:ℝ)/x = 1/x := by dsimp [x]; field_simp; ring
  have hw : 1-ray m = ((1/x:ℝ):ℂ) := by
    change 1-(((m:ℝ)/x:ℝ):ℂ) = _
    rw [← Complex.ofReal_one,← Complex.ofReal_sub,hreal]
  have hright : 1 < ((3*(m:ℝ)+2:ℝ):ℂ).re := by
    change 1 < 3*(m:ℝ)+2
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hsub : ((3*(m:ℝ)+2:ℝ):ℂ)-1 = ((3*(m:ℝ)+1:ℝ):ℂ) := by push_cast; ring
  change x^(exponent K)*‖(1-ray m)^CayleyHigher.order K*entireReg K (criticalPoint (ray m))‖ = _
  rw [ray_coordinate,(CayleyFields.boundary K).1 _ hright,hw,hsub,norm_mul,norm_pow,
    Complex.norm_of_nonneg (by positivity : 0 ≤ 1/x),norm_mul,Complex.norm_of_nonneg (by positivity)]
  rw [show CayleyHigher.order K = exponent K+1 by rfl,pow_succ,div_pow,one_pow]
  change _ = (3-2/x)*_
  field_simp [hx.ne']
  dsimp [x]
  <;> ring

theorem scaled_limit :
    Tendsto (fun m : ℕ => ((m:ℝ)+1)^(exponent K)*‖H K (ray m)‖) atTop (𝓝 3) := by
  have hx : Tendsto (fun m : ℕ => 3*(m:ℝ)+2) atTop atTop := by
    apply Filter.tendsto_atTop.mpr
    intro b
    obtain ⟨L,hL⟩ := exists_nat_gt b
    filter_upwards [eventually_ge_atTop L] with m hm
    have h : (L:ℝ) ≤ m := by exact_mod_cast hm
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hZ := ((CayleyReturn.real_limit K).comp hx).norm
  have he := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hf := (tendsto_const_nhds (x := (3:ℝ))).sub (he.const_mul 2)
  simpa only [scaled_value,Function.comp_apply,norm_one,mul_zero,sub_zero,mul_one,mul_one_div] using hf.mul hZ

theorem necessary_cost {C : ℝ} (hC : 3 < C) :
    ∃ m₀ n₀ : ℕ, ∀ m ≥ m₀, ∀ n ≥ n₀, ∀ D : ℕ, 0 < D →
      CayleyFiniteGrid.passes (a K) (subradius m) (1/((n:ℝ)+1)) (length n) D →
      ((m:ℝ)+1)^(exponent K) < C*((n:ℝ)+1) := by
  let U := (C+3)/2
  have hU : 3 < U := by dsimp [U]; linarith
  have hUC : U < C := by dsimp [U]; linarith
  have hc : 0 < C := by linarith
  obtain ⟨m₀,hm₀⟩ := eventually_atTop.mp ((scaled_limit K).eventually_lt_const hU)
  have hfrac : U/C < 1 := (div_lt_one hc).mpr hUC
  have hlim := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (major K)
  have htend : Tendsto (fun n : ℕ => 1-major K/((n:ℝ)+1)) atTop (𝓝 1) := by
    simpa only [mul_zero,sub_zero,mul_one_div] using (tendsto_const_nhds (x := (1:ℝ))).sub hlim
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp (htend.eventually_const_lt hfrac)
  refine ⟨m₀,n₀,?_⟩
  intro m hm n hn D hD hp
  let b : ℝ := (n:ℝ)+1
  let A := ((m:ℝ)+1)^(exponent K)
  have hb : 0 < b := by dsimp [b]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hw := (ray_norm m).trans_lt (rad m).2
  let P := taylorPoly (a K) (length n) (ray m)
  have hP : 1/b < ‖P‖ :=
    (CayleyFiniteGrid.finite_lower_test _ (rad m).1 (rad m).2.le _ _).mpr ⟨D,hD,hp⟩ _ (ray_norm m).le
  have he := critical_tail K ((n+1)^2) hw
  have hden : ((((n+1)^2:ℕ):ℝ)+1) = b^2+1 := by dsimp [b]; push_cast; ring
  rw [hden] at he
  have hM : 0 ≤ major K := (critical_decay K).choose_spec.1
  have herr : ‖H K (ray m)-P‖ ≤ major K / b^2 := he.trans
    (div_le_div_of_nonneg_left hM (by positivity) (by linarith))
  have htri := norm_add_le (P-H K (ray m)) (H K (ray m))
  rw [sub_add_cancel,norm_sub_rev] at htri
  have hi : 1/b < major K/b^2+‖H K (ray m)‖ := by linarith only [hP,herr,htri]
  have hi' := (div_lt_iff₀ hb).mp hi
  have heq : (major K/b^2+‖H K (ray m)‖)*b = major K/b+‖H K (ray m)‖*b := by field_simp [hb.ne'] <;> ring
  rw [heq] at hi'
  have hmargin : U/C < 1-major K/b := hn₀ n hn
  have hpoint : U/C < ‖H K (ray m)‖*b := by linarith
  have hdisk : A*‖H K (ray m)‖ < U := hm₀ m hm
  have h1 := mul_lt_mul_of_pos_left hpoint hA
  have h2 := mul_lt_mul_of_pos_right hdisk hb
  have hh : A*(U/C) < U*b  := by nlinarith only [h1,h2]
  have hU0 : 0 < U := by linarith
  have hh' : A*U < (U*b)*C := (div_lt_iff₀ hc).mp (by simpa only [mul_div_assoc] using hh)
  change A < C*b
  exact (mul_lt_mul_iff_left₀ hU0).mp (by linarith only [hh'])

#print axioms ray_coordinate
#print axioms scaled_value
#print axioms scaled_limit
#print axioms necessary_cost
end OMA.CayleyCost
