import RealFifth

/-! Cubic-field disks. After the substitution u=x^(2/3), the folded weight
is (3/2)(sqrt(u)+1/u). A four-exponential majorant keeps the margin needed
to identify the zero at the origin as a nearest zero. -/
noncomputable section
namespace OMA.CubicDisk
open Complex NumberField NumberField.InfinitePlace MeasureTheory Set
open GeneralHeat GeneralSlope GeneralStrip RadialProfile ThetaContinuation ExactRadius

private def decay (b u : ℝ) := Real.exp (-b*(u-1))
private def component (b x : ℝ) := x^(-(1/3:ℝ)) * decay b (x^(2/3:ℝ))

private theorem component_int {b : ℝ} (hb : 0 < b) : IntegrableOn (component b) (Ioi 1) := by
  have hi : IntegrableOn (fun x : ℝ => Real.exp b * (x^(-(1/3:ℝ))*Real.exp (-b*x^(2/3:ℝ)))) (Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num : -(1:ℝ) < -(1/3:ℝ))
    (by norm_num : 0 < (2/3:ℝ)) hb).const_mul (Real.exp b)
  apply (hi.mono_set (Ioi_subset_Ioi (zero_le_one : (0:ℝ) ≤ 1))).congr_fun _ measurableSet_Ioi
  intro x hx
  dsimp [component, decay]
  rw [show -b*(x^(2/3:ℝ)-1) = b+(-b*x^(2/3:ℝ)) by ring, Real.exp_add]
  ring

private theorem component_mass {b : ℝ} (hb : 0 < b) :
    ∫ x in Ioi 1, component b x = (3/2)/b := by
  have h := integral_comp_rpow_Ioi_of_pos' (g := component b)
    (by norm_num : 0 < (3/2:ℝ)) (zero_le_one : (0:ℝ) ≤ 1)
  rw [Real.one_rpow] at h
  rw [← h]
  calc _ = ∫ x : ℝ in Ioi 1, ((3/2)*Real.exp b) * Real.exp (-b*x) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro x hx
          have hx0 : 0 < x := zero_lt_one.trans hx
          change ((3/2)*x^((3/2:ℝ)-1))*component b (x^(3/2:ℝ)) = _
          unfold component decay
          rw [← Real.rpow_mul hx0.le, ← Real.rpow_mul hx0.le,
            show (3/2:ℝ)*(2/3)=1 by norm_num, Real.rpow_one,
            show -(b)*(x-1)=b+(-b*x) by ring, Real.exp_add]
          have hpow : x^((3/2:ℝ)-1) * x^((3/2:ℝ)*(-(1/3))) = 1 := by
            rw [← Real.rpow_add hx0]; norm_num
          linear_combination (3/2*Real.exp b*Real.exp (-b*x))*hpow
       _ = _ := by
          rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos hb), mul_one, Real.exp_neg]
          field_simp [(Real.exp_pos b).ne']

private theorem reciprocal_envelope {u : ℝ} (hu : 1 ≤ u) :
    u⁻¹ ≤ 1-Real.exp (-(u-1))+Real.exp (-(2*(u-1))) := by
  let e := Real.exp (-(u-1))
  have hu0 := zero_lt_one.trans_le hu
  have he : 0 ≤ e := (Real.exp_pos _).le
  have hinv : e ≤ u⁻¹ := by
    dsimp [e]; rw [Real.exp_neg, inv_le_inv₀ (Real.exp_pos _) hu0]
    linarith [Real.add_one_le_exp (u-1)]
  have hlin : 1-e ≤ u-1 := by dsimp [e]; linarith [Real.add_one_le_exp (-(u-1))]
  have hm := mul_le_mul hlin hinv he (sub_nonneg.mpr hu)
  have hprod : (u-1)*u⁻¹ = 1-u⁻¹ := by field_simp [hu0.ne']
  have he2 : Real.exp (-(2*(u-1))) = e*e := by
    dsimp [e]; rw [← Real.exp_add]; congr 1; ring
  rw [he2]
  change u⁻¹ ≤ 1-e+e*e
  nlinarith

private theorem decay_mul (a b u : ℝ) : decay (a+b) u = decay a u*decay b u := by
  dsimp [decay]; rw [← Real.exp_add]; congr 1; ring

variable (K : Type*) [Field K] [NumberField K]

theorem cubic_moment (he : exponent K = 2/3) {a : ℝ} (ha : 1/2 < a)
    (hal : a ≤ GeneralHeat.rate K) {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1) :
    ‖(pair K).Λ₀ s‖ ≤ heat K 1 * ((3/2)/(a-1/2)+(3/2)/a-(3/2)/(a+1)+(3/2)/(a+2)) := by
  have ha0 : 0 < a := by linarith
  have hA : 0 < a-1/2 := by linarith
  have hB : 0 < a+1 := by linarith
  have hC : 0 < a+2 := by linarith
  let B := fun x => component (a-1/2) x+component a x-component (a+1) x+component (a+2) x
  have hi1 : IntegrableOn (fun x => component (a-1/2) x+component a x) (Ioi 1) :=
    (component_int hA).add (component_int ha0)
  have hi2 : IntegrableOn (fun x => component (a-1/2) x+component a x-component (a+1) x) (Ioi 1) :=
    hi1.sub (component_int hB)
  have hi : IntegrableOn B (Ioi 1) := hi2.add (component_int hC)
  have h := strip_majorant K h0 h1 (hi.const_mul (heat K 1)) (fun x hx => by
    let v := x^(1/3:ℝ)
    let u := x^(2/3:ℝ)
    have hx0 := zero_lt_one.trans hx
    have hu : 1 ≤ u := Real.one_le_rpow hx.le (by norm_num)
    have hv : 0 < v := Real.rpow_pos_of_pos hx0 _
    have hu0 := zero_lt_one.trans_le hu
    have huv : v*u=x := by
      dsimp [v,u]; rw [← Real.rpow_add hx0, show (1/3:ℝ)+2/3=1 by norm_num, Real.rpow_one]
    have hv2 : v^2 = u := by
      dsimp [v,u]; rw [← Real.rpow_mul_natCast hx0.le]; congr 1; norm_num
    have hvis : v ≤ decay (-(1/2)) u := by
      apply (sq_le_sq₀ hv.le (Real.exp_pos _).le).mp
      rw [hv2]
      change u ≤ (Real.exp (-(-(1/2:ℝ))*(u-1)))^2
      rw [sq, ← Real.exp_add, show -(-(1/2:ℝ))*(u-1)+ -(-(1/2:ℝ))*(u-1)=u-1 by ring]
      linarith [Real.add_one_le_exp (u-1)]
    have hcoef : v+u⁻¹ ≤ decay (-(1/2)) u+1-decay 1 u+decay 2 u := by
      have hr := reciprocal_envelope hu
      simp only [decay, neg_mul, one_mul] at hvis ⊢
      linarith
    have hfac : 1+x⁻¹ = v⁻¹*(v+u⁻¹) := by rw [← huv]; field_simp
    have hheat := contraction K zero_lt_one hx.le
    rw [he, Real.one_rpow] at hheat
    have hdec : heat K x ≤ decay a u * heat K 1 := by
      apply hheat.trans (mul_le_mul_of_nonneg_right _ (heat_nonneg K 1))
      exact Real.exp_le_exp.mpr (by dsimp [u] at *; nlinarith [mul_le_mul_of_nonneg_right hal (sub_nonneg.mpr hu)])
    have h0c : 0 ≤ v+u⁻¹ := add_nonneg hv.le (inv_nonneg.mpr hu0.le)
    have hm := mul_le_mul hcoef hdec (heat_nonneg K x) (h0c.trans hcoef)
    change (1+x⁻¹)*heat K x ≤ heat K 1*B x
    rw [hfac, mul_assoc]
    apply (mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr hv.le)).trans_eq
    dsimp only [B, component]
    rw [Real.rpow_neg hx0.le]
    change _ = heat K 1*(v⁻¹*decay (a-1/2) u+v⁻¹*decay a u-v⁻¹*decay (a+1) u+v⁻¹*decay (a+2) u)
    rw [sub_eq_add_neg a, decay_mul a (-(1/2)) u, decay_mul a 1 u, decay_mul a 2 u]
    ring)
  have hmass : (∫ x in Ioi 1, B x) = (3/2)/(a-1/2)+(3/2)/a-(3/2)/(a+1)+(3/2)/(a+2) := by
    dsimp only [B]
    rw [integral_add hi2 (component_int hC), integral_sub hi1 (component_int hB),
      integral_add (component_int hA) (component_int ha0), component_mass hA,
      component_mass ha0, component_mass hB, component_mass hC]
  rwa [integral_const_mul, hmass] at h

private theorem rates (hd : Module.finrank ℚ K = 3) (hD : (discr K).natAbs ≤ 23) :
    exponent K = 2/3 ∧ 11/5 ≤ slopeRate K ∧ 33/10 ≤ GeneralHeat.rate K := by
  have hd' : degree K = 3 := by unfold degree; rw [hd]; norm_num
  have he : exponent K = 2/3 := by rw [exponent, hd']
  have hdisc : 0 < ((discr K).natAbs:ℝ) := by exact_mod_cast Int.natAbs_pos.mpr (discr_ne_zero K)
  have hroot : ((discr K).natAbs:ℝ)^(1/3:ℝ) ≤ 57/20 := by
    apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg hdisc.le _) (by norm_num) (by decide : (3:ℕ)≠0)).mp
    rw [← Real.rpow_mul_natCast hdisc.le]
    rw [show (1/3:ℝ)*(3:ℕ)=1 by norm_num, Real.rpow_one]
    exact (show ((discr K).natAbs:ℝ) ≤ 23 by exact_mod_cast hD).trans (by norm_num)
  have hq : 11/5 ≤ slopeRate K := by
    rw [slopeRate_eq, hd', le_div_iff₀ (Real.rpow_pos_of_pos hdisc _)]
    linarith [Real.pi_gt_d2]
  refine ⟨he, hq, ?_⟩
  rw [slopeRate, he] at hq
  linarith

theorem small_cubic_height (hd : Module.finrank ℚ K = 3) (hD : (discr K).natAbs ≤ 23)
    {z : ℂ} (hz : z ∈ zeros K) (h0 : 0 < z.re) : (89/50:ℝ)^2 < z.im^2 := by
  obtain ⟨he,hq,hl⟩ := rates K hd hD
  have h1 := zeros_left K hz
  have hM := cubic_moment K he (by norm_num) hl h0.le h1.le
  norm_num at hM
  have hL := self_dual_residue K
  have hL' : (2*(11/5)-1)*heat K 1 ≤ ‖cst K‖ :=
    (mul_le_mul_of_nonneg_right (by linarith : 2*(11/5)-1 ≤ 2*slopeRate K-1) (heat_nonneg K 1)).trans hL
  by_contra! him
  have hp : ‖z‖*‖z-1‖ ≤ (89/50:ℝ)^2+1/2 := by linarith [height_of_product h0 h1]
  have hu := mul_le_mul hp hM (norm_nonneg _) (by norm_num)
  rw [product_at_zero K hz h0] at hu
  linarith [norm_pos_iff.mpr (cst_ne K)]

theorem small_cubic_exact (hd : Module.finrank ℚ K = 3) (hD : (discr K).natAbs ≤ 23)
    {t : ℝ} (ht : |t| ≤ 1/25) :
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ, p.radius = ENNReal.ofReal (Real.sqrt (4+t^2)) ∧
      ReciprocalRadius.InverseGerm K t p := by
  have hzero : (0:ℂ) ∈ zeros K := by
    apply ZeroAtOrigin.origin_mem
    have := card_add_two_mul_card_eq_rank K
    omega
  have hv (z : ℂ) (hz : z ∈ zeros K) (hp : 0 < z.re) : 89/50 < |z.im| := by
    apply (sq_lt_sq₀ (by norm_num) (abs_nonneg _)).mp
    rw [sq_abs]; exact small_cubic_height K hd hD hz hp
  have hgap : 4+t^2 ≤ 1+(89/50-|t|)^2 := by nlinarith [sq_abs t]
  have hh := RealFifth.exact_at_origin_zero K hzero hv (by linarith : |t| ≤ 89/50) hgap
  obtain ⟨p,hp,hg⟩ := AllFieldRadius.all_fields_radius_gt_one K t
  exact ⟨p, (radius_eq_zeroDistance K t (zero_lt_one.trans hp) hg).trans (congrArg ENNReal.ofReal hh), hg⟩

theorem small_cubic_radius (hd : Module.finrank ℚ K = 3) (hD : (discr K).natAbs ≤ 23)
    {t : ℝ} (ht : |t| ≤ 13/20) :
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ, ENNReal.ofReal (3/2) < p.radius ∧
      ReciprocalRadius.InverseGerm K t p := by
  refine radius_from_height K (T := 89/50) (by norm_num)
    (fun _ => small_cubic_height K hd hD) (by linarith) ?_
  have hm : 113/100 ≤ 89/50-|t| := by linarith
  have := (sq_le_sq₀ (by norm_num) (by linarith : 0 ≤ 89/50-|t|)).mpr hm
  linarith

#print axioms cubic_moment
#print axioms small_cubic_height
#print axioms small_cubic_exact
#print axioms small_cubic_radius
end OMA.CubicDisk
