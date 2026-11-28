import CentralRadius

/-! A three-exponential upper bound for the folded critical-strip moment.
This separates the first trivial zero from the critical-strip zeros in a
closed interval of heights for the fourth cyclotomic field. -/
noncomputable section
namespace OMA.SharpStrip
open Complex NumberField NumberField.InfinitePlace MeasureTheory Set
open ThetaContinuation HeatDecay ExactRadius
variable (K : Type*) [Field K] [NumberField K]

private def decay (a x : ℝ) := Real.exp (-(a*(x-1)))

private theorem decay_eq (a : ℝ) :
    decay a = fun x => Real.exp a * Real.exp (-a*x) := by
  funext x
  rw [decay, ← Real.exp_add]; congr 1; ring

private theorem decay_int {a : ℝ} (ha : 0 < a) : IntegrableOn (decay a) (Ioi 1) := by
  rw [decay_eq]; exact (integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) 1).const_mul _

private theorem decay_mass {a : ℝ} (ha : 0 < a) : ∫ x in Ioi 1, decay a x = 1/a := by
  rw [decay_eq, integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos ha), mul_one, Real.exp_neg]
  field_simp [(Real.exp_pos a).ne']

private theorem reciprocal_majorant {x : ℝ} (hx : 1 < x) :
    1+x⁻¹ ≤ 2-decay 1 x + (decay 1 x)^2 := by
  let e := decay 1 x
  have he : 0 ≤ e := (Real.exp_pos _).le
  have hx0 := zero_lt_one.trans hx
  have hinv : e ≤ x⁻¹ := by
    dsimp [e, decay]; rw [one_mul, Real.exp_neg]
    apply (inv_le_inv₀ (Real.exp_pos _) hx0).mpr
    linarith [Real.add_one_le_exp (x-1)]
  have hu : 1-e ≤ x-1 := by
    have hh := Real.add_one_le_exp (-(x-1))
    dsimp [e, decay]; rw [one_mul]; linarith
  have hprod := mul_le_mul hu hinv he (sub_nonneg.mpr hx.le)
  have heq : (x-1)*x⁻¹ = 1-x⁻¹ := by field_simp [hx0.ne']
  change 1+x⁻¹ ≤ 2-e+e^2
  nlinarith

private theorem decay_add (a b x : ℝ) :
    decay (a+b) x = decay a x * decay b x := by
  simp only [decay, ← Real.exp_add]; congr 1; ring

theorem sharp_moment (hr : nrRealPlaces K = 0) (hc : nrComplexPlaces K = 1)
    {a : ℝ} (ha : 0 < a) (haq : a ≤ rate K)
    {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1) :
    ‖(pair K).Λ₀ s‖ ≤ heat K 1 * (2/a - 1/(a+1) + 1/(a+2)) := by
  let f := fun x => 2*decay a x - decay (a+1) x + decay (a+2) x
  have hb : 0 < a+1 := by linarith
  have hc' : 0 < a+2 := by linarith
  have hi : IntegrableOn f (Ioi 1) := (((decay_int ha).const_mul 2).sub (decay_int hb)).add (decay_int hc')
  have hm := StripHeat.strip_majorant K hr hc h0 h1 (hi.const_mul (heat K 1)) (fun x hx => by
    have hdec : heat K x ≤ heat K 1 * decay a x := by
      rw [mul_comm (heat K 1)]
      apply (contraction K zero_lt_one hx.le).trans
      apply mul_le_mul_of_nonneg_right _ (heat_nonneg K 1)
      exact Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right haq (sub_nonneg.mpr hx.le)))
    have hcoef := reciprocal_majorant hx
    have hcpos : 0 ≤ 1+x⁻¹ := by have := zero_lt_one.trans hx; positivity
    have hmajor := mul_le_mul hcoef hdec (heat_nonneg K x) (hcpos.trans hcoef)
    have hf : f x = (2-decay 1 x+(decay 1 x)^2)*decay a x := by
      dsimp [f]
      rw [decay_add a 1, decay_add a 2,
        show decay 2 x = decay 1 x * decay 1 x by
          rw [show (2:ℝ) = 1+1 by norm_num]; exact decay_add 1 1 x]
      ring
    change (1+x⁻¹)*heat K x ≤ heat K 1 * f x
    rw [hf]
    linarith only [hmajor, show (2-decay 1 x+(decay 1 x)^2)*(heat K 1*decay a x) =
      heat K 1*((2-decay 1 x+(decay 1 x)^2)*decay a x) by ring])
  have hf : (∫ x in Ioi 1, f x) = 2/a-1/(a+1)+1/(a+2) := by
    dsimp [f]
    have hsub : IntegrableOn (fun x => 2*decay a x - decay (a+1) x) (Ioi 1) :=
      ((decay_int ha).const_mul 2).sub (decay_int hb)
    have hmul : IntegrableOn (fun x => 2*decay a x) (Ioi 1) := (decay_int ha).const_mul 2
    rw [integral_add hsub (decay_int hc'), integral_sub hmul (decay_int hb), integral_const_mul,
      decay_mass ha, decay_mass hb, decay_mass hc']
    ring
  rwa [integral_const_mul, hf] at hm

theorem gaussian_zero_height {s : ℂ} (hz : s ∈ zeros (CyclotomicField 4 ℚ)) (h0 : 0 < s.re) :
    23/8 < |s.im| := by
  let F := CyclotomicField 4 ℚ
  obtain ⟨hr,hc,hd⟩ := CyclotomicDisks.gaussian_invariants
  have hq : (25:ℝ)/8 ≤ rate F := by
    change 25/8 ≤ 2*Real.pi / Real.sqrt (((discr (CyclotomicField 4 ℚ)).natAbs:ℕ):ℝ)
    rw [hd]
    change 25/8 ≤ 2*Real.pi / Real.sqrt 4
    rw [show Real.sqrt 4 = 2 by norm_num]
    linarith [Real.pi_gt_d2]
  have h1 := zeros_left F hz
  have hn : s ≠ 0 := by rintro rfl; norm_num at h0
  have e := (entireReg_eq_reg F hn).symm.trans (show entireReg F s = 0 from hz)
  rw [reg] at e
  have he := (div_eq_zero_iff.mp ((mul_eq_zero.mp e).resolve_right (inv_ne_zero (arch_ne F h0)))).resolve_right hn
  have heq := congrArg (fun z : ℂ => ‖z‖)
    (eq_neg_of_add_eq_zero_left he : s*(s-1)*(pair F).Λ₀ s = -cst F)
  simp only [norm_mul, norm_neg] at heq
  have hC := norm_pos_iff.mpr (cst_ne F)
  have hM := sharp_moment F hr hc (by norm_num) hq h0.le h1.le
  norm_num at hM
  have hL := SelfDualHeat.self_dual_residue F hr hc
  have hL' : (2*(25/8)-1)*heat F 1 ≤ ‖cst F‖ :=
    (mul_le_mul_of_nonneg_right (by linarith : 2*(25/8)-1 ≤ 2*rate F-1) (heat_nonneg F 1)).trans hL
  by_contra! him
  have hs := (sq_le_sq₀ (abs_nonneg s.im) (by norm_num)).mpr him
  rw [sq_abs] at hs
  have hA : ‖s‖^2 = s.re^2+s.im^2 := by rw [Complex.sq_norm, normSq_apply]; ring
  have hB : ‖s-1‖^2 = (s.re-1)^2+s.im^2 := by rw [Complex.sq_norm, normSq_apply]; simp [sq]
  have hp : ‖s‖*‖s-1‖ ≤ (23/8)^2+1/2 := by
    nlinarith [sq_nonneg (‖s‖-‖s-1‖), mul_pos h0 (sub_pos.mpr h1)]
  have hU := mul_le_mul hp hM (norm_nonneg _) (by norm_num)
  rw [heq] at hU
  linarith

theorem gaussian_exact {t : ℝ} (ht : |t| ≤ 1/24) :
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ, p.radius = ENNReal.ofReal (Real.sqrt (9+t^2)) ∧
      ReciprocalRadius.InverseGerm (CyclotomicField 4 ℚ) t p := by
  let F := CyclotomicField 4 ℚ
  obtain ⟨hr,hc,_⟩ := CyclotomicDisks.gaussian_invariants
  have hgap : 9+t^2 ≤ 1+(23/8-|t|)^2 := by nlinarith [sq_abs t]
  have hd := CentralRadius.exact_from_height F hr hc (fun _ => gaussian_zero_height)
    (t := t) (by linarith) hgap
  obtain ⟨p,hp,hg⟩ := AllFieldRadius.all_fields_radius_gt_one F t
  exact ⟨p, (radius_eq_zeroDistance F t (zero_lt_one.trans hp) hg).trans (congrArg ENNReal.ofReal hd), hg⟩

#print axioms sharp_moment
#print axioms gaussian_zero_height
#print axioms gaussian_exact
end OMA.SharpStrip
