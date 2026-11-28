import GeneralStrip
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! A square-root exponential envelope gives a concrete H2 disk in the
quartic field of fifth roots of unity. -/
noncomputable section
namespace OMA.QuarticDisk
open Complex NumberField NumberField.InfinitePlace MeasureTheory Set
open ExactRadius GeneralHeat RadialProfile GeneralSlope GeneralStrip ThetaContinuation
variable (K : Type*) [Field K] [NumberField K]

private def envelope (b x : ℝ) := x^(-(1/2:ℝ)) * Real.exp (-b*x^(1/2:ℝ))

private theorem envelope_int {b : ℝ} (hb : 0 < b) : IntegrableOn (envelope b) (Ioi 1) := by
  have h : IntegrableOn (envelope b) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) hb
  exact h.mono_set (Ioi_subset_Ioi (by norm_num))

private theorem envelope_mass {b : ℝ} (hb : 0 < b) :
    ∫ x in Ioi 1, envelope b x = 2*Real.exp (-b)/b := by
  have h := integral_comp_rpow_Ioi_of_pos' (g := envelope b) (by norm_num : 0 < (2:ℝ))
    (zero_le_one : (0:ℝ) ≤ 1)
  rw [Real.one_rpow] at h
  rw [← h]
  calc _ = ∫ x : ℝ in Ioi 1, 2*Real.exp (-b*x) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro x hx
          have hx0 : 0 < x := zero_lt_one.trans hx
          have he : (x^(2:ℝ))^(1/2:ℝ) = x := by
            rw [← Real.rpow_mul hx0.le]; norm_num
          have hn : (x^(2:ℝ))^(-(1/2:ℝ)) = x⁻¹ := by
            rw [Real.rpow_neg (Real.rpow_nonneg hx0.le _), he]
          change (2*x^((2:ℝ)-1))*envelope b (x^(2:ℝ)) = 2*Real.exp (-b*x)
          rw [envelope, he, hn, show (2:ℝ)-1=1 by norm_num, Real.rpow_one]
          field_simp
       _ = _ := by rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos hb), mul_one]; ring

theorem sqrt_moment (he : 1/2 ≤ exponent K) {a : ℝ} (ha : 1/2 < a)
    (hal : a ≤ GeneralHeat.rate K) {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1) :
    ‖(pair K).Λ₀ s‖ ≤ 4*heat K 1/(a-1/2) := by
  let b := a-1/2
  have hb : 0 < b := sub_pos.mpr ha
  let c := 2*heat K 1*Real.exp b
  have h := strip_majorant K h0 h1 ((envelope_int hb).const_mul c) (fun x hx => by
    let u := x^(1/2:ℝ)
    have hx0 := zero_lt_one.trans hx
    have hu : 1 ≤ u := Real.one_le_rpow hx.le (by norm_num)
    have hu0 := zero_lt_one.trans_le hu
    have hu2 : u^2 = x := by
      dsimp [u]; rw [← Real.rpow_mul_natCast hx0.le]; norm_num
    have hcoef : 1+x⁻¹ ≤ 2*Real.exp ((u-1)/2)/u := by
      rw [le_div_iff₀ hu0]
      have hy : x⁻¹*u = u⁻¹ := by rw [← hu2, sq, mul_inv]; field_simp
      have hv : u⁻¹ ≤ 1 := (inv_le_one₀ hu0).mpr hu
      linarith [Real.add_one_le_exp ((u-1)/2), show (1+x⁻¹)*u = u+u⁻¹ by rw [add_mul, one_mul, hy]]
    have hH := contraction K zero_lt_one hx.le
    rw [Real.one_rpow] at hH
    have hdec : heat K x ≤ Real.exp (-a*(u-1))*heat K 1 := by
      apply hH.trans (mul_le_mul_of_nonneg_right _ (heat_nonneg K _))
      apply Real.exp_le_exp.mpr
      have hu' : u ≤ x^(exponent K) := Real.rpow_le_rpow_of_exponent_le hx.le he
      linarith only [mul_le_mul hal (sub_le_sub_right hu' 1) (sub_nonneg.mpr hu)
        (GeneralHeat.rate_pos K).le, show -a*(u-1) = -(a*(u-1)) by ring]
    have hcoeff0 : 0 ≤ 1+x⁻¹ := by positivity
    have hle := mul_le_mul hcoef hdec (heat_nonneg K x) (hcoeff0.trans hcoef)
    have hexp : Real.exp ((u-1)/2)*Real.exp (-a*(u-1)) = Real.exp b*Real.exp (-b*u) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; dsimp [b]; ring
    change (1+x⁻¹)*heat K x ≤ c*envelope b x
    apply hle.trans_eq
    calc (2*Real.exp ((u-1)/2)/u)*(Real.exp (-a*(u-1))*heat K 1) =
           2*heat K 1*u⁻¹*(Real.exp ((u-1)/2)*Real.exp (-a*(u-1))) := by ring
         _ = _ := by rw [hexp, envelope, Real.rpow_neg hx0.le]; dsimp [c, u]; ring)
  rw [integral_const_mul, envelope_mass hb, Real.exp_neg] at h
  have hval : c*(2*(Real.exp b)⁻¹/b) = 4*heat K 1/b := by
    dsimp [c]; field_simp [(Real.exp_pos b).ne']; ring
  rwa [hval] at h

abbrev Fifth := CyclotomicField 5 ℚ

theorem fifth_invariants : Module.finrank ℚ Fifth = 4 ∧ discr Fifth = 125 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let A : Algebra ℚ Fifth := DivisionRing.toRatAlgebra
  have hc : @IsCyclotomicExtension {5} ℚ Fifth _ _ A := by
    rw [Subsingleton.elim A (CyclotomicField.algebra 5 ℚ)]; infer_instance
  let : @IsCyclotomicExtension {5} ℚ Fifth _ _ DivisionRing.toRatAlgebra := hc
  constructor
  · rw [IsCyclotomicExtension.Rat.finrank 5 Fifth]; decide
  · rw [IsCyclotomicExtension.Rat.discr_prime 5 Fifth]; norm_num

private theorem fifth_rates : exponent Fifth = 1/2 ∧ 15/8 ≤ slopeRate Fifth ∧
    15/4 ≤ GeneralHeat.rate Fifth := by
  obtain ⟨hd, hdisc⟩ := fifth_invariants
  have hd' : degree Fifth = 4 := by unfold degree; rw [hd]; norm_num
  have he : exponent Fifth = 1/2 := by rw [exponent, hd']; norm_num
  have hroot : (125:ℝ)^(1/4:ℝ) ≤ 67/20 := by
    apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg (by norm_num) _) (by norm_num) (by decide : (4:ℕ) ≠ 0)).mp
    rw [← Real.rpow_mul_natCast (by norm_num)]
    norm_num
  have hq : 15/8 ≤ slopeRate Fifth := by
    rw [slopeRate_eq, hdisc, hd']
    change 15/8 ≤ 2*Real.pi/(125:ℝ)^(1/4:ℝ)
    rw [le_div_iff₀ (Real.rpow_pos_of_pos (by norm_num) _)]
    linarith [Real.pi_gt_d4]
  refine ⟨he, hq, ?_⟩
  rw [slopeRate, he] at hq
  linarith

theorem fifth_zero_height {s : ℂ} (hz : s ∈ zeros Fifth) (h0 : 0 < s.re) :
    (21/16:ℝ)^2 < s.im^2 := by
  obtain ⟨he,hq,hl⟩ := fifth_rates
  have h1 := zeros_left Fifth hz
  have hM := sqrt_moment Fifth he.ge (by norm_num) hl h0.le h1.le
  norm_num at hM
  have hL := self_dual_residue Fifth
  have hL' : (2*(15/8)-1)*heat Fifth 1 ≤ ‖cst Fifth‖ :=
    (mul_le_mul_of_nonneg_right (by linarith : 2*(15/8)-1 ≤ 2*slopeRate Fifth-1)
      (heat_nonneg Fifth 1)).trans hL
  have hp := height_of_product h0 h1
  have hC := norm_pos_iff.mpr (cst_ne Fifth)
  by_contra! him
  have hbound : ‖s‖*‖s-1‖ ≤ (21/16:ℝ)^2+1/2 := by linarith
  have hu := mul_le_mul hbound hM (norm_nonneg _) (by norm_num)
  rw [product_at_zero Fifth hz h0] at hu
  linarith

theorem fifth_radius {t : ℝ} (ht : |t| ≤ 3/16) :
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ, ENNReal.ofReal (3/2) < p.radius ∧
      ReciprocalRadius.InverseGerm Fifth t p := by
  refine radius_from_height Fifth (T := 21/16) (by norm_num) (fun _ => fifth_zero_height)
    (by linarith) ?_
  have hm : 9/8 ≤ 21/16-|t| := by linarith
  have := (sq_le_sq₀ (by norm_num) (by linarith : 0 ≤ 21/16-|t|)).mpr hm
  linarith

#print axioms sqrt_moment
#print axioms fifth_invariants
#print axioms fifth_zero_height
#print axioms fifth_radius
end OMA.QuarticDisk
