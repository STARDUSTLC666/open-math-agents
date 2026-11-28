import FoldedPhase
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.MellinInversion

/-! Uniform Riemann-Lebesgue decay on the whole closed critical strip.
The horizontal Lipschitz constant is independent of the imaginary part. -/
noncomputable section
namespace OMA.VerticalDecay
open Complex NumberField Set Filter Metric MeasureTheory
open FoldedPhase ThetaContinuation GeneralHeat
open scoped Topology FourierTransform
variable (K : Type*) [Field K] [NumberField K]

theorem fixed_line (a : ℝ) :
    Tendsto (fun t : ℝ => (pair K).Λ₀ ⟨a,t⟩) (cocompact ℝ) (𝓝 0) := by
  let g := fun u : ℝ => Real.exp (-a*u) • (pair K).f_modif (Real.exp (-u))
  have hscale := (Homeomorph.mulRight₀ ((2*Real.pi)⁻¹) (inv_ne_zero
    (mul_ne_zero two_ne_zero Real.pi_ne_zero))).isClosedEmbedding.tendsto_cocompact
  have h := (Real.zero_at_infty_fourier g).comp hscale
  convert h using 1
  funext t
  rw [WeakFEPair.Λ₀, mellin_eq_fourier]
  rfl

private theorem exp_gap_of_le {a b : ℝ} (hab : a ≤ b) (hb : b ≤ 0) :
    Real.exp b - Real.exp a ≤ b-a := by
  have hf : Real.exp b - Real.exp a = Real.exp b*(1-Real.exp (a-b)) := by
    rw [mul_sub, mul_one, ← Real.exp_add, add_sub_cancel]
  rw [hf]
  have hn := sub_nonneg.mpr (Real.exp_le_one_iff.mpr (sub_nonpos.mpr hab))
  have h := mul_le_of_le_one_left hn (Real.exp_le_one_iff.mpr hb)
  linarith [Real.add_one_le_exp (a-b)]

private theorem exp_gap {a b : ℝ} (ha : a ≤ 0) (hb : b ≤ 0) :
    |Real.exp a-Real.exp b| ≤ |a-b| := by
  rcases le_total a b with h | h
  · rw [abs_sub_comm, abs_sub_comm a b, abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr h)),
      abs_of_nonneg (sub_nonneg.mpr h)]
    exact exp_gap_of_le h hb
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr h)), abs_of_nonneg (sub_nonneg.mpr h)]
    exact exp_gap_of_le h ha

private theorem power_gap {x a b : ℝ} (hx : 1 < x) (ha : a ≤ 1) (hb : b ≤ 1) :
    |x^(a-1)-x^(b-1)| ≤ |a-b| * x := by
  have hx0 := zero_lt_one.trans hx
  have hlog := Real.log_nonneg hx.le
  rw [Real.rpow_def_of_pos hx0, Real.rpow_def_of_pos hx0]
  apply (exp_gap (mul_nonpos_of_nonneg_of_nonpos hlog (sub_nonpos.mpr ha))
    (mul_nonpos_of_nonneg_of_nonpos hlog (sub_nonpos.mpr hb))).trans
  rw [show Real.log x*(a-1)-Real.log x*(b-1)=(a-b)*Real.log x by ring,
    abs_mul, abs_of_nonneg hlog]
  exact mul_le_mul_of_nonneg_left (by linarith [Real.log_le_sub_one_of_pos hx0]) (abs_nonneg _)

private theorem split_integrand (a t : ℝ) {x : ℝ} (hx : 1 < x) :
    integrand K ⟨a,t⟩ x = ((x^(a-1):ℝ):ℂ) * ((x:ℂ)^((t:ℂ)*I) * (heat K x:ℂ)) := by
  have hx0 := zero_lt_one.trans hx
  have he : (⟨a,t⟩:ℂ)-1 = ((a-1:ℝ):ℂ) + (t:ℂ)*I := by apply Complex.ext <;> simp
  rw [integrand, he, cpow_add _ _ (ofReal_ne_zero.mpr hx0.ne'), ← ofReal_cpow hx0.le]
  have hv : (pair K).f_modif x = (heat K x:ℂ) := by
    simp [WeakFEPair.f_modif, hx, hx.not_gt, pair, kernel_eq K hx0]
  rw [hv, mul_assoc]

private theorem half_lipschitz (t : ℝ) {x a b : ℝ} (hx : 1 < x) (ha : a ≤ 1) (hb : b ≤ 1) :
    ‖integrand K ⟨a,t⟩ x - integrand K ⟨b,t⟩ x‖ ≤ |a-b| * (x*heat K x) := by
  have hn : ‖(x:ℂ)^((t:ℂ)*I)‖ = 1 := by rw [norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hx)]; simp
  rw [split_integrand K a t hx, split_integrand K b t hx, ← sub_mul, ← ofReal_sub, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, norm_mul, hn, one_mul, Complex.norm_of_nonneg (heat_nonneg K x)]
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (power_gap hx ha hb) (heat_nonneg K x)

private theorem heat_int : IntegrableOn (fun x : ℝ => x*heat K x) (Ioi 1) := by
  have hi := (integrand_int K 2).mono_set (Ioi_subset_Ioi (zero_le_one : (0:ℝ) ≤ 1))
  have hr : IntegrableOn (fun x => (integrand K 2 x).re) (Ioi 1) := hi.re
  apply hr.congr_fun _ measurableSet_Ioi
  intro x hx
  change 1 < x at hx
  simp [integrand, show (2:ℂ)-1 = 1 by norm_num, WeakFEPair.f_modif, hx, hx.not_gt,
    pair, kernel_eq K (zero_lt_one.trans hx), mul_re]

def horizontalConstant := 2*(∫ x in Ioi 1, x*heat K x) + 1

theorem horizontal_constant_pos : 0 < horizontalConstant K := by
  have h : 0 ≤ ∫ x in Ioi 1, x*heat K x :=
    setIntegral_nonneg measurableSet_Ioi (fun x hx => mul_nonneg (zero_le_one.trans hx.le) (heat_nonneg K x))
  unfold horizontalConstant
  linarith

theorem horizontal_lipschitz (t : ℝ) {a b : ℝ} (ha : a ∈ Icc (0:ℝ) 1) (hb : b ∈ Icc (0:ℝ) 1) :
    ‖(pair K).Λ₀ ⟨a,t⟩-(pair K).Λ₀ ⟨b,t⟩‖ ≤ |a-b| * horizontalConstant K := by
  let f (u : ℝ) (x : ℝ) := integrand K ⟨u,t⟩ x+integrand K (1-⟨u,t⟩) x
  have hi (s : ℂ) := (integrand_int K s).mono_set (Ioi_subset_Ioi (zero_le_one : (0:ℝ) ≤ 1))
  have hf (u : ℝ) : IntegrableOn (f u) (Ioi 1) := (hi _).add (hi _)
  have href (u : ℝ) : (1:ℂ)-⟨u,t⟩ = ⟨1-u,-t⟩ := by apply Complex.ext <;> simp
  have hp (x : ℝ) (hx : x ∈ Ioi 1) : ‖f a x - f b x‖ ≤ (2*|a-b|)*(x*heat K x) := by
    dsimp only [f]
    rw [show ∀ A B C D : ℂ, (A+B)-(C+D)=(A-C)+(B-D) by intros; ring, href a, href b]
    apply (norm_add_le _ _).trans
    have h₁ := half_lipschitz K t hx ha.2 hb.2
    have h₂ := half_lipschitz K (-t) (a := 1-a) (b := 1-b) hx (by linarith [ha.1]) (by linarith [hb.1])
    rw [show 1-a-(1-b)=b-a by ring, abs_sub_comm b a] at h₂
    linarith
  rw [folded K ⟨a,t⟩, folded K ⟨b,t⟩]
  change ‖(∫ x in Ioi 1, f a x)-(∫ x in Ioi 1, f b x)‖ ≤ _
  rw [← integral_sub (hf a) (hf b)]
  apply (norm_integral_le_integral_norm (μ := volume.restrict (Ioi 1)) _).trans
  have h := setIntegral_mono_on ((hf a).sub (hf b)).norm ((heat_int K).const_mul (2*|a-b|))
    measurableSet_Ioi hp
  rw [integral_const_mul] at h
  apply h.trans
  have he : 2*|a-b| * (∫ x in Ioi 1, x*heat K x) = |a-b| * (2*(∫ x in Ioi 1, x*heat K x)) := by ring
  rw [horizontalConstant, mul_add, mul_one, he]
  exact le_add_of_nonneg_right (abs_nonneg _)

/-- Both signs of the imaginary part, uniformly for 0 ≤ Re(s) ≤ 1. -/
theorem uniform_strip {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in cocompact ℝ, ∀ a ∈ Icc (0:ℝ) 1, ‖(pair K).Λ₀ ⟨a,t⟩‖ < ε := by
  let C := horizontalConstant K
  have hC : 0 < C := horizontal_constant_pos K
  let δ := (ε/2)/C
  have hδ : 0 < δ := div_pos (half_pos hε) hC
  obtain ⟨S, hsub, hfin, hcover⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).finite_cover_balls hδ
  have hlocal (a : ℝ) : ∀ᶠ t : ℝ in cocompact ℝ, ‖(pair K).Λ₀ ⟨a,t⟩‖ < ε/2 := by
    simpa [dist_eq_norm] using (Metric.tendsto_nhds.mp (fixed_line K a) (ε/2) (half_pos hε))
  have hall := hfin.eventually_all.mpr (fun a (_ : a ∈ S) => hlocal a)
  filter_upwards [hall] with t ht a ha
  obtain ⟨b, hb, hab⟩ := mem_iUnion₂.mp (hcover ha)
  have hab' : |a-b| < δ := by simpa [Real.dist_eq] using (mem_ball.mp hab)
  have hclose : |a-b| * C < ε/2 := (lt_div_iff₀ hC).mp hab'
  have h := horizontal_lipschitz K t ha (hsub hb)
  calc ‖(pair K).Λ₀ ⟨a,t⟩‖ ≤ ‖(pair K).Λ₀ ⟨a,t⟩-(pair K).Λ₀ ⟨b,t⟩‖+‖(pair K).Λ₀ ⟨b,t⟩‖ :=
           norm_le_norm_sub_add _ _
       _ < ε := by linarith [h.trans_lt hclose, ht b hb]

#print axioms fixed_line
#print axioms horizontal_lipschitz
#print axioms uniform_strip
end OMA.VerticalDecay
