import ReciprocalRadius
import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.NumberTheory.LSeries.Injectivity

/-! Simultaneous vertical returns of the absolutely convergent ideal series. -/
noncomputable section
namespace OMA.CayleyReturn
open Complex Filter Metric Set NumberField ReciprocalRadius
open scoped Topology

def shift (x : ℝ) (n : ℕ) : ℂ := (x:ℂ)+(n:ℂ)*I

private def phase (m : ℕ) : Circle :=
  if h : m = 0 then 1 else
    ⟨(m:ℂ)^(-I), mem_sphere_zero_iff_norm.mpr (by
      have hp : 0 < (m:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h
      simpa using norm_cpow_eq_rpow_re_of_pos hp (-I))⟩

private theorem vertical_factor (m n : ℕ) {x : ℝ} (hx : 1 < x) :
    (m:ℂ)^(-shift x n) = (m:ℂ)^(-(x:ℂ))*((phase m:ℂ)^n) := by
  by_cases hm : m = 0
  · subst m
    have h0 : -(x:ℂ) ≠ 0 := neg_ne_zero.mpr (ofReal_ne_zero.mpr (by linarith))
    have hs : -shift x n ≠ 0 := neg_ne_zero.mpr (ne_zero_of_re_pos (by simpa [shift] using zero_lt_one.trans hx))
    simp [hs,h0]
  · have he : -shift x n = -(x:ℂ)+(-I)*(n:ℂ) := by dsimp [shift]; ring
    rw [he,cpow_add _ _ (Nat.cast_ne_zero.mpr hm),cpow_mul_nat]
    simp [phase,hm]

theorem common_heights :
    ∃ u : ℕ → ℕ, StrictMono u ∧
      ∀ (K : Type) [Field K] [NumberField K] (x : ℝ), 1 < x →
        Tendsto (fun n => dedekindZeta K (shift x (u n))) atTop (𝓝 (dedekindZeta K (x:ℂ))) := by
  obtain ⟨u,hu,hpow⟩ := (mapClusterPt_one_atTop_pow phase).tendsto_subseq
  have hphase (m : ℕ) : Tendsto (fun n => (phase m : ℂ)^u n) atTop (𝓝 1) := by
    have hcoord : Tendsto (fun n => phase m ^ u n) atTop (𝓝 (1:Circle)) := by
      simpa [Function.comp_def] using (continuous_apply m).continuousAt.tendsto.comp hpow
    change Tendsto ((fun z : Circle => (z:ℂ)) ∘ (fun n => phase m ^ u n)) atTop (𝓝 ((1:Circle):ℂ))
    exact continuous_subtype_val.continuousAt.tendsto.comp hcoord
  refine ⟨u,hu,?_⟩
  intro K _ _ x hx
  have he (n : ℕ) : (∑' J, weight K (shift x (u n)) J) = dedekindZeta K (shift x (u n)) :=
    sum_eq_zeta K (by simpa [shift] using hx)
  simp_rw [← he,← sum_eq_zeta K (s := (x:ℂ)) hx]
  apply tendsto_tsum_of_dominated_convergence (norm_summable K (s := (x:ℂ)) hx)
  · intro J
    have ht := (hphase J.absNorm).const_mul (weight K (x:ℂ) J)
    simpa only [weight,vertical_factor _ _ hx,mul_one] using ht
  · exact Eventually.of_forall fun n J => by simp [weight,vertical_factor _ _ hx,norm_pow,Circle.norm_coe]

theorem real_limit (K : Type*) [Field K] [NumberField K] :
    Tendsto (fun x : ℝ => dedekindZeta K (x:ℂ)) atTop (𝓝 1) := by
  have hab := LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    (f := fun n => (a K n:ℂ)) (x := (1:ℝ)) (fun y hy => series_summable K (s := (y:ℂ)) hy)
  have hlim := LSeries.tendsto_atTop (lt_of_le_of_lt hab (EReal.coe_lt_top _))
  have hf : a K 1 = 1 := by
    simpa [a,fiber,Ideal.absNorm_eq_one_iff] using (Nat.card_unique (α := ({⊤} : Set (Ideal (𝓞 K)))))
  simpa [dedekindZeta,a,fiber] using (show Tendsto (fun x : ℝ => LSeries (fun n => (a K n:ℂ)) x)
    atTop (𝓝 (1:ℂ)) by simpa only [hf,Nat.cast_one] using hlim)

theorem large_real (K : Type*) [Field K] [NumberField K] (A : ℝ) :
    ∃ x : ℝ, 1 < x ∧ A < ‖dedekindZeta K (x:ℂ)‖ := by
  by_contra! h
  have hx : Tendsto (fun x : ℝ => x) (𝓝[>] 1) (𝓝 1) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hz : Tendsto (fun x : ℝ => (x-1)*A) (𝓝[>] 1) (𝓝 0) := by
    simpa using (hx.sub_const 1).mul_const A
  have hs : ∀ᶠ x : ℝ in 𝓝[>] 1, ‖((x-1:ℝ):ℂ)*dedekindZeta K (x:ℂ)‖ ≤ (x-1)*A := by
    filter_upwards [self_mem_nhdsWithin] with x (h1 : 1 < x)
    rw [norm_mul,Complex.norm_of_nonneg (sub_nonneg.mpr h1.le)]
    exact mul_le_mul_of_nonneg_left (h x h1) (sub_nonneg.mpr h1.le)
  have hle := le_of_tendsto_of_tendsto (tendsto_sub_one_mul_dedekindZeta_nhdsGT K).norm hz (by
    filter_upwards [hs] with x he
    simpa only [ofReal_sub,ofReal_one] using he)
  exact (norm_pos_iff.mpr (ofReal_ne_zero.mpr (dedekindZeta_residue_ne_zero K))).not_ge hle

#print axioms common_heights
#print axioms real_limit
#print axioms large_real
end OMA.CayleyReturn
