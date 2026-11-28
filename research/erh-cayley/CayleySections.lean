import CayleyHigher
import Mathlib.Analysis.Complex.TaylorSeries

/-! Uniform Taylor truncation on the open disk and finite-degree certificates
for individual closed subdisks. The field-dependent constant is existential. -/
noncomputable section
namespace OMA.CayleySections
open Complex Set Filter Metric NumberField CayleyBounds CayleyRecurrence CayleySmoothing CayleyHigher ExactRadius
open scoped Topology
variable (K : Type*) [Field K] [NumberField K]

def taylorPoly (a : ℕ → ℂ) (L : ℕ) (w : ℂ) := ∑ j ∈ Finset.range L, a j * w^j
abbrev poly := taylorPoly (difference^[order K] (b K))

theorem taylor_sum {w : ℂ} (hw : ‖w‖ < 1) :
    HasSum (fun j => (difference^[order K] (b K)) j*w^j) (damp (entireReg K) (order K) w) := by
  have h := (damp_analytic _ (entireReg_diff K) (order K)).differentiableOn
  apply (Complex.hasSum_taylorSeries_on_ball h (mem_ball_zero_iff.mpr hw)).congr_fun
  intro j
  rw [← difference_formula K]
  simp only [coeff,smul_eq_mul,sub_zero,div_eq_mul_inv]
  ring

theorem tail_of_decay (a : ℕ → ℂ) {H : ℂ → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hcoeff : ∀ n : ℕ, ‖a (n+2)‖ ≤ M/(((n:ℝ)+1)*(n+2)))
    (hsum : ∀ w : ℂ, ‖w‖ < 1 → HasSum (fun j => a j*w^j) (H w)) :
    ∀ (N : ℕ) (w : ℂ), ‖w‖ < 1 → ‖H w-taylorPoly a (N+2) w‖ ≤ M/((N:ℝ)+1) := by
  intro N w hw
  let u (j : ℕ) := a j*w^j
  let v (j : ℕ) := M/((j:ℝ)+1)
  have hpiece (j : ℕ) : ‖u (j+(N+2))‖ ≤ v (N+j)-v (N+(j+1)) := by
    rw [show j+(N+2)=(N+j)+2 by omega]
    dsimp only [u]
    rw [norm_mul,norm_pow]
    apply (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hw.le)).trans
    apply (hcoeff (N+j)).trans_eq
    dsimp only [v]
    push_cast
    field_simp
    <;> ring
  have hblock (k : ℕ) :
      (∑ j ∈ Finset.range k, ‖u (j+(N+2))‖) ≤ v N-v (N+k) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ]
      linarith only [ih,hpiece k]
  have hs : HasSum u (H w) := hsum w hw
  have ha := hs.summable.sum_add_tsum_nat_add (N+2)
  rw [hs.tsum_eq] at ha
  have ht : H w-taylorPoly a (N+2) w = ∑' j, u (j+(N+2)) := by
    change _-(∑ j ∈ Finset.range (N+2), u j) = _
    linear_combination -ha
  rw [ht]
  apply le_of_tendsto ((summable_nat_add_iff (N+2)).mpr hs.summable).hasSum.tendsto_sum_nat.norm
  apply Eventually.of_forall
  intro k
  apply (norm_sum_le _ _).trans
  have hp : 0 ≤ v (N+k) := div_nonneg hM (by positivity)
  exact (hblock k).trans (sub_le_self _ hp)

theorem disk_lower_iff (a : ℕ → ℂ) {H : ℂ → ℂ} {M : ℝ}
    (hc : ContinuousOn H (ball 0 1))
    (herr : ∀ (N : ℕ) (w : ℂ), ‖w‖ < 1 → ‖H w-taylorPoly a (N+2) w‖ ≤ M/((N:ℝ)+1))
    {r : ℝ} (hr : 0 ≤ r) (h1 : r < 1) :
    (∀ w : ℂ, ‖w‖ ≤ r → H w ≠ 0) ↔
      ∃ N : ℕ, ∀ w : ℂ, ‖w‖ ≤ r → M/((N:ℝ)+1) < ‖taylorPoly a (N+2) w‖ := by
  constructor
  · intro hf
    have hcont : ContinuousOn (fun w => ‖H w‖) (closedBall 0 r) :=
      (hc.mono (closedBall_subset_ball h1)).norm
    obtain ⟨v,hv,hmin⟩ := (isCompact_closedBall (0:ℂ) r).exists_isMinOn
      ⟨0,mem_closedBall_self hr⟩ hcont
    have hvr := mem_closedBall_zero_iff.mp hv
    have hv0 : 0 < ‖H v‖ := norm_pos_iff.mpr (hf v hvr)
    obtain ⟨N,hN⟩ := exists_nat_gt (2*M/‖H v‖)
    have hs : 2*(M/((N:ℝ)+1)) < ‖H v‖ := by
      have h := (div_lt_iff₀ hv0).mp hN
      rw [mul_div_assoc',div_lt_iff₀ (by positivity : 0 < (N:ℝ)+1)]
      nlinarith only [h,hv0]
    refine ⟨N,?_⟩
    intro w hw
    have hl := (isMinOn_iff.mp hmin) w (mem_closedBall_zero_iff.mpr hw)
    have ht := norm_add_le (H w-taylorPoly a (N+2) w) (taylorPoly a (N+2) w)
    rw [sub_add_cancel] at ht
    change ‖H v‖ ≤ ‖H w‖ at hl
    have he := herr N w (hw.trans_lt h1)
    linarith
  · rintro ⟨N,hp⟩ w hw hzero
    have he := herr N w (hw.trans_lt h1)
    rw [hzero,zero_sub,norm_neg] at he
    exact (hp w hw).not_ge he

theorem uniform_tail : ∃ M : ℝ, 0 ≤ M ∧ ∀ (N : ℕ) (w : ℂ), ‖w‖ < 1 →
    ‖damp (entireReg K) (order K) w-poly K (N+2) w‖ ≤ M/((N:ℝ)+1) := by
  obtain ⟨M,hM,hcoeff⟩ := decay K
  exact ⟨M,hM,tail_of_decay _ hM hcoeff (fun _ hw => taylor_sum K hw)⟩

theorem subdisk_certificate :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ r : ℝ, 0 ≤ r → r < 1 →
      ((∀ w : ℂ, ‖w‖ ≤ r → entireReg K (point w) ≠ 0) ↔
        ∃ N : ℕ, ∀ w : ℂ, ‖w‖ ≤ r → M/((N:ℝ)+1) < ‖poly K (N+2) w‖) := by
  obtain ⟨M,hM,herr⟩ := uniform_tail K
  refine ⟨M,hM,fun r hr h1 => ?_⟩
  have hc := (damp_analytic _ (entireReg_diff K) (order K)).continuousOn
  exact (forall_congr' fun w => forall_congr' fun hw =>
    not_congr (damp_zero_iff K (m := order K) (hw.trans_lt h1)).symm).trans
    (disk_lower_iff _ hc herr hr h1)

#print axioms taylor_sum
#print axioms tail_of_decay
#print axioms disk_lower_iff
#print axioms uniform_tail
#print axioms subdisk_certificate
end OMA.CayleySections
