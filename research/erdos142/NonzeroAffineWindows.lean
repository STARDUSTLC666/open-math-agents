import FormalConjectures.ErdosProblems.«142»
import Mathlib

/-!
# Genuine arithmetic progressions in affine windows of a prime cyclic group

Event contribution by @STARDUSTLC666 for the finite counting task in desk plan #151553.
The two interval lemmas below are from the merged #142 reductions lower.R2.H1.R1
and lower.R3 at 2c794d365a153e7fc59e62956e54a3f42d0d0962. The definitions and the
window_bound, place_bijective, total_occupancy and total_patterns proofs are
from @futurum-dev's desk notes #174105 and #174148. They are included here so
the nonzero-step refinement can be checked using only the pinned problem import.
-/

namespace Erdos142.FiniteWindows

open Finset

lemma free_of_noAP {V : Finset ℕ} {k : ℕ} (hk : 1 < k)
    (hno : ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ V) :
    (V : Set ℕ).IsAPOfLengthFree k := by
  have hk' : (1 : ℕ∞) < (k : ℕ∞) := by exact_mod_cast hk
  intro T hsub hT
  obtain ⟨a, d, hcard, hterms⟩ := hT
  have hmem (i : ℕ) (hi : i < k) : a + i * d ∈ T := by
    rw [hterms]
    exact ⟨i, by exact_mod_cast hi, by simp⟩
  have hd : 0 < d := by
    by_contra! h
    have he : d = 0 := Nat.eq_zero_of_le_zero h
    have hs : T = {a} := by
      apply Set.Subset.antisymm
      · rw [hterms, he]
        rintro _ ⟨i, -, rfl⟩
        simp
      · apply Set.singleton_subset_iff.mpr
        simpa using hmem 0 (by omega)
    rw [hs] at hcard
    exact hk'.ne (by simpa using hcard)
  exact (hno ⟨a, d, hd, fun i hi => hsub (hmem i hi)⟩).elim

lemma card_le_r {k N : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 N)
    (hf : (S : Set ℕ).IsAPOfLengthFree k) : S.card ≤ r k N := by
  unfold r Set.IsAPOfLengthFree.maxCard
  refine le_csSup ?_ ⟨S, hS, hf, rfl⟩
  refine ⟨N, ?_⟩
  rintro _ ⟨U, hU, -, rfl⟩
  simpa using Finset.card_le_card hU

/-- All positive-step progressions inside the short interval, indexed by start and step. -/
def patterns (k M : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 M) ×ˢ (Icc 1 M)).filter fun v ↦ v.1 + (k-1)*v.2 ≤ M

/-- The ordered progressions counted in the event, including zero common difference. -/
def progressions {p : ℕ} [NeZero p] (k : ℕ) (A : Finset (ZMod p)) :
    Finset (ZMod p × ZMod p) :=
  univ.filter fun u ↦ ∀ i : Fin k, u.1 + (i.val : ZMod p) * u.2 ∈ A

def affine {p : ℕ} (u : ZMod p × ZMod p) (j : ℕ) : ZMod p := u.1 + (j : ZMod p)*u.2

def place {p : ℕ} (v : ℕ × ℕ) (u : ZMod p × ZMod p) : ZMod p × ZMod p :=
  (affine u v.1, (v.2 : ZMod p)*u.2)

/-- Removing the start of every represented pattern leaves an independent set. -/
theorem window_bound {k M p : ℕ} [NeZero p] (hk : 1 < k)
    (A : Finset (ZMod p)) (u : ZMod p × ZMod p) :
    ((Icc 1 M).filter fun j ↦ affine u j ∈ A).card ≤ r k M +
      ((patterns k M).filter fun v ↦ place v u ∈ progressions k A).card := by
  classical
  let S := (Icc 1 M).filter fun j ↦ affine u j ∈ A
  let P := (patterns k M).filter fun v ↦ place v u ∈ progressions k A
  let B := P.image Prod.fst
  have hfree : ((S \ B : Finset ℕ) : Set ℕ).IsAPOfLengthFree k := by
    apply free_of_noAP hk
    rintro ⟨a,d,hd,h⟩
    have ha : a ∈ S \ B := by simpa using h 0 (by omega)
    have hlast := (mem_Icc.mp (mem_filter.mp (mem_sdiff.mp (h (k-1) (by omega))).1).1).2
    have hsecond := (mem_Icc.mp (mem_filter.mp (mem_sdiff.mp (h 1 hk)).1).1).2
    have haI := (mem_filter.mp (mem_sdiff.mp ha).1).1
    simp only [one_mul] at hsecond
    have hdM : d ≤ M := by omega
    have hv : (a,d) ∈ patterns k M :=
      mem_filter.mpr ⟨mem_product.mpr ⟨haI, mem_Icc.mpr ⟨hd,hdM⟩⟩,hlast⟩
    have hw : (a,d) ∈ P := by
      apply mem_filter.mpr
      refine ⟨hv,mem_filter.mpr ⟨mem_univ _,?_⟩⟩
      intro i
      have he := (mem_filter.mp (mem_sdiff.mp (h i i.isLt)).1).2
      change affine u (a + (i:ℕ)*d) ∈ A at he
      convert he using 1
      simp [place, affine]
      ring
    exact (mem_sdiff.mp ha).2 (mem_image.mpr ⟨(a,d),hw,rfl⟩)
  have hrem := card_le_r (k := k) (N := M) (S := S \ B)
    (fun j hj ↦ (mem_filter.mp (mem_sdiff.mp hj).1).1) hfree
  have hb : B.card ≤ P.card := card_image_le
  have hcut := le_card_sdiff B S
  change S.card ≤ r k M + P.card
  omega

/-- A short pattern maps affine parameters bijectively onto ordered cyclic pairs. -/
theorem place_bijective {p k M : ℕ} [Fact p.Prime] (hM : M < p)
    {v : ℕ × ℕ} (hv : v ∈ patterns k M) : Function.Bijective (place (p := p) v) := by
  have hd := mem_Icc.mp (mem_product.mp (mem_filter.mp hv).1).2
  have hne : (v.2 : ZMod p) ≠ 0 := by
    intro h
    have := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt (lt_of_le_of_lt hd.2 hM), ZMod.val_zero] at this
    omega
  constructor
  · rintro ⟨a,d⟩ ⟨b,e⟩ heq
    have hh : (v.2 : ZMod p)*d = (v.2 : ZMod p)*e := congrArg Prod.snd heq
    have he := mul_left_cancel₀ hne hh
    subst e
    have hfst : a + (v.1 : ZMod p)*d = b + (v.1 : ZMod p)*d := congrArg Prod.fst heq
    rw [add_right_cancel hfst]
  · rintro ⟨a,d⟩
    refine ⟨(a - (v.1 : ZMod p)*(d/v.2), d/v.2), ?_⟩
    ext <;> simp [place, affine, hne, mul_div_cancel₀]

theorem total_occupancy {p : ℕ} [NeZero p] (M : ℕ) (A : Finset (ZMod p)) :
    (∑ u : ZMod p × ZMod p, ((Icc 1 M).filter fun j ↦ affine u j ∈ A).card) =
      M*p*A.card := by
  classical
  simp only [card_filter]
  rw [sum_comm]
  have fixed (j : ℕ) : (∑ u : ZMod p × ZMod p, if affine u j ∈ A then 1 else 0) = p*A.card := by
    rw [Fintype.sum_prod_type_right]
    have row (d : ZMod p) : (∑ a : ZMod p, if a + (j : ZMod p)*d ∈ A then 1 else 0) = A.card := by
      calc
        _ = ∑ a : ZMod p, if a ∈ A then 1 else 0 :=
          Equiv.sum_comp (Equiv.addRight ((j : ZMod p)*d)) (fun a ↦ if a ∈ A then 1 else 0)
        _ = A.card := by simp
    change (∑ d : ZMod p, ∑ a : ZMod p, if a + (j : ZMod p)*d ∈ A then 1 else 0) = _
    simp_rw [row]
    simp [ZMod.card]
  simp [fixed, Nat.mul_assoc]

theorem total_patterns {p k M : ℕ} [Fact p.Prime] (hM : M < p) (A : Finset (ZMod p)) :
    (∑ u : ZMod p × ZMod p, ((patterns k M).filter fun v ↦ place v u ∈ progressions k A).card) =
      (patterns k M).card * (progressions k A).card := by
  classical
  simp only [card_filter]
  rw [sum_comm]
  have fixed (v : ℕ × ℕ) (hv : v ∈ patterns k M) :
      (∑ u : ZMod p × ZMod p, if place v u ∈ progressions k A then 1 else 0) =
        (progressions k A).card := by
    calc
      _ = ∑ u : ZMod p × ZMod p, if u ∈ progressions k A then 1 else 0 :=
        (place_bijective hM hv).sum_comp (fun u ↦ if u ∈ progressions k A then 1 else 0)
      _ = _ := by simp
  rw [sum_congr rfl fixed]
  simp

/-- Ordered arithmetic progressions with nonzero common difference. -/
def genuine {p : ℕ} [NeZero p] (k : ℕ) (A : Finset (ZMod p)) :
    Finset (ZMod p × ZMod p) := (progressions k A).filter fun u => u.2 ≠ 0

private lemma constant_mem {p k : ℕ} [NeZero p] (hk : 0 < k)
    (A : Finset (ZMod p)) (a : ZMod p) : (a,0) ∈ progressions k A ↔ a ∈ A := by
  constructor
  · intro h
    simpa using (mem_filter.mp h).2 (⟨0,hk⟩ : Fin k)
  · intro h
    exact mem_filter.mpr ⟨mem_univ _,fun _ => by simpa using h⟩

theorem progressions_card {p k : ℕ} [NeZero p] (hk : 0 < k) (A : Finset (ZMod p)) :
    (progressions k A).card = (genuine k A).card + A.card := by
  classical
  have diag : ((progressions k A).filter fun u => u.2 = 0) = A ×ˢ {0} := by
    ext ⟨a,d⟩
    by_cases hd : d = 0
    · simp [hd,constant_mem hk A]
    · simp [hd,Ne.symm hd]
  have split := card_filter_add_card_filter_not (s := progressions k A) (fun u => u.2 = 0)
  rw [diag] at split
  simpa [genuine,Nat.add_comm] using split.symm

private lemma split_slopes {p : ℕ} [NeZero p] (f : ZMod p × ZMod p → ℕ) :
    (∑ u, f u) =
      (∑ d ∈ (univ : Finset (ZMod p)).erase 0, ∑ a, f (a,d)) + ∑ a, f (a,0) := by
  rw [Fintype.sum_prod_type_right]
  exact (sum_erase_add _ _ (mem_univ (0 : ZMod p))).symm

/-- Occupied positions in the short interval for an affine map. -/
def occupied {p : ℕ} (M : ℕ) (A : Finset (ZMod p)) (u : ZMod p × ZMod p) : Finset ℕ :=
  (Icc 1 M).filter fun j => affine u j ∈ A

private def localPatterns {p : ℕ} [NeZero p] (k M : ℕ) (A : Finset (ZMod p))
    (u : ZMod p × ZMod p) : ℕ :=
  ((patterns k M).filter fun v => place v u ∈ progressions k A).card

def sumNonzeroSlopes {p : ℕ} [NeZero p] (f : ZMod p × ZMod p → ℕ) : ℕ :=
  ∑ d ∈ (univ : Finset (ZMod p)).erase 0, ∑ a, f (a,d)

private lemma nonzero_totals {p k M : ℕ} [Fact p.Prime] (hk : 1 < k) (hM : M < p)
    (A : Finset (ZMod p)) :
    sumNonzeroSlopes (fun u => (occupied M A u).card) = (p-1)*(M*A.card) ∧
    sumNonzeroSlopes (localPatterns k M A) = (patterns k M).card*(genuine k A).card := by
  classical
  let W (u : ZMod p × ZMod p) := (occupied M A u).card
  let D := localPatterns k M A
  have w0 : (∑ a, W (a,0)) = M*A.card := by
    have each (a : ZMod p) : W (a,0) = if a ∈ A then M else 0 := by
      by_cases ha : a ∈ A <;> simp [W,occupied,affine,ha]
    simp [each,Nat.mul_comm]
  have d0 : (∑ a, D (a,0)) = (patterns k M).card*A.card := by
    have each (a : ZMod p) : D (a,0) = if a ∈ A then (patterns k M).card else 0 := by
      by_cases ha : a ∈ A <;> simp [D,localPatterns,place,affine,constant_mem (by omega : 0 < k) A,ha]
    simp [each,Nat.mul_comm]
  have hp : p-1+1 = p := Nat.sub_add_cancel (Fact.out : p.Prime).one_le
  have wa : sumNonzeroSlopes W + M*A.card = M*p*A.card :=
    w0 ▸ ((split_slopes W).symm.trans (total_occupancy M A))
  have expand : M*p*A.card = (p-1)*(M*A.card) + M*A.card := by
    calc
      M*p*A.card = M*(p-1+1)*A.card := by rw [hp]
      _ = _ := by ring
  rw [expand] at wa
  have wn := Nat.add_right_cancel wa
  have da : sumNonzeroSlopes D + (patterns k M).card*A.card =
      (patterns k M).card*(progressions k A).card :=
    d0 ▸ ((split_slopes D).symm.trans (total_patterns hM A))
  rw [progressions_card (by omega : 0 < k) A,Nat.mul_add] at da
  exact ⟨wn,Nat.add_right_cancel da⟩

/-- The nonzero-slope affine-window inequality. Only genuine ordered APs occur on the right. -/
theorem nonzero_window_bound {p k M : ℕ} [Fact p.Prime] (hk : 1 < k) (hM : M < p)
    (A : Finset (ZMod p)) :
    (p-1)*(M*A.card) ≤ (p-1)*(p*r k M) + (patterns k M).card*(genuine k A).card := by
  classical
  let W (u : ZMod p × ZMod p) := (occupied M A u).card
  let D := localPatterns k M A
  obtain ⟨wn,dn⟩ := nonzero_totals hk hM A
  have summed : sumNonzeroSlopes W ≤
      ∑ d ∈ (univ : Finset (ZMod p)).erase 0, ∑ a : ZMod p, (r k M + D (a,d)) :=
    sum_le_sum fun d _ => sum_le_sum fun a _ => window_bound hk A (a,d)
  have count : ((univ : Finset (ZMod p)).erase 0).card = p-1 := by
    simp [ZMod.card]
  calc
    _ = sumNonzeroSlopes W := wn.symm
    _ ≤ _ := summed
    _ = (p-1)*(p*r k M) + sumNonzeroSlopes D := by
      simp [sum_add_distrib,sumNonzeroSlopes,count,ZMod.card]
    _ = _ := by rw [dn]

/-- A strict criterion for the ordered-count threshold in the event's cyclic transfer. -/
theorem strict_count {p k M : ℕ} [Fact p.Prime] (hk : 1 < k) (hM : M < p)
    (A : Finset (ZMod p))
    (h : (p-1)*(p*r k M) + (patterns k M).card*(p-A.card) < (p-1)*(M*A.card)) :
    p < (progressions k A).card := by
  by_contra! few
  rw [progressions_card (by omega : 0 < k) A] at few
  have upper := Nat.mul_le_mul_left (patterns k M).card
    (show (genuine k A).card ≤ p-A.card by omega)
  have lower := nonzero_window_bound hk hM A
  omega

/-- In Z/5Z every four-element set has four genuine and eight total ordered four-term APs. -/
theorem four_of_five : ∀ z : ZMod 5,
    (genuine 4 ((univ : Finset (ZMod 5)).erase z)).card = 4 ∧
      (progressions 4 ((univ : Finset (ZMod 5)).erase z)).card = 8 := by decide

private theorem r_four_four : r 4 4 = 3 := by
  have sub : (Icc 1 3 : Finset ℕ) ⊆ Icc 1 4 := Icc_subset_Icc_right (by decide)
  have small : ((Icc 1 3 : Finset ℕ) : Set ℕ).IsAPOfLengthFree 4 := by
    apply free_of_noAP (by decide : 1 < 4)
    rintro ⟨a,d,hd,h⟩
    have first := mem_Icc.mp (h 0 (by decide))
    have last := mem_Icc.mp (h 3 (by decide))
    omega
  have full : ((Icc 1 4 : Finset ℕ) : Set ℕ).IsAPOfLength 4 := by
    refine ⟨1,1,?_,?_⟩
    · norm_num [Set.encard_coe_eq_coe_finsetCard,Nat.card_Icc]
    · ext m
      constructor
      · intro hm
        obtain ⟨lo,hi⟩ := mem_Icc.mp (show m ∈ (Icc 1 4 : Finset ℕ) from hm)
        refine ⟨m-1,by exact_mod_cast (show m-1 < 4 by omega),?_⟩
        simp only [nsmul_eq_mul,mul_one]
        change 1 + (m-1) = m
        omega
      · rintro ⟨j,hj,rfl⟩
        have h : j < 4 := by exact_mod_cast hj
        apply mem_Icc.mpr
        simp only [nsmul_eq_mul,mul_one]
        change 1 ≤ 1+j ∧ 1+j ≤ 4
        omega
  apply le_antisymm
  · unfold r Set.IsAPOfLengthFree.maxCard
    apply csSup_le
    · exact ⟨(Icc 1 3 : Finset ℕ).card,Icc 1 3,sub,small,rfl⟩
    rintro _ ⟨S,hS,free,rfl⟩
    by_contra! big
    have same : S = Icc 1 4 := eq_of_subset_of_card_le hS
      ((by decide : (Icc 1 4 : Finset ℕ).card ≤ 4).trans big)
    subst S
    exact full.not_isAPOfLengthFree (by decide) free
  · simpa [Nat.card_Icc] using card_le_r sub small

/-- Here the genuine bound is attained, and the earlier sufficient test is at equality. -/
theorem sharp_mod_five :
    let A := (univ : Finset (ZMod 5)).erase 0
    (5-1)*(4*A.card) = (5-1)*(5*r 4 4) + (patterns 4 4).card*(genuine 4 A).card ∧
    (5-1)*(5*r 4 4) + (patterns 4 4).card*(5-A.card) < (5-1)*(4*A.card) ∧
    5*r 4 4 + (patterns 4 4).card = 4*A.card := by
  dsimp only
  rw [r_four_four]
  decide

private def samplePair {p : ℕ} (v : ℕ × ℕ) (u : ZMod p × ZMod p) : ZMod p × ZMod p :=
  (affine u v.1, affine u v.2)

-- Images of two distinct positions determine both the origin and the slope.
private lemma samplePair_bijective {p M : ℕ} [Fact p.Prime] (hM : M < p)
    {v : ℕ × ℕ} (hv : v ∈ (Icc 1 M).offDiag) : Function.Bijective (samplePair (p := p) v) := by
  obtain ⟨hi,hj,distinct⟩ := mem_offDiag.mp hv
  have diff : (v.2 : ZMod p) - v.1 ≠ 0 := by
    apply sub_ne_zero.mpr
    intro eq
    have vals := congrArg ZMod.val eq
    rw [ZMod.val_natCast_of_lt (lt_of_le_of_lt (mem_Icc.mp hj).2 hM),
        ZMod.val_natCast_of_lt (lt_of_le_of_lt (mem_Icc.mp hi).2 hM)] at vals
    exact distinct vals.symm
  constructor
  · rintro ⟨a,d⟩ ⟨b,e⟩ he
    have h1 : a + (v.1 : ZMod p)*d = b + (v.1 : ZMod p)*e := congrArg Prod.fst he
    have h2 : a + (v.2 : ZMod p)*d = b + (v.2 : ZMod p)*e := congrArg Prod.snd he
    have sides : ((v.2 : ZMod p)-v.1)*d = ((v.2 : ZMod p)-v.1)*e := by
      linear_combination h2 - h1
    obtain rfl := mul_left_cancel₀ diff sides
    exact Prod.ext (add_right_cancel h1) rfl
  · rintro ⟨x,y⟩
    let d := (y-x) / ((v.2 : ZMod p)-v.1)
    have slope : ((v.2 : ZMod p)-v.1)*d = y-x := by
      simp [d, diff, mul_div_cancel₀]
    refine ⟨(x-(v.1 : ZMod p)*d,d),Prod.ext ?_ ?_⟩
    · simp [samplePair,affine]
    · change x - (v.1 : ZMod p)*d + (v.2 : ZMod p)*d = y
      linear_combination slope

private lemma offDiag_size {α : Type*} (s : Finset α) :
    s.offDiag.card = s.card*(s.card-1) := by rw [offDiag_card,Nat.mul_sub,Nat.mul_one]

private lemma ordered_pairs_plus_diag (n : ℕ) : n*(n-1)+n = n*n := by
  cases n with
  | zero => rfl
  | succ n => simp only [Nat.add_sub_cancel]; ring

/-- Each ordered pair of distinct short positions has A.card squared images over all slopes. -/
private lemma all_window_pairs {p M : ℕ} [Fact p.Prime] (hM : M < p) (A : Finset (ZMod p)) :
    (∑ u : ZMod p × ZMod p, (occupied M A u).offDiag.card) =
      M*(M-1)*(A.card*A.card) := by
  classical
  have positions (u : ZMod p × ZMod p) : (occupied M A u).offDiag =
      (Icc 1 M).offDiag.filter fun v => samplePair v u ∈ A ×ˢ A := by
    ext v
    simp only [occupied,mem_offDiag,mem_filter,mem_product,samplePair]
    tauto
  simp_rw [positions,card_filter]
  rw [sum_comm]
  have fixed (v : ℕ × ℕ) (hv : v ∈ (Icc 1 M).offDiag) :
      (∑ u : ZMod p × ZMod p, if samplePair v u ∈ A ×ˢ A then 1 else 0) = A.card*A.card := by
    have size (s : Finset (ZMod p × ZMod p)) :
        (∑ u : ZMod p × ZMod p, if u ∈ s then 1 else 0) = s.card := by simp
    calc
      _ = ∑ u : ZMod p × ZMod p, if u ∈ A ×ˢ A then 1 else 0 :=
        (samplePair_bijective hM hv).sum_comp (fun u => if u ∈ A ×ˢ A then 1 else 0)
      _ = _ := (size _).trans (card_product _ _)
  rw [sum_congr rfl fixed]
  simp [Nat.mul_sub]

/-- Exact second factorial moment of the occupancy over nonzero slopes. -/
theorem factorial_window_moment {p M : ℕ} [Fact p.Prime] (hM : M < p) (A : Finset (ZMod p)) :
    sumNonzeroSlopes (fun u => (occupied M A u).card * ((occupied M A u).card-1)) =
      M*(M-1)*(A.card*(A.card-1)) := by
  classical
  let f (u : ZMod p × ZMod p) := (occupied M A u).card * ((occupied M A u).card-1)
  have z : (∑ a, f (a,0)) = M*(M-1)*A.card := by
    have each (a : ZMod p) : f (a,0) = if a ∈ A then M*(M-1) else 0 := by
      by_cases ha : a ∈ A <;> simp [f,occupied,affine,ha]
    simp [each,Nat.mul_comm]
  have total : (∑ u, f u) = M*(M-1)*(A.card*A.card) := by
    simpa only [f,offDiag_size] using all_window_pairs hM A
  have split : sumNonzeroSlopes f + M*(M-1)*A.card = M*(M-1)*(A.card*A.card) :=
    z ▸ ((split_slopes f).symm.trans total)
  have back : M*(M-1)*(A.card*A.card) =
      M*(M-1)*(A.card*(A.card-1)) + M*(M-1)*A.card := by
    rw [← Nat.mul_add,ordered_pairs_plus_diag]
  exact Nat.add_right_cancel (split.trans back)

/-- Weight the window deletion bound by occupancy, using its exact first two moments. -/
theorem pair_weighted_window_bound {p k M : ℕ} [Fact p.Prime] (hk : 1 < k)
    (pos : 0 < M) (hM : M < p) (A : Finset (ZMod p)) :
    (M-1)*(A.card*(A.card-1)) + (p-1)*A.card ≤
      r k M*(p-1)*A.card + (patterns k M).card*(genuine k A).card := by
  classical
  let W (u : ZMod p × ZMod p) := (occupied M A u).card
  let D := localPatterns k M A
  have pointwise (u : ZMod p × ZMod p) :
      W u*(W u-1) + W u ≤ r k M*W u + M*D u := by
    have wm : W u ≤ M := by
      simpa [W,occupied] using (card_filter_le (Icc 1 M) (fun j => affine u j ∈ A))
    rw [ordered_pairs_plus_diag]
    calc
      W u*W u ≤ (r k M+D u)*W u := Nat.mul_le_mul_right _ (window_bound hk A u)
      _ = r k M*W u + W u*D u := by ring
      _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_right _ wm) _
  have h : sumNonzeroSlopes (fun u => W u*(W u-1) + W u) ≤
      sumNonzeroSlopes (fun u => r k M*W u + M*D u) :=
    sum_le_sum fun d _ => sum_le_sum fun a _ => pointwise (a,d)
  have add (f g : ZMod p × ZMod p → ℕ) :
      sumNonzeroSlopes (fun u => f u + g u) = sumNonzeroSlopes f + sumNonzeroSlopes g := by
    simp only [sumNonzeroSlopes,sum_add_distrib]
  have scale (c : ℕ) (f : ZMod p × ZMod p → ℕ) :
      sumNonzeroSlopes (fun u => c*f u) = c*sumNonzeroSlopes f := by
    simp only [sumNonzeroSlopes,mul_sum]
  obtain ⟨first,pats⟩ := nonzero_totals hk hM A
  rw [add (fun u => W u*(W u-1)) W,add (fun u => r k M*W u) (fun u => M*D u),
    scale (r k M) W,scale M D] at h
  have second : sumNonzeroSlopes (fun u => W u*(W u-1)) = _ := factorial_window_moment hM A
  rw [second,show sumNonzeroSlopes W = _ from first,show sumNonzeroSlopes D = _ from pats] at h
  apply Nat.le_of_mul_le_mul_left _ pos
  simpa only [Nat.mul_add,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using h

/-- In modulus eleven the pair bound forces at least eight genuine APs even at negative
first-moment surplus: 4 times 8 = 32, while 11 times r_4(4) = 33. -/
theorem eight_in_eleven (A : Finset (ZMod 11)) (size : A.card = 8) : 8 ≤ (genuine 4 A).card := by
  let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
  have h := pair_weighted_window_bound (k := 4) (M := 4) (by decide) (by decide) (by decide) A
  rw [size,r_four_four,show (patterns 4 4).card = 1 by decide] at h
  omega

private lemma genuine_mem {p : ℕ} [NeZero p] (k : ℕ) (A : Finset (ZMod p)) (a d : ZMod p) :
    (a,d) ∈ genuine k A ↔ (∀ i : Fin k, a + (i.val : ZMod p)*d ∈ A) ∧ d ≠ 0 := by
  simp [genuine,progressions]

/-- A nonconstant affine change of coordinates preserves the number of genuine ordered APs. -/
theorem genuine_affine_preimage {p : ℕ} [Fact p.Prime] (k : ℕ) (x c : ZMod p) (hc : c ≠ 0)
    {S T : Finset (ZMod p)} (pull : ∀ v, x+c*v ∈ S ↔ v ∈ T) :
    (genuine k T).card = (genuine k S).card := by
  classical
  let f (u : ZMod p × ZMod p) := (x+c*u.1,c*u.2)
  have bij : Function.Bijective f := by
    constructor
    · rintro ⟨a,d⟩ ⟨b,e⟩ eq
      have left : x+c*a = x+c*b := congrArg Prod.fst eq
      have right : c*d = c*e := congrArg Prod.snd eq
      exact Prod.ext (mul_left_cancel₀ hc (add_left_cancel left)) (mul_left_cancel₀ hc right)
    · rintro ⟨a,d⟩
      exact ⟨((a-x)/c,d/c),by ext <;> simp [f,hc,mul_div_cancel₀]⟩
  have same (u : ZMod p × ZMod p) : f u ∈ genuine k S ↔ u ∈ genuine k T := by
    rcases u with ⟨a,d⟩
    change (x+c*a,c*d) ∈ genuine k S ↔ (a,d) ∈ genuine k T
    rw [genuine_mem,genuine_mem]
    have term (i : Fin k) : x+c*a+(i.val : ZMod p)*(c*d) ∈ S ↔ a+(i.val : ZMod p)*d ∈ T := by
      rw [show x+c*a+(i.val : ZMod p)*(c*d) = x+c*(a+(i.val : ZMod p)*d) by ring]
      exact pull _
    constructor
    · rintro ⟨terms,nonzero⟩
      exact ⟨fun i => (term i).mp (terms i),fun eq => nonzero (by simp [eq])⟩
    · rintro ⟨terms,nonzero⟩
      exact ⟨fun i => (term i).mpr (terms i),mul_ne_zero hc nonzero⟩
  calc
    _ = ∑ u : ZMod p × ZMod p, if f u ∈ genuine k S then 1 else 0 := by simp_rw [same]; simp
    _ = ∑ u : ZMod p × ZMod p, if u ∈ genuine k S then 1 else 0 :=
      bij.sum_comp (fun u => if u ∈ genuine k S then 1 else 0)
    _ = _ := by simp

private def triple (t : ZMod 11) : Finset (ZMod 11) := {0,1,t}

set_option maxRecDepth 10000 in
private theorem normalized_eleven : ∀ t : ZMod 11, t ≠ 0 → t ≠ 1 →
    (genuine 4 (triple t)ᶜ).card = if 0 < (genuine 3 (triple t)).card then 22 else 24 := by
  decide

/-- For every eight-element set modulo 11, the exact four-AP count is determined by whether
the three omitted elements form an arithmetic progression. -/
theorem eight_in_eleven_exact (A : Finset (ZMod 11)) (size : A.card = 8) :
    (genuine 4 A).card = if 0 < (genuine 3 Aᶜ).card then 22 else 24 := by
  classical
  let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
  have holes : Aᶜ.card = 3 := by simp [card_compl,ZMod.card,size]
  obtain ⟨x,y,z,hxy,hxz,hyz,hs⟩ := card_eq_three.mp holes
  let c := y-x
  have hc : c ≠ 0 := sub_ne_zero.mpr hxy.symm
  let t := (z-x)/c
  let f (v : ZMod 11) := x+c*v
  have inj : Function.Injective f := by intro i j eq; exact mul_left_cancel₀ hc (add_left_cancel eq)
  have f0 : f 0 = x := by simp [f]
  have f1 : f 1 = y := by simp [f,c]
  have ft : f t = z := by simp [f,t,hc,mul_div_cancel₀]
  have pre {i j a : ZMod 11} (eq : f j = a) : f i = a ↔ i = j := eq ▸ inj.eq_iff
  have pull (v : ZMod 11) : x+c*v ∈ Aᶜ ↔ v ∈ triple t := by
    rw [hs]
    change f v ∈ ({x,y,z} : Finset (ZMod 11)) ↔ v ∈ ({0,1,t} : Finset (ZMod 11))
    simp only [mem_insert,mem_singleton]
    exact or_congr (pre f0) (or_congr (pre f1) (pre ft))
  have rest (v : ZMod 11) : x+c*v ∈ A ↔ v ∈ (triple t)ᶜ := by
    simpa using not_congr (pull v)
  have not0 : t ≠ 0 := by intro e; exact hxz (f0.symm.trans ((congrArg f e).symm.trans ft))
  have not1 : t ≠ 1 := by intro e; exact hyz (f1.symm.trans ((congrArg f e).symm.trans ft))
  rw [← genuine_affine_preimage 4 x c hc rest,← genuine_affine_preimage 3 x c hc pull]
  exact normalized_eleven t not0 not1

set_option maxRecDepth 10000 in
theorem eleven_examples :
    (triple 2)ᶜ.card = 8 ∧ (genuine 4 (triple 2)ᶜ).card = 22 ∧
    (triple 3)ᶜ.card = 8 ∧ (genuine 4 (triple 3)ᶜ).card = 24 := by decide

end Erdos142.FiniteWindows
