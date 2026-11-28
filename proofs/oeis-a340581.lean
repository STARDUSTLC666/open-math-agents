import OMAStatements.S_oeis_a340581

/-! Compare divisor and part multiplicities by grouping columns by their first row. -/
-- Credit: @STARDUSTLC666

namespace TriangleDivisors

open Finset Nat.Partition OMA.S_oeis_a340581

-- The fixed-part deletion argument also appears in our A340426 and A340524 proofs.
private def occurrences (n d : ℕ) := ∑ p : n.Partition, p.parts.count d
private def residuals (n d : ℕ) :=
  ∑ j ∈ range n, if d ∣ n-j then A000041 j else 0

private lemma erase_one {n d : ℕ} (hd : 0 < d) (hn : d ≤ n) :
    occurrences n d = occurrences (n-d) d + A000041 (n-d) := by
  classical
  let e := partitionWithPartEquiv (n := n) hd hn
  have split := Fintype.sum_subtype_add_sum_subtype
    (fun p : n.Partition => d ∈ p.parts) (fun p => p.parts.count d)
  have empty : (∑ p : {p : n.Partition // d ∉ p.parts}, p.val.parts.count d) = 0 := by
    apply sum_eq_zero
    intro p _
    exact Multiset.count_eq_zero.mpr p.property
  rw [empty, add_zero] at split
  calc
    occurrences n d = ∑ p : {p : n.Partition // d ∈ p.parts}, p.val.parts.count d := split.symm
    _ = ∑ q : (n-d).Partition, (e.symm q).val.parts.count d :=
      (e.symm.sum_comp (fun p => p.val.parts.count d)).symm
    _ = _ := by simp [e, occurrences, A000041, sum_add_distrib]

private lemma residual_step (m d : ℕ) (hd : 0 < d) :
    residuals (m+d) d = residuals m d + A000041 m := by
  classical
  unfold residuals
  rw [sum_range_add]
  congr 1
  · apply sum_congr rfl
    intro j hj
    have h := mem_range.mp hj
    rw [show m+d-j = (m-j)+d by omega]
    simp
  · rw [sum_eq_single_of_mem 0 (mem_range.mpr hd)]
    · simp
    · intro j hj hj0
      have hjd := mem_range.mp hj
      have no : ¬ d ∣ d-j := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
      simp [show m+d-(m+j) = d-j by omega, no]

private lemma count_parts (n d : ℕ) (hd : 0 < d) : occurrences n d = residuals n d := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : d ≤ n
    · rw [erase_one hd hn, ih (n-d) (by omega)]
      simpa [Nat.sub_add_cancel hn] using (residual_step (n-d) d hd).symm
    · have no : occurrences n d = 0 := by
        apply sum_eq_zero
        intro p _
        apply Multiset.count_eq_zero.mpr
        exact fun h => hn (le_of_mem_parts h)
      rw [no, residuals]
      symm
      apply sum_eq_zero
      intro j hj
      have h := mem_range.mp hj
      simp [Nat.not_dvd_of_pos_of_lt (show 0 < n-j by omega) (show n-j < d by omega)]

private lemma all_parts (n d : ℕ) : occurrences n d = residuals n d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have hz : occurrences n 0 = 0 := by
      apply sum_eq_zero
      intro p _
      exact Multiset.count_eq_zero.mpr (fun h => (Nat.lt_irrefl 0) (p.parts_pos h))
    rw [hz, residuals]
    symm
    apply sum_eq_zero
    intro j hj
    have h := mem_range.mp hj
    simp [show n-j ≠ 0 by omega]
  · exact count_parts n d hd

private lemma length_sum (n : ℕ) : L n = ∑ r ∈ range n, A000070 r := by
  cases n <;> simp [L, A014153]

private lemma length_step (n : ℕ) : L (n+1) = L n + A000070 n := by
  rw [length_sum (n+1), length_sum n, sum_range_succ]

private lemma length_mono : Monotone L := by
  apply monotone_nat_of_le_succ
  intro n
  rw [length_step]
  omega

private lemma first_row (r j : ℕ) (hj : j < A000070 r) : start (L r+j+1) = r+1 := by
  let s := {i : ℕ | L r+j+1 ≤ L i}
  have mem : r+1 ∈ s := by
    change L r+j+1 ≤ L (r+1)
    rw [length_step]
    omega
  change sInf s = r+1
  apply le_antisymm (csInf_le (show BddBelow s from ⟨0, fun i _ => Nat.zero_le i⟩) mem)
  apply le_csInf ⟨r+1, mem⟩
  intro i hi
  change L r+j+1 ≤ L i at hi
  by_contra! h
  have := length_mono (show i ≤ r by omega)
  omega

-- Column numbers in the interval (L r, L (r+1)] all have the same value in row n.
private lemma column_sum (n : ℕ) (f : ℕ → ℕ) (r : ℕ) (hr : r ≤ n) :
    (∑ j ∈ range (L r), f (T n (j+1))) = ∑ i ∈ range r, A000070 i * f (n-i) := by
  induction r with
  | zero => simp [L]
  | succ r ih =>
    rw [length_step, sum_range_add, ih (by omega), sum_range_succ]
    congr 1
    calc
      _ = ∑ j ∈ range (A000070 r), f (n-r) := by
        apply sum_congr rfl
        intro j hj
        rw [T, first_row r j (mem_range.mp hj), show n-(r+1)+1 = n-r by omega]
      _ = _ := by simp

private lemma indices (m : ℕ) (f : ℕ → ℕ) :
    ∑ k ∈ Icc 1 m, f k = ∑ j ∈ range m, f (j+1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [sum_Icc_succ_top (by omega), ih, sum_range_succ]

private def cumulative (n d : ℕ) : ℕ :=
  ∑ j ∈ range n, if d ∣ n-j then A000070 j else 0

private lemma divisor_side (n d : ℕ) :
    ((row n).bind (fun t => t.divisors.val)).count d = cumulative n d := by
  let f (m : ℕ) := m.divisors.val.count d
  calc
    _ = ∑ k ∈ Icc 1 (L n), f (T n k) := by
      rw [row, Multiset.count_bind, Multiset.map_map]
      rfl
    _ = ∑ j ∈ range (L n), f (T n (j+1)) := indices _ _
    _ = ∑ j ∈ range n, A000070 j * f (n-j) := column_sum n f n le_rfl
    _ = _ := by
      apply sum_congr rfl
      intro j hj
      have lt := mem_range.mp hj
      have nz : n-j ≠ 0 := by omega
      dsimp [f]
      by_cases divides : d ∣ n-j
      · have mem : d ∈ (n-j).divisors := Nat.mem_divisors.mpr ⟨divides, nz⟩
        rw [Multiset.count_eq_one_of_mem (n-j).divisors.nodup mem, if_pos divides, mul_one]
      · have miss : d ∉ (n-j).divisors := fun h => divides (Nat.mem_divisors.mp h).1
        rw [Multiset.count_eq_zero.mpr miss, if_neg divides, mul_zero]

private lemma cumulative_step (n d : ℕ) :
    cumulative (n+1) d = cumulative n d + residuals (n+1) d := by
  have base : A000070 0 = A000041 0 := by simp [A000070]
  have step (j : ℕ) : A000070 (j+1) = A000070 j + A000041 (j+1) := by
    exact sum_range_succ _ _
  have term (j : ℕ) :
      (if d ∣ n-j then A000070 (j+1) else 0) =
        (if d ∣ n-j then A000070 j else 0) + (if d ∣ n-j then A000041 (j+1) else 0) := by
    by_cases h : d ∣ n-j <;> simp [h, step]
  unfold cumulative residuals
  rw [sum_range_succ' (fun j => if d ∣ n+1-j then A000070 j else 0),
    sum_range_succ' (fun j => if d ∣ n+1-j then A000041 j else 0)]
  simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero, base, term, sum_add_distrib]
  omega

private lemma partition_side (n d : ℕ) :
    (∑ j ∈ Icc 1 n, (univ : Finset (Nat.Partition j)).val.bind (fun p => p.parts)).count d =
      cumulative n d := by
  induction n with
  | zero => simp [cumulative]
  | succ n ih =>
    rw [sum_Icc_succ_top (show 1 ≤ n+1 by omega), Multiset.count_add, ih, cumulative_step]
    congr 1
    rw [Multiset.count_bind]
    exact all_parts (n+1) d

end TriangleDivisors

open TriangleDivisors OMA.S_oeis_a340581

theorem OMA.solution : type_of% @OMA.S_oeis_a340581.main := by
  intro n _
  apply Multiset.ext.mpr
  intro d
  exact (divisor_side n d).trans (partition_side n d).symm
