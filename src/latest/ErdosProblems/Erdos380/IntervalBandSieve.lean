import ErdosProblems.Erdos380.AnchoredRunSieve

/-! # Bad intervals of one length scale and one greatest prime factor -/

open scoped BigOperators

namespace Erdos380

noncomputable def badPointsInLengthBand (N H p : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter fun n => ∃ u v : ℕ,
    BadInterval u v ∧ u ≤ n ∧ n ≤ v ∧ 2 * H ≤ v - u + 1 ∧
      v - u + 1 < 4 * H ∧ intervalPrime u v = p

def primeSquareAnchorNeighborhoods (s : Finset ℕ) (p W : ℕ) : Finset ℕ :=
  s.biUnion fun m => Finset.Icc (p ^ 2 * m - W) (p ^ 2 * m + W)

lemma primeSquareAnchorNeighborhoods_card_le (s : Finset ℕ) (p W : ℕ) :
    (primeSquareAnchorNeighborhoods s p W).card ≤ (2 * W + 1) * s.card := by
  calc
    _ ≤ ∑ m ∈ s, (Finset.Icc (p ^ 2 * m - W) (p ^ 2 * m + W)).card := Finset.card_biUnion_le
    _ ≤ ∑ _m ∈ s, (2 * W + 1) := by
      apply Finset.sum_le_sum
      intro m _
      rw [Nat.card_Icc]
      omega
    _ = _ := by simp [mul_comm]

lemma badPointsInLengthBand_card_le_anchoredRuns {u₀ N H p : ℕ}
    (hanchor : ∀ u v : ℕ, u₀ ≤ u → BadInterval u v →
      ∃ a ∈ Finset.Icc u v, intervalPrime u v ^ 2 ∣ a ∧
        largestPrimeFactor a = intervalPrime u v)
    (hH : 0 < H) :
    (badPointsInLengthBand N H p).card ≤ 2 * u₀ + (8 * H + 1) *
      ((anchoredSmoothRunStarts p (2 * N / p ^ 2) H false).card +
        (anchoredSmoothRunStarts p (2 * N / p ^ 2) H true).card) := by
  classical
  let S := anchoredSmoothRunStarts p (2 * N / p ^ 2) H false ∪
    anchoredSmoothRunStarts p (2 * N / p ^ 2) H true
  have hsub : badPointsInLengthBand N H p ⊆
      Finset.Icc 1 (2 * u₀) ∪ primeSquareAnchorNeighborhoods S p (4 * H) := by
    intro n hn
    obtain ⟨hnrange, u, v, hbad, hun, hnv, hlo, hhi, hQ⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hnrange
    by_cases hsmall : n ≤ 2 * u₀
    · exact Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨hn1, hsmall⟩)
    apply Finset.mem_union_right
    have hratio := hbad.right_lt_two_mul_left
    obtain ⟨a, ha, hdiv, _⟩ := hanchor u v (by omega) hbad
    obtain ⟨hua, hav⟩ := Finset.mem_Icc.mp ha
    have hapos : 0 < a := by have := hbad.1; omega
    rw [hQ] at hdiv
    let m := a / p ^ 2
    have hma : p ^ 2 * m = a := Nat.mul_div_cancel' hdiv
    have hmpos : 0 < m := by
      by_contra h
      have hz := Nat.eq_zero_of_not_pos h
      rw [hz, mul_zero] at hma
      omega
    have hmM : m ≤ 2 * N / p ^ 2 := Nat.div_le_div_right (by omega : a ≤ 2 * N)
    have hsmooth : ∀ b ∈ Finset.Icc u v, largestPrimeFactor b ≤ p := by
      intro b hb
      simpa only [hQ] using largestPrimeFactor_le_intervalPrime hbad.1 hb
    have hmS : m ∈ S := by
      by_cases hright : a + H - 1 ≤ v
      · apply Finset.mem_union_left
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_Icc.mpr ⟨by omega, hmM⟩, ?_⟩
        intro j hj
        have hjH := Finset.mem_range.mp hj
        simp only [anchorShiftValue, Bool.false_eq_true, ↓reduceIte, hma]
        exact hsmooth (a + j) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      · apply Finset.mem_union_right
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_Icc.mpr ⟨by omega, hmM⟩, ?_⟩
        intro j hj
        have hjH := Finset.mem_range.mp hj
        simp only [anchorShiftValue, ↓reduceIte, hma]
        exact hsmooth (a - j) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    apply Finset.mem_biUnion.mpr
    exact ⟨m, hmS, Finset.mem_Icc.mpr ⟨by rw [hma]; omega, by rw [hma]; omega⟩⟩
  have hScard : S.card ≤
      (anchoredSmoothRunStarts p (2 * N / p ^ 2) H false).card +
        (anchoredSmoothRunStarts p (2 * N / p ^ 2) H true).card := Finset.card_union_le _ _
  calc
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ (Finset.Icc 1 (2 * u₀)).card + (primeSquareAnchorNeighborhoods S p (4 * H)).card :=
      Finset.card_union_le _ _
    _ ≤ (Finset.Icc 1 (2 * u₀)).card + (2 * (4 * H) + 1) * S.card :=
      Nat.add_le_add_left (primeSquareAnchorNeighborhoods_card_le S p (4 * H)) _
    _ ≤ (Finset.Icc 1 (2 * u₀)).card + (2 * (4 * H) + 1) *
        ((anchoredSmoothRunStarts p (2 * N / p ^ 2) H false).card +
          (anchoredSmoothRunStarts p (2 * N / p ^ 2) H true).card) := by gcongr
    _ = _ := by rw [Nat.card_Icc]; simp only [Nat.add_sub_cancel]; ring

theorem exists_uniform_badPointsInLengthBand_bound : ∃ E P₀ : ℕ, ∀ p ≥ P₀,
    p.Prime → ∀ k H : ℕ, 0 < k → 0 < H → H ≤ p →
    20 * (k : ℝ) * Real.log p ≤ p → ∀ N : ℕ, (2 * p) ^ (2 * k) ≤ 2 * N / p ^ 2 →
      ((badPointsInLengthBand N H p).card : ℝ) ≤ E +
        (32 * H + 4 : ℝ) * ((2 * N / p ^ 2 : ℕ) : ℝ) /
          (((H : ℝ) / (40 * k * Real.log p)) ^ k) := by
  obtain ⟨u₀, hanchor⟩ := exists_badInterval_square_anchor_threshold
  obtain ⟨P₀, hP₀⟩ := exists_uniform_anchoredSmoothRunStarts_bound
  refine ⟨2 * u₀, P₀, ?_⟩
  intro p hp₀ hp k H hk hH hHp hkp N hpower
  have h₁ := badPointsInLengthBand_card_le_anchoredRuns (N := N) (p := p) hanchor hH
  have hleft := hP₀ p hp₀ hp k H hk hH hHp hkp _ hpower true
  have hright := hP₀ p hp₀ hp k H hk hH hHp hkp _ hpower false
  have h₁R : ((badPointsInLengthBand N H p).card : ℝ) ≤ (2 * u₀ : ℕ) + (8 * H + 1 : ℝ) *
      ((anchoredSmoothRunStarts p (2 * N / p ^ 2) H false).card +
        (anchoredSmoothRunStarts p (2 * N / p ^ 2) H true).card) := by exact_mod_cast h₁
  calc
    _ ≤ _ := h₁R
    _ ≤ ((2 * u₀ : ℕ) : ℝ) + (8 * H + 1 : ℝ) *
        ((((2 * N / p ^ 2 : ℕ) : ℝ) + (2 * N / p ^ 2 : ℕ)) /
          (((H : ℝ) / (40 * k * Real.log p)) ^ k) +
        (((2 * N / p ^ 2 : ℕ) : ℝ) + (2 * N / p ^ 2 : ℕ)) /
          (((H : ℝ) / (40 * k * Real.log p)) ^ k)) := by gcongr
    _ = _ := by ring

end Erdos380
