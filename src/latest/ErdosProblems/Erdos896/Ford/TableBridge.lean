/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos896.Basic
import ErdosProblems.Erdos896.Ford.Defs

/-!
# The finite dyadic bridge for the multiplication table

This file contains the elementary part of the reduction of the multiplication
table problem to Ford's divisor-in-an-interval counting function.  No
analytic number theory is used here.

For a product `m = a * b`, first exchange the factors so that `a ≤ b`.  A
dyadic shell `k` records

`2^k m ≤ N² < 2^(k+1) m`,

and a dyadic window `j` for the smaller factor records

`2^j a ≤ N < 2^(j+1) a`.

The inequalities `a² ≤ m` force `k ≤ 2j+2`.  This restriction is important:
without it the resulting over-count would be too large for the analytic
summation used in Ford's multiplication-table estimate.
-/

namespace Erdos896.Ford

open Filter Asymptotics

/-- The possible divisor-window indices in product shell `k`.

The first condition is encoded by `range (k+1)`, namely `j ≤ k`; the filter
is the restriction forced by the fact that the selected divisor is the
smaller factor. -/
def admissibleWindows (k : ℕ) : Finset ℕ :=
  (Finset.range (k + 1)).filter fun j ↦ k ≤ 2 * j + 2

/-- The products remaining after the first `K` dyadic product shells. -/
def terminalProducts (N K : ℕ) : Finset ℕ :=
  Finset.Icc 1 (N ^ 2 / 2 ^ K)

/-- The `H`-set associated with shell `k` and factor window `j`.

Real endpoints avoid all rounding ambiguities: membership says that a
positive `m ≤ N² / 2^k` has a divisor in
`(N / 2^(j+1), N / 2^j]`. -/
noncomputable def tableHSet (N k j : ℕ) : Finset ℕ :=
  HSetR (N ^ 2 / 2 ^ k)
    ((N : ℝ) / (2 : ℝ) ^ (j + 1))
    ((N : ℝ) / (2 : ℝ) ^ j)

/-- The union of all divisor-window sets in the first `K` product shells. -/
noncomputable def tableHUnion (N K : ℕ) : Finset ℕ :=
  (Finset.range K).biUnion fun k ↦
    (admissibleWindows k).biUnion fun j ↦ tableHSet N k j

/-- The full finite dyadic cover: a terminal interval and the `H`-sets. -/
noncomputable def tableDyadicCover (N K : ℕ) : Finset ℕ :=
  terminalProducts N K ∪ tableHUnion N K

/-- The corresponding sum of Ford `H`-counts. -/
noncomputable def tableHSum (N K : ℕ) : ℕ :=
  ∑ k ∈ Finset.range K,
    ∑ j ∈ admissibleWindows k,
      HR (N ^ 2 / 2 ^ k)
        ((N : ℝ) / (2 : ℝ) ^ (j + 1))
        ((N : ℝ) / (2 : ℝ) ^ j)

@[simp]
theorem mem_admissibleWindows {k j : ℕ} :
    j ∈ admissibleWindows k ↔ j ≤ k ∧ k ≤ 2 * j + 2 := by
  simp [admissibleWindows]

@[simp]
theorem card_terminalProducts (N K : ℕ) :
    (terminalProducts N K).card = N ^ 2 / 2 ^ K := by
  simp [terminalProducts, Nat.card_Icc]

/-- Locate a point in one of the first `K` dyadic shells.

This induction is the discrete substitute for taking a base-two logarithm.
It deliberately has no positivity assumptions, which makes it reusable for
both product shells and factor windows. -/
theorem exists_dyadic_index {x y K : ℕ}
    (hyx : y ≤ x) (hcross : x < 2 ^ K * y) :
    ∃ k < K, 2 ^ k * y ≤ x ∧ x < 2 ^ (k + 1) * y := by
  induction K with
  | zero =>
      simp only [pow_zero, one_mul] at hcross
      exact (not_lt_of_ge hyx hcross).elim
  | succ K ih =>
      by_cases h : x < 2 ^ K * y
      · obtain ⟨k, hkK, hklo, hkhi⟩ := ih h
        exact ⟨k, hkK.trans (Nat.lt_succ_self K), hklo, hkhi⟩
      · exact ⟨K, Nat.lt_succ_self K, le_of_not_gt h, by simpa [Nat.succ_eq_add_one] using hcross⟩

/-- A product whose factors are already ordered belongs to the dyadic cover. -/
theorem ordered_product_mem_tableDyadicCover
    {N K a b : ℕ}
    (ha1 : 1 ≤ a) (haN : a ≤ N) (hbN : b ≤ N) (hab : a ≤ b) :
    a * b ∈ tableDyadicCover N K := by
  have hb1 : 1 ≤ b := ha1.trans hab
  have hm1 : 1 ≤ a * b := Nat.mul_pos ha1 hb1
  have hmN : a * b ≤ N ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul haN hbN
  by_cases hterminal : N ^ 2 < 2 ^ K * (a * b)
  · obtain ⟨k, hkK, hkshellUpper, hkshellLower⟩ :=
      exists_dyadic_index hmN hterminal
    have hfactorCross : N < 2 ^ (k + 1) * a := by
      by_contra h
      have hfactorUpper : 2 ^ (k + 1) * a ≤ N := le_of_not_gt h
      have hproductUpper : 2 ^ (k + 1) * (a * b) ≤ N ^ 2 := by
        calc
          2 ^ (k + 1) * (a * b) = (2 ^ (k + 1) * a) * b := by ring
          _ ≤ N * N := Nat.mul_le_mul hfactorUpper hbN
          _ = N ^ 2 := by ring
      exact (not_lt_of_ge hproductUpper) hkshellLower
    obtain ⟨j, hjk, hjfactorUpper, hjfactorLower⟩ :=
      exists_dyadic_index haN hfactorCross
    have hkj : k ≤ 2 * j + 2 := by
      by_contra h
      have hexponents : 2 * j + 2 ≤ k := Nat.le_of_lt (Nat.lt_of_not_ge h)
      have hpowers : 2 ^ (2 * j + 2) ≤ 2 ^ k :=
        Nat.pow_le_pow_right (by decide) hexponents
      have hsquare : N ^ 2 < (2 ^ (j + 1) * a) ^ 2 :=
        Nat.pow_lt_pow_left hjfactorLower (by decide)
      have haa : a ^ 2 ≤ a * b := by
        simpa [pow_two] using Nat.mul_le_mul_left a hab
      have hmiddle :
          (2 ^ (j + 1) * a) ^ 2 ≤ 2 ^ k * (a * b) := by
        calc
          (2 ^ (j + 1) * a) ^ 2 = 2 ^ (2 * j + 2) * a ^ 2 := by ring
          _ ≤ 2 ^ k * a ^ 2 := Nat.mul_le_mul_right (a ^ 2) hpowers
          _ ≤ 2 ^ k * (a * b) := Nat.mul_le_mul_left (2 ^ k) haa
      exact (not_lt_of_ge (hmiddle.trans hkshellUpper)) hsquare
    have hmCutoff : a * b ≤ N ^ 2 / 2 ^ k := by
      rw [Nat.le_div_iff_mul_le (by positivity)]
      simpa [mul_comm] using hkshellUpper
    have hwindow : a * b ∈ tableHSet N k j := by
      rw [tableHSet, mem_HSetR]
      refine ⟨hm1, hmCutoff, a, dvd_mul_right a b, ?_, ?_⟩
      · apply (div_lt_iff₀' (by positivity : (0 : ℝ) < (2 : ℝ) ^ (j + 1))).2
        exact_mod_cast hjfactorLower
      · apply (le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ j)).2
        exact_mod_cast (by simpa [mul_comm] using hjfactorUpper)
    apply Finset.mem_union_right
    rw [tableHUnion, Finset.mem_biUnion]
    refine ⟨k, Finset.mem_range.mpr hkK, ?_⟩
    rw [Finset.mem_biUnion]
    exact ⟨j, mem_admissibleWindows.mpr ⟨Nat.lt_succ_iff.mp hjk, hkj⟩, hwindow⟩
  · apply Finset.mem_union_left
    rw [terminalProducts, Finset.mem_Icc]
    refine ⟨hm1, ?_⟩
    rw [Nat.le_div_iff_mul_le (by positivity)]
    simpa [mul_comm] using le_of_not_gt hterminal

/-- Every entry of the `N` by `N` multiplication table lies in the finite
dyadic cover. -/
theorem multiplicationTable_subset_tableDyadicCover (N K : ℕ) :
    multiplicationTable N ⊆ tableDyadicCover N K := by
  intro m hm
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hm
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
  obtain ⟨ha1, haN⟩ := mem_box.mp ha
  obtain ⟨hb1, hbN⟩ := mem_box.mp hb
  rcases le_total a b with hab | hba
  · exact ordered_product_mem_tableDyadicCover ha1 haN hbN hab
  · rw [mul_comm]
    exact ordered_product_mem_tableDyadicCover hb1 hbN haN hba

/-- Cardinality form of the dyadic bridge.

The terminal contribution is explicit, while overlaps between different
`H`-sets are harmlessly bounded by the sum of their cardinalities. -/
theorem multiplicationTable_card_le_terminal_add_tableHSum (N K : ℕ) :
    (multiplicationTable N).card ≤ N ^ 2 / 2 ^ K + tableHSum N K := by
  calc
    (multiplicationTable N).card ≤ (tableDyadicCover N K).card :=
      Finset.card_le_card (multiplicationTable_subset_tableDyadicCover N K)
    _ ≤ (terminalProducts N K).card + (tableHUnion N K).card := by
      exact Finset.card_union_le _ _
    _ ≤ N ^ 2 / 2 ^ K + tableHSum N K := by
      rw [card_terminalProducts]
      apply Nat.add_le_add_left
      rw [tableHUnion, tableHSum]
      refine (Finset.card_biUnion_le).trans ?_
      apply Finset.sum_le_sum
      intro k hk
      refine (Finset.card_biUnion_le).trans_eq ?_
      apply Finset.sum_congr rfl
      intro j hj
      rfl

/-! ## Asymptotic transfer lemmas

The next results remain intentionally generic.  A Ford module proving the
analytic estimate can discharge their aggregate hypothesis directly; the
finite bridge itself does not postulate that estimate.
-/

/-- An eventual bound for the explicit terminal-plus-`H` sum gives the same
eventual bound for the table cardinality. -/
theorem multiplicationTable_eventually_le_of_terminal_add_tableHSum
    (K : ℕ → ℕ) (g : ℕ → ℝ)
    (h : ∀ᶠ N in atTop,
      ((N ^ 2 / 2 ^ K N + tableHSum N (K N) : ℕ) : ℝ) ≤ g N) :
    ∀ᶠ N in atTop, ((multiplicationTable N).card : ℝ) ≤ g N := by
  filter_upwards [h] with N hN
  have hfinite :
      ((multiplicationTable N).card : ℝ) ≤
        ((N ^ 2 / 2 ^ K N + tableHSum N (K N) : ℕ) : ℝ) := by
    exact_mod_cast multiplicationTable_card_le_terminal_add_tableHSum N (K N)
  exact hfinite.trans hN

/-- Big-O transfer from an already proved estimate for the explicit
terminal-plus-`H` sum. -/
theorem multiplicationTable_isBigO_of_terminal_add_tableHSum_isBigO
    (K : ℕ → ℕ) (g : ℕ → ℝ)
    (h : (fun N : ℕ ↦
      ((N ^ 2 / 2 ^ K N + tableHSum N (K N) : ℕ) : ℝ)) =O[atTop] g) :
    (fun N : ℕ ↦ ((multiplicationTable N).card : ℝ)) =O[atTop] g := by
  have hbridge :
      (fun N : ℕ ↦ ((multiplicationTable N).card : ℝ)) =O[atTop]
        (fun N : ℕ ↦
          ((N ^ 2 / 2 ^ K N + tableHSum N (K N) : ℕ) : ℝ)) := by
    apply Filter.Eventually.isBigO
    filter_upwards with N
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast multiplicationTable_card_le_terminal_add_tableHSum N (K N)
  exact hbridge.trans h

/-- A convenient two-piece form of the preceding transfer: prove the
terminal interval and the sum of `H`-terms are each `O(g)` separately. -/
theorem multiplicationTable_isBigO_of_terminal_isBigO_of_tableHSum_isBigO
    (K : ℕ → ℕ) (g : ℕ → ℝ)
    (hterminal :
      (fun N : ℕ ↦ ((N ^ 2 / 2 ^ K N : ℕ) : ℝ)) =O[atTop] g)
    (hH :
      (fun N : ℕ ↦ (tableHSum N (K N) : ℝ)) =O[atTop] g) :
    (fun N : ℕ ↦ ((multiplicationTable N).card : ℝ)) =O[atTop] g := by
  apply multiplicationTable_isBigO_of_terminal_add_tableHSum_isBigO K g
  simpa only [Nat.cast_add] using hterminal.add hH

end Erdos896.Ford
