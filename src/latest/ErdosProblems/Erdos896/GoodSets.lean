/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos896.Basic
import ErdosProblems.Erdos896.Ford.Defs

/-!
# The finite good sets for Erdős Problem 896

This file isolates the elementary finite sets used in the lower-bound
construction.  No estimate for Ford's counting functions is used here.

For a fixed `N` and `p`, `G N p` consists of the positive integers

`n ≤ N * N / (2 * p)`

having exactly one divisor in the cross-multiplied window

`N < 2 * p * d` and `p * d ≤ N`.

The refinements `GWithoutPrime` and `GFree` remove, respectively, multiples
of `p` and multiples of every prime in a selected finite set.  The last
section proves the exact bridge from `GFree` to the `Good` predicate in the
main Problem 896 file.
-/

namespace Erdos896

/-! ## The exact finite `G_p` -/

/-- The integral upper cutoff `N y_p`, with `y_p = N / (2p)`, used for
the finite good set.  Writing it in this form avoids real-number rounding. -/
def X (N p : ℕ) : ℕ :=
  N * N / (2 * p)

/-- The finite set `G_p`: positive integers below the exact cutoff having
exactly one divisor in the cross-multiplied divisor window. -/
def G (N p : ℕ) : Finset ℕ :=
  Ford.scaledH1Set N p (X N p)

/-- The `H₁`-type unique-divisor predicate underlying `G`. -/
def HasUniqueWindowDivisor (N p n : ℕ) : Prop :=
  ∃! d : ℕ, d ∣ n ∧ N < 2 * p * d ∧ p * d ≤ N

theorem mem_G {N p n : ℕ} :
    n ∈ G N p ↔
      1 ≤ n ∧ n ≤ X N p ∧ HasUniqueWindowDivisor N p n := by
  simpa only [G, HasUniqueWindowDivisor] using
    (Ford.mem_scaledH1Set (N := N) (p := p) (X := X N p) (n := n))

/-! ## The cofactor bound -/

/-- The cutoff `n ≤ N²/(2p)` and the lower side of the divisor window imply
the cofactor bound `n / d ≤ N`. -/
theorem cofactor_le_of_le_X_of_window {N p n d : ℕ}
    (hn : n ≤ X N p)
    (hd : N < 2 * p * d) :
    n / d ≤ N := by
  have htwoP : 0 < 2 * p := by
    by_contra h
    have hz : 2 * p = 0 := Nat.eq_zero_of_not_pos h
    rw [hz] at hd
    omega
  have hdpos : 0 < d := by
    by_contra h
    have hz : d = 0 := Nat.eq_zero_of_not_pos h
    subst d
    simp at hd
  have hmul : n * (2 * p) ≤ N * N := by
    exact (Nat.le_div_iff_mul_le htwoP).mp hn
  have hNle : N ≤ 2 * p * d := Nat.le_of_lt hd
  have hNN : N * N ≤ (N * d) * (2 * p) := by
    calc
      N * N ≤ N * (2 * p * d) := Nat.mul_le_mul_left N hNle
      _ = (N * d) * (2 * p) := by ac_rfl
  have hnNd : n ≤ N * d :=
    Nat.le_of_mul_le_mul_right (hmul.trans hNN) htwoP
  exact Nat.div_le_of_le_mul (by simpa [mul_comm] using hnNd)

/-- Membership in `G` is exactly the finite `H₁` condition together with
the cofactor bound needed by the combinatorial bridge. -/
theorem mem_G_iff_existsUnique_bounded {N p n : ℕ} :
    n ∈ G N p ↔
      1 ≤ n ∧ n ≤ X N p ∧
        ∃! d : ℕ,
          d ∣ n ∧ N < 2 * p * d ∧ p * d ≤ N ∧ n / d ≤ N := by
  rw [mem_G]
  constructor
  · rintro ⟨hn1, hnX, d, hd, huniq⟩
    refine ⟨hn1, hnX, d, ⟨hd.1, hd.2.1, hd.2.2,
      cofactor_le_of_le_X_of_window hnX hd.2.1⟩, ?_⟩
    intro e he
    exact huniq e ⟨he.1, he.2.1, he.2.2.1⟩
  · rintro ⟨hn1, hnX, d, hd, huniq⟩
    refine ⟨hn1, hnX, d, ⟨hd.1, hd.2.1, hd.2.2.1⟩, ?_⟩
    intro e he
    apply huniq e
    exact ⟨he.1, he.2.1, he.2.2,
      cofactor_le_of_le_X_of_window hnX he.2.1⟩

/-! ## Prime-excluded and selected-set-free refinements -/

/-- Remove the exceptional multiples of `p` from `G_p`. -/
def GWithoutPrime (N p : ℕ) : Finset ℕ :=
  (G N p).filter fun n ↦ ¬p ∣ n

@[simp]
theorem mem_GWithoutPrime {N p n : ℕ} :
    n ∈ GWithoutPrime N p ↔ n ∈ G N p ∧ ¬p ∣ n := by
  simp [GWithoutPrime]

/-- Starting from `G_p^0`, remove every integer divisible by a member of the
selected finite set `P`. -/
def GFree (N p : ℕ) (P : Finset ℕ) : Finset ℕ :=
  (GWithoutPrime N p).filter fun n ↦ ∀ q ∈ P, ¬q ∣ n

@[simp]
theorem mem_GFree {N p n : ℕ} {P : Finset ℕ} :
    n ∈ GFree N p P ↔
      n ∈ G N p ∧ ¬p ∣ n ∧ ∀ q ∈ P, ¬q ∣ n := by
  simp [GFree, and_assoc]

theorem GFree_subset_GWithoutPrime (N p : ℕ) (P : Finset ℕ) :
    GFree N p P ⊆ GWithoutPrime N p := by
  exact Finset.filter_subset _ _

theorem GWithoutPrime_subset_G (N p : ℕ) :
    GWithoutPrime N p ⊆ G N p := by
  exact Finset.filter_subset _ _

/-! ## The elementary exceptional-multiple bound -/

/-- Members of `G_p` which are removed in `G_p^0`. -/
def GMultiples (N p : ℕ) : Finset ℕ :=
  (G N p).filter fun n ↦ p ∣ n

@[simp]
theorem mem_GMultiples {N p n : ℕ} :
    n ∈ GMultiples N p ↔ n ∈ G N p ∧ p ∣ n := by
  simp [GMultiples]

/-- At most `⌊X/p⌋` members of `G_p` are exceptional multiples of `p`. -/
theorem card_GMultiples_le (N p : ℕ) :
    (GMultiples N p).card ≤ X N p / p := by
  let multiplesUpTo : Finset ℕ :=
    (Finset.range (X N p).succ).filter fun n ↦ n ≠ 0 ∧ p ∣ n
  have hsubset : GMultiples N p ⊆ multiplesUpTo := by
    intro n hn
    rw [mem_GMultiples] at hn
    rw [Finset.mem_filter, Finset.mem_range]
    have hnG := mem_G.mp hn.1
    exact ⟨Nat.lt_succ_iff.mpr hnG.2.1,
      Nat.one_le_iff_ne_zero.mp hnG.1, hn.2⟩
  calc
    (GMultiples N p).card ≤ multiplesUpTo.card := Finset.card_le_card hsubset
    _ = X N p / p := by
      simpa only [multiplesUpTo] using Nat.card_multiples' (X N p) p

/-- `G_p` is the disjoint union, by cardinality, of its multiples of `p` and
its `p`-excluded refinement. -/
theorem card_GMultiples_add_card_GWithoutPrime (N p : ℕ) :
    (GMultiples N p).card + (GWithoutPrime N p).card = (G N p).card := by
  simpa only [GMultiples, GWithoutPrime] using
    (Finset.card_filter_add_card_filter_not (s := G N p) (p := fun n ↦ p ∣ n))

/-- Removing multiples of `p` loses at most `⌊X/p⌋` elements. -/
theorem card_G_le_card_GWithoutPrime_add (N p : ℕ) :
    (G N p).card ≤ (GWithoutPrime N p).card + X N p / p := by
  have hexception := card_GMultiples_le N p
  rw [← card_GMultiples_add_card_GWithoutPrime N p]
  omega

/-- Subtractive form of the same exceptional-set estimate. -/
theorem card_G_sub_le_card_GWithoutPrime (N p : ℕ) :
    (G N p).card - X N p / p ≤ (GWithoutPrime N p).card := by
  have htotal := card_G_le_card_GWithoutPrime_add N p
  omega

/-! ## Bridge to the main finite construction -/

/-- Every member of the selected-set-free refinement supplies precisely the
finite data required by `Erdos896.Good`. -/
theorem good_of_mem_GFree {N p n : ℕ} {P : Finset ℕ}
    (hn : n ∈ GFree N p P) :
    Good N P p n := by
  rw [mem_GFree] at hn
  have hbounded := mem_G_iff_existsUnique_bounded.mp hn.1
  exact ⟨Nat.lt_of_lt_of_le Nat.zero_lt_one hbounded.1,
    hn.2.2, hbounded.2.2⟩

end Erdos896
