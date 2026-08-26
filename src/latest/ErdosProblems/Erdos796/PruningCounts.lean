import ErdosProblems.Erdos796.PruningArithmetic
import ErdosProblems.Erdos796.Core

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Elementary cardinality losses in pruning

This file handles the polynomial-size and small-prime exceptional sets whose
cardinality estimates do not use the complete-box argument.
-/

namespace Erdos796

open scoped Nat.Prime

namespace PruningCounts

open PruningArithmetic

/-- Surviving `Y`-smooth elements, after all integers with three factors
larger than `Y` have been removed. -/
noncomputable def survivingSmooth (A : Finset ℕ) (Y : ℕ) : Finset ℕ := by
  classical
  exact A.filter fun a => YSmooth Y a ∧ ¬HasThreeLargeFactors Y a

theorem survivingSmooth_subset_power
    {n Y : ℕ} {A : Finset ℕ} (hA : Admissible n A) (hY : 2 ≤ Y) :
    survivingSmooth A Y ⊆ positiveIcc (Y ^ 6) := by
  classical
  intro a ha
  have ha' := Finset.mem_filter.mp ha
  have hapos := (mem_positiveIcc.mp (hA.1 ha'.1)).1
  exact mem_positiveIcc.mpr
    ⟨hapos, ySmooth_le_pow_six_of_no_three_large_factors
      hY ha'.2.1 ha'.2.2⟩

/-- Hence the smooth exceptional set has at most `Y⁶` elements. -/
theorem card_survivingSmooth_le
    {n Y : ℕ} {A : Finset ℕ} (hA : Admissible n A) (hY : 2 ≤ Y) :
    (survivingSmooth A Y).card ≤ Y ^ 6 := by
  classical
  have hcard := Finset.card_le_card (survivingSmooth_subset_power hA hY)
  simpa [positiveIcc] using! hcard

/-- Products of a prime at most `N` with a cofactor in `[1,R]`. -/
def boundedPrimeCofactorProducts (N R : ℕ) : Finset ℕ :=
  (Nat.primesLE N ×ˢ positiveIcc R).image fun qt => qt.1 * qt.2

theorem card_boundedPrimeCofactorProducts_le (N R : ℕ) :
    (boundedPrimeCofactorProducts N R).card ≤
      Nat.primeCounting N * R := by
  calc
    (boundedPrimeCofactorProducts N R).card ≤
        (Nat.primesLE N ×ˢ positiveIcc R).card := Finset.card_image_le
    _ = Nat.primeCounting N * R := by
      simp [positiveIcc]

/-- Any finite set admitting the displayed prime/cofactor factorization has
the same cardinal upper bound. -/
theorem card_le_primeCounting_mul_of_factorization
    {B : Finset ℕ} {N R : ℕ}
    (hfactor : ∀ a ∈ B, ∃ q ∈ Nat.primesLE N,
      ∃ t ∈ positiveIcc R, a = q * t) :
    B.card ≤ Nat.primeCounting N * R := by
  have hsub : B ⊆ boundedPrimeCofactorProducts N R := by
    intro a ha
    rcases hfactor a ha with ⟨q, hq, t, ht, rfl⟩
    exact Finset.mem_image.mpr
      ⟨(q, t), Finset.mem_product.mpr ⟨hq, ht⟩, rfl⟩
  exact (Finset.card_le_card hsub).trans
    (card_boundedPrimeCofactorProducts_le N R)

/-- Repeated-prime products `s*q*q` with `s≤R`, `q≤N` also have at most
`R π(N)` possibilities. -/
def boundedPrimeSquareProducts (N R : ℕ) : Finset ℕ :=
  (Nat.primesLE N ×ˢ positiveIcc R).image fun qs => qs.2 * qs.1 * qs.1

theorem card_boundedPrimeSquareProducts_le (N R : ℕ) :
    (boundedPrimeSquareProducts N R).card ≤
      Nat.primeCounting N * R := by
  calc
    (boundedPrimeSquareProducts N R).card ≤
        (Nat.primesLE N ×ˢ positiveIcc R).card := Finset.card_image_le
    _ = Nat.primeCounting N * R := by
      simp [positiveIcc]

end PruningCounts

end Erdos796
