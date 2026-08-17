/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Sort
import Mathlib.NumberTheory.Divisors
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic

/-!
# Erdős Problem 1099: definitions and filter-level reduction

This file contains the source-faithful statistic and the elementary passage
from a cofinal bounded subsequence to the literal real-valued liminf.
-/

open Filter Finset
open scoped BigOperators

namespace Erdos1099

noncomputable section

/-- The increasing enumeration of the positive divisors of `n`. -/
def orderedDivisor (n : ℕ) : Fin n.divisors.card ↪o ℕ :=
  n.divisors.orderEmbOfFin rfl

lemma orderedDivisor_mem (n : ℕ) (i : Fin n.divisors.card) :
    orderedDivisor n i ∈ n.divisors :=
  Finset.orderEmbOfFin_mem n.divisors rfl i

lemma orderedDivisor_pos (n : ℕ) (i : Fin n.divisors.card) :
    0 < orderedDivisor n i :=
  Nat.pos_of_mem_divisors (orderedDivisor_mem n i)

/-- The power energy of consecutive relative divisor gaps from Problem 1099. -/
def hAlpha (α : ℝ) (n : ℕ) : ℝ :=
  ∑ i : Fin (n.divisors.card - 1),
    Real.rpow
      (((orderedDivisor n ⟨i.1 + 1, by omega⟩ : ℕ) : ℝ) /
          ((orderedDivisor n ⟨i.1, by omega⟩ : ℕ) : ℝ) - 1)
      α

lemma relativeGap_nonneg (n : ℕ) (i : Fin (n.divisors.card - 1)) :
    0 ≤ (((orderedDivisor n ⟨i.1 + 1, by omega⟩ : ℕ) : ℝ) /
      ((orderedDivisor n ⟨i.1, by omega⟩ : ℕ) : ℝ) - 1) := by
  have hlt :
      orderedDivisor n ⟨i.1, by omega⟩ <
        orderedDivisor n ⟨i.1 + 1, by omega⟩ :=
    (orderedDivisor n).strictMono (by simp)
  have hden : (0 : ℝ) < orderedDivisor n ⟨i.1, by omega⟩ := by
    exact_mod_cast orderedDivisor_pos n ⟨i.1, by omega⟩
  rw [sub_nonneg, one_le_div hden]
  exact_mod_cast hlt.le

lemma hAlpha_nonneg (α : ℝ) (n : ℕ) : 0 ≤ hAlpha α n := by
  unfold hAlpha
  exact Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (relativeGap_nonneg n i) α

/-- The substantive, non-vacuous interpretation of a finite liminf in the problem. -/
def IsBoundedFrequently (f : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ᶠ n : ℕ in atTop, f n ≤ C

lemma frequently_le_of_cofinal_sequence {f : ℕ → ℝ} {u : ℕ → ℕ} {C : ℝ}
    (hu : Tendsto u atTop atTop) (hC : ∀ k, f (u k) ≤ C) :
    ∃ᶠ n : ℕ in atTop, f n ≤ C := by
  rw [frequently_atTop]
  intro N
  obtain ⟨K, hK⟩ := (tendsto_atTop_atTop.mp hu) N
  exact ⟨u K, hK K le_rfl, hC K⟩

lemma liminf_le_of_frequently_hAlpha_le {α C : ℝ}
    (hfreq : ∃ᶠ n : ℕ in atTop, hAlpha α n ≤ C) :
    Filter.liminf (hAlpha α) atTop ≤ C := by
  exact Filter.liminf_le_of_frequently_le hfreq
    (Filter.isBoundedUnder_of ⟨0, hAlpha_nonneg α⟩)

end

end Erdos1099
