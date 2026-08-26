import ErdosProblems.Erdos486.BiasedColoring
import ErdosProblems.Erdos486.FiniteAveraging

/- Ported to Lean/Mathlib 4.33.0; see README.md for source and modifications. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Finite averages of the biased footprint

This module identifies the periodic footprint ratio with the average of its
zero-one coverage indicator.  It also records the finite Fubini step used to
exchange the averages over residues and colourings.
-/

open scoped BigOperators

namespace Erdos486

noncomputable section

local instance biasedPeriodNeZero (j : ℕ) : NeZero (biasedPeriod j) :=
  ⟨(biasedPeriod_pos j).ne'⟩

/-- The rational zero-one indicator that a residue is covered by a biased
colouring. -/
noncomputable def biasedCoverageIndicator (j : ℕ)
    (x : ZMod (biasedPeriod j)) (c : BiasedColoring j) : ℚ := by
  classical
  exact if IsBiasedCovered j c x then 1 else 0

/-- Finite Fubini for uniform rational averages over nonempty finite types. -/
theorem fintypeAverage_comm {α β : Type*}
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (f : α → β → ℚ) :
    fintypeAverage (fun a ↦ fintypeAverage (f a)) =
      fintypeAverage (fun b ↦ fintypeAverage (fun a ↦ f a b)) := by
  classical
  have hα : (Fintype.card α : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hβ : (Fintype.card β : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold fintypeAverage
  calc
    (∑ a : α, (∑ b : β, f a b) / Fintype.card β) /
          Fintype.card α =
        (∑ a : α, ∑ b : β, f a b) /
          ((Fintype.card β : ℚ) * Fintype.card α) := by
      rw [← Finset.sum_div, div_div]
    _ = (∑ b : β, ∑ a : α, f a b) /
          ((Fintype.card α : ℚ) * Fintype.card β) := by
      apply (div_eq_div_iff (mul_ne_zero hβ hα)
        (mul_ne_zero hα hβ)).2
      rw [Finset.sum_comm]
      ring
    _ = (∑ b : β, (∑ a : α, f a b) / Fintype.card α) /
          Fintype.card β := by
      rw [← Finset.sum_div, div_div]

/-- For a fixed colouring, the average coverage indicator over one period is
exactly its rational footprint. -/
theorem fintypeAverage_biasedCoverageIndicator (j : ℕ)
    (c : BiasedColoring j) :
    fintypeAverage (fun x ↦ biasedCoverageIndicator j x c) =
      biasedFootprintRat j c := by
  classical
  have hcard :
      Fintype.card (ZMod (biasedPeriod j)) = biasedPeriod j :=
    ZMod.card (biasedPeriod j)
  have hperiodQ : (biasedPeriod j : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (biasedPeriod_pos j).ne'
  have hcardQ :
      (Fintype.card (ZMod (biasedPeriod j)) : ℚ) ≠ 0 := by
    rw [hcard]
    exact hperiodQ
  unfold fintypeAverage biasedCoverageIndicator
  rw [Finset.sum_boole, biasedFootprintRat]
  unfold biasedFootprintCount
  apply (div_eq_div_iff hcardQ hperiodQ).2
  rw [hcard]

/-- Averaging the rational footprint over colourings is the same as first
averaging the coverage indicator over colourings and then over residues. -/
theorem fintypeAverage_biasedFootprintRat (j : ℕ) :
    fintypeAverage (fun c : BiasedColoring j ↦ biasedFootprintRat j c) =
      fintypeAverage (fun x : ZMod (biasedPeriod j) ↦
        fintypeAverage (fun c : BiasedColoring j ↦
          biasedCoverageIndicator j x c)) := by
  calc
    fintypeAverage (fun c : BiasedColoring j ↦ biasedFootprintRat j c) =
        fintypeAverage (fun c : BiasedColoring j ↦
          fintypeAverage (fun x : ZMod (biasedPeriod j) ↦
            biasedCoverageIndicator j x c)) := by
      apply congrArg fintypeAverage
      funext c
      exact (fintypeAverage_biasedCoverageIndicator j c).symm
    _ = fintypeAverage (fun x : ZMod (biasedPeriod j) ↦
          fintypeAverage (fun c : BiasedColoring j ↦
            biasedCoverageIndicator j x c)) :=
      fintypeAverage_comm (fun c x ↦ biasedCoverageIndicator j x c)

end

end Erdos486
