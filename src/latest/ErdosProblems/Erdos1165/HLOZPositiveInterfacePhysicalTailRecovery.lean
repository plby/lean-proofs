/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPositiveInterfacePhysicalCoordinateRecovery
import ErdosProblems.Erdos1165.HLOZPositiveInterfaceGatedPhysicalSplit

/-!
# Recovering the random-total tail from physical shell counts

The pathwise positive-interface reconstruction supplies the cardinalities of
the two adjacent physical shell windows.  This file contains the finite
combinatorial step which turns those two cardinalities and the raw growth
failure into the exact random-total product predicate.  In particular, no
probability or product-mass premise enters this conversion.
-/

namespace Erdos1165.HLOZPositiveInterfacePhysicalTailRecovery

open HeterogeneousProductTail
open HLOZAllSixBandProductClosure
open NearFavoriteShells
open NearFavoriteThresholded

noncomputable section

attribute [local instance] Classical.propDecidable

variable {Coordinate : Type*} [Fintype Coordinate]
variable {State : Coordinate → Type*}

/-- Two disjoint coordinate windows with the raw adjacent-shell
cardinalities satisfy the aggregate random-total product predicate whenever
the corresponding raw shell occupancies satisfy the thresholded growth
failure and their sum is below the displayed product bound. -/
theorem randomTotalThresholdedUpperTail_of_shell_cardinalities
    (upper lower : ∀ c, State c → Prop)
    [∀ c, DecidablePred (upper c)] [∀ c, DecidablePred (lower c)]
    (threshold : ℕ → ℕ) (G shell bound : ℕ)
    (ell : ∀ c, State c) (lowerCount upperCountRaw : ℕ)
    (hdisjoint : ∀ c, ¬ (upper c (ell c) ∧ lower c (ell c)))
    (hupper : (Finset.univ.filter fun c ↦ upper c (ell c)).card =
      upperCountRaw)
    (hlower : (Finset.univ.filter fun c ↦ lower c (ell c)).card =
      lowerCount)
    (hfailure : threshold (shell + 1) < upperCountRaw ∧
      G * lowerCount < upperCountRaw)
    (hbound : lowerCount + upperCountRaw < bound + 1) :
    randomTotalThresholdedUpperTail upper lower threshold G shell bound ell := by
  classical
  have hfinsetDisjoint : Disjoint
      (Finset.univ.filter fun c ↦ upper c (ell c))
      (Finset.univ.filter fun c ↦ lower c (ell c)) := by
    rw [Finset.disjoint_left]
    intro c hcUpper hcLower
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hcUpper hcLower
    exact hdisjoint c ⟨hcUpper, hcLower⟩
  have hpair : (pairSupport upper lower ell).card =
      lowerCount + upperCountRaw := by
    unfold pairSupport
    rw [Finset.filter_or, Finset.card_union_of_disjoint hfinsetDisjoint,
      hupper, hlower, Nat.add_comm]
  have hupperCount : HeterogeneousProductTail.upperCount upper ell =
      upperCountRaw := by
    unfold HeterogeneousProductTail.upperCount
    calc
      (∑ c, if upper c (ell c) then 1 else 0) =
          (Finset.univ.filter fun c ↦ upper c (ell c)).card := by
        exact Finset.sum_boole (R := ℕ) (fun c ↦ upper c (ell c))
          (Finset.univ : Finset Coordinate)
      _ = upperCountRaw := hupper
  have hcut : thresholdedGrowthCut threshold G shell
      (lowerCount + upperCountRaw) ≤ upperCountRaw := by
    apply max_le
    · omega
    · apply growthCut_le_of_ratio
      · omega
      · have hsub : lowerCount + upperCountRaw - upperCountRaw =
            lowerCount := by omega
        rw [hsub]
        exact hfailure.2
  unfold randomTotalThresholdedUpperTail
  rw [hpair, hupperCount]
  exact ⟨hbound, hcut⟩

end

end Erdos1165.HLOZPositiveInterfacePhysicalTailRecovery
