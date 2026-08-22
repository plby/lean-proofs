/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPositiveInterfaceScreenedSplit

/-!
# Honest balance predicate induced by a screened interface

For an adjacent-shell growth event `growth j` and a concrete stopped screen
`screened j`, the natural balanced event is

`growth j` complement union `screened j`.

On this event every actual growth failure is screened.  Its complement is
exactly the unscreened growth remainder.  Moreover, substituting this
balanced predicate into `thresholdedInterfaceBad` leaves the original growth
failure event unchanged, so the outer shell recurrence need not be altered.
-/

open Set

namespace Erdos1165.HLOZScreenedInterfaceBalance

open NearFavoriteThresholded

variable {Omega : Type*}

/-- Balanced means either no threshold-relevant growth occurred or the
growth path belongs to the concrete stopped screen. -/
def screenedInterfaceBalanced
    (occupancy : Omega → ℕ → ℕ) (threshold : ℕ → ℕ) (G : ℕ)
    (screened : ℕ → Set Omega) (j : ℕ) : Set Omega :=
  (thresholdedGrowthFailure occupancy threshold G j)ᶜ ∪ screened j

/-- Failure of the induced balance predicate is precisely the part of the
growth event not covered by the screen. -/
theorem screenedInterfaceBalanced_compl
    (occupancy : Omega → ℕ → ℕ) (threshold : ℕ → ℕ) (G : ℕ)
    (screened : ℕ → Set Omega) (j : ℕ) :
    (screenedInterfaceBalanced occupancy threshold G screened j)ᶜ =
      thresholdedGrowthFailure occupancy threshold G j \ screened j := by
  ext omega
  simp only [screenedInterfaceBalanced, Set.mem_compl_iff,
    Set.mem_union, not_or, Set.mem_sdiff]
  tauto

/-- A balanced path on which growth actually occurs is in the stopped
screen, exactly as required by the conditional product law. -/
theorem screenedInterfaceBalanced_inter_growth_subset_screened
    (occupancy : Omega → ℕ → ℕ) (threshold : ℕ → ℕ) (G : ℕ)
    (screened : ℕ → Set Omega) (j : ℕ) :
    screenedInterfaceBalanced occupancy threshold G screened j ∩
        thresholdedGrowthFailure occupancy threshold G j ⊆
      screened j := by
  rintro omega ⟨hbalanced, hgrowth⟩
  rcases hbalanced with hnotGrowth | hscreen
  · exact (hnotGrowth hgrowth).elim
  · exact hscreen

/-- The shell recurrence's public bad event is unchanged: the explicit
balance complement is already a subset of the raw growth failure. -/
theorem thresholdedInterfaceBad_screenedInterfaceBalanced
    (occupancy : Omega → ℕ → ℕ) (threshold : ℕ → ℕ) (G : ℕ)
    (screened : ℕ → Set Omega) (j : ℕ) :
    thresholdedInterfaceBad
        (screenedInterfaceBalanced occupancy threshold G screened)
        occupancy threshold G j =
      thresholdedGrowthFailure occupancy threshold G j := by
  rw [thresholdedInterfaceBad, screenedInterfaceBalanced_compl]
  exact union_eq_right.mpr sdiff_subset

end Erdos1165.HLOZScreenedInterfaceBalance
