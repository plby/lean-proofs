/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616RichCoordinateFacts

/-!
# Scalar capacity bounds for the rich Claim 6.16 coordinate backend

This module converts the common cluster size and the two exact distinguished
reserve sizes into the literal raw-reservoir margins used by the coordinate
embedding backend.  It contains no graph copy, embedding, continuation, or
cut-forest-data premise.
-/

open scoped BigOperators

noncomputable section

namespace Erdos547b.ZhaoClaim616RichCoordinateCapacityNumerics

open Finset
open Erdos547b.ZhaoClaim616HierarchicalCoordinateHostLayout

universe u

variable {B : Type u} [Fintype B] [DecidableEq B]

/-- Deleting two reserves of size `quota` from a common cluster of size `m`
leaves at least `m - 2 * quota` vertices. -/
theorem sub_two_mul_le_card_removeRootReserves
    (rootReserve companionReserve X : Finset B) (quota m : ℕ)
    (hroot : rootReserve.card = quota)
    (hcompanion : companionReserve.card = quota)
    (hX : X.card = m) :
    m - 2 * quota ≤
      #(removeRootReserves rootReserve companionReserve X) := by
  have hsplit := Finset.card_sdiff_add_card_inter X
    (rootReserve ∪ companionReserve)
  have hinter : #(X ∩ (rootReserve ∪ companionReserve)) ≤
      #(rootReserve ∪ companionReserve) :=
    Finset.card_le_card Finset.inter_subset_right
  have hunion : #(rootReserve ∪ companionReserve) ≤
      rootReserve.card + companionReserve.card :=
    Finset.card_union_le _ _
  simp only [removeRootReserves]
  omega

/-- A scalar margin against the common lower bound `m - 2 * quota` implies
the literal margin for any load bounded by `capacity` in the corresponding
reserve-deleted cluster. -/
theorem capacity_margin_removeRootReserves
    (rootReserve companionReserve X : Finset B)
    (quota m load capacity small : ℕ)
    (rho density removalBudget : ℝ)
    (hroot : rootReserve.card = quota)
    (hcompanion : companionReserve.card = quota)
    (hX : X.card = m)
    (hgap : 0 ≤ density - rho)
    (hload : load ≤ capacity)
    (hmargin :
      (capacity + small + 1 : ℝ) + removalBudget + 1 ≤
        (density - rho) * (m - 2 * quota : ℕ)) :
    (load + small + 1 : ℝ) + removalBudget + 1 ≤
      (density - rho) *
        #(removeRootReserves rootReserve companionReserve X) := by
  have hcardNat := sub_two_mul_le_card_removeRootReserves
    rootReserve companionReserve X quota m hroot hcompanion hX
  have hcard : ((m - 2 * quota : ℕ) : ℝ) ≤
      #(removeRootReserves rootReserve companionReserve X) := by
    exact_mod_cast hcardNat
  have hscaled := mul_le_mul_of_nonneg_left hcard hgap
  have hloadReal : (load : ℝ) ≤ capacity := by
    exact_mod_cast hload
  linarith

/-- For a distinguished slot the raw reservoir has exactly `quota` vertices,
so a scalar quota margin transfers without any reserve-deletion loss. -/
theorem capacity_margin_exact_quota
    (reserve : Finset B) (quota load capacity small : ℕ)
    (rho density removalBudget : ℝ)
    (hreserve : reserve.card = quota)
    (hload : load ≤ capacity)
    (hmargin :
      (capacity + small + 1 : ℝ) + removalBudget + 1 ≤
        (density - rho) * quota) :
    (load + small + 1 : ℝ) + removalBudget + 1 ≤
      (density - rho) * #reserve := by
  have hloadReal : (load : ℝ) ≤ capacity := by
    exact_mod_cast hload
  rw [hreserve]
  linarith

end Erdos547b.ZhaoClaim616RichCoordinateCapacityNumerics

#print axioms Erdos547b.ZhaoClaim616RichCoordinateCapacityNumerics.sub_two_mul_le_card_removeRootReserves
#print axioms Erdos547b.ZhaoClaim616RichCoordinateCapacityNumerics.capacity_margin_removeRootReserves
#print axioms Erdos547b.ZhaoClaim616RichCoordinateCapacityNumerics.capacity_margin_exact_quota
