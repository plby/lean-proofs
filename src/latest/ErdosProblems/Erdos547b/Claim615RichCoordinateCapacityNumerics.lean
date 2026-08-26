/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichCoordinateCapacityFacts

/-!
# Scalar capacity numerics for coordinate Claim 6.15

The literal rich host removes the two distinguished reserves from every
ordinary matching cluster.  This file converts the resulting two-reserve
loss into the raw-size and residual-margin inequalities used by the
coordinate hierarchy.  It contains no graph copy or embedding premise.
-/

open scoped BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim615RichCoordinateCapacityNumerics

open Finset
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoClaim615CoordinateSourceAllocation
open Erdos547b.ZhaoClaim615HierarchicalCoordinateHostPools

universe u v

variable {Bv : Type u} {I : Type v}
variable [Fintype Bv] [DecidableEq Bv] [Fintype I] [DecidableEq I]
variable (Pcluster : ClusterAssignment Bv I)
variable (Gdegree : SimpleGraph Bv) [DecidableRel Gdegree.Adj]
variable (threshold quota : ℕ)
variable (R : SimpleGraph I) [DecidableRel R.Adj]
variable (miss : ℕ)
variable
  (Q : RichClaim61Certificate Pcluster Gdegree threshold quota R
    (largeClustersAtLeast Pcluster Gdegree threshold quota) miss)

/-- The exact loss-of-two-reserves inequality in real form. -/
theorem rho_mul_card_le_remove_reserves
    (rho : ℝ) (X : Finset Bv)
    (hlarge : rho * #X + (2 * quota : ℕ) ≤ #X) :
    rho * #X ≤ #(X \ (Q.A₀ ∪ Q.B₀)) := by
  have hcardNat :=
    card_le_removeRootReserves_card_add Pcluster Gdegree threshold quota R miss
      Q X
  have hcard : (#X : ℝ) ≤
      #(X \ (Q.A₀ ∪ Q.B₀)) + (2 * quota : ℕ) := by
    exact_mod_cast hcardNat
  linarith

/-- The two distinguished slots use the exact quota, while every ordinary
slot loses at most the two quota-sized reserves. -/
theorem richSlotRaw_large
    (rho : ℝ)
    (hA : rho * #(clusterVertices Pcluster Q.A) ≤ quota)
    (hB : rho * #(clusterVertices Pcluster Q.B) ≤ quota)
    (hmatching : ∀ e : MatchingEdge Q.claim67.M, ∀ side : Fin 2,
      rho * #(slotWhole Pcluster Gdegree threshold quota R miss Q
          (Sum.inr ⟨e, side⟩)) + (2 * quota : ℕ) ≤
        #(slotWhole Pcluster Gdegree threshold quota R miss Q
          (Sum.inr ⟨e, side⟩)))
    (slot : RootSlot Pcluster Gdegree threshold quota R miss Q) :
    rho * #(slotWhole Pcluster Gdegree threshold quota R miss Q slot) ≤
      #(slotRaw Pcluster Gdegree threshold quota R miss Q slot) := by
  rcases slot with side | edgeSide
  · fin_cases side
    · simpa [slotWhole, slotRaw, Q.A₀_card] using hA
    · simpa [slotWhole, slotRaw, Q.B₀_card] using hB
  · rcases edgeSide with ⟨e, side⟩
    simpa [slotWhole, slotRaw] using
      rho_mul_card_le_remove_reserves Pcluster Gdegree threshold quota R miss Q
        rho
        (padCluster (clusterVertices Pcluster)
          (matchingEdgeEndpoint e.1 side))
        (hmatching e side)

/-- An ordinary-slot scalar margin against `whole.card - 2*quota` implies
the literal margin after deleting the two reserves. -/
theorem ordinary_margin_of_two_reserve_loss
    (rho density removalBudget : ℝ)
    (capacity small : ℕ)
    (e : MatchingEdge Q.claim67.M) (side : Fin 2)
    (hgap : 0 ≤ density - rho)
    (hmargin :
      (capacity + small + 1 : ℝ) + removalBudget + 1 ≤
        (density - rho) *
          (#(slotWhole Pcluster Gdegree threshold quota R miss Q
            (Sum.inr ⟨e, side⟩)) - 2 * quota : ℕ)) :
    (capacity + small + 1 : ℝ) + removalBudget + 1 ≤
      (density - rho) *
        #(slotRaw Pcluster Gdegree threshold quota R miss Q
          (Sum.inr ⟨e, side⟩)) := by
  have hcardNat :
      #(slotWhole Pcluster Gdegree threshold quota R miss Q
          (Sum.inr ⟨e, side⟩)) - 2 * quota ≤
        #(slotRaw Pcluster Gdegree threshold quota R miss Q
          (Sum.inr ⟨e, side⟩)) := by
    have h := slotWhole_card_le_slotRaw_card_add Pcluster Gdegree threshold
      quota R miss Q e side
    omega
  have hcard :
      ((#(slotWhole Pcluster Gdegree threshold quota R miss Q
          (Sum.inr ⟨e, side⟩)) - 2 * quota : ℕ) : ℝ) ≤
        #(slotRaw Pcluster Gdegree threshold quota R miss Q
          (Sum.inr ⟨e, side⟩)) := by
    exact_mod_cast hcardNat
  exact hmargin.trans (mul_le_mul_of_nonneg_left hcard hgap)

/-- A distinguished-slot scalar quota margin is its literal raw margin. -/
theorem reserve_margin_of_quota
    (rho density removalBudget : ℝ)
    (capacity small : ℕ) (side : Fin 2)
    (hmargin :
      (capacity + small + 1 : ℝ) + removalBudget + 1 ≤
        (density - rho) * quota) :
    (capacity + small + 1 : ℝ) + removalBudget + 1 ≤
      (density - rho) *
        #(slotRaw Pcluster Gdegree threshold quota R miss Q
          (Sum.inl side)) := by
  simpa only [slotRaw_reserve_card] using hmargin

end Erdos547b.ZhaoClaim615RichCoordinateCapacityNumerics

#print axioms Erdos547b.ZhaoClaim615RichCoordinateCapacityNumerics.richSlotRaw_large
#print axioms Erdos547b.ZhaoClaim615RichCoordinateCapacityNumerics.ordinary_margin_of_two_reserve_loss
