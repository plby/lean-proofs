/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma58CombinedResidual

/-!
# Combined residual bounds for a fixed global orientation

This is the owner-batch continuation form of the combined-deletion
bookkeeping.  It turns scalar whole-endpoint inequalities into the exact
`FixedOrientationStepData` consumed by the synchronized online recursion.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoLemma58FixedCombinedResidual

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma58OwnerLocalStep
open Erdos547b.ZhaoLemma58OwnerForbidden
open Erdos547b.ZhaoLemma58ThresholdResidualCapacity
open Erdos547b.ZhaoLemma58CombinedResidual

universe v

/-- Construct the literal fixed-orientation record from one common bound on
the permanent deletion, all earlier images, and the current forbidden set. -/
noncomputable def fixedOrientationStepDataOfCombinedBounds
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (externalParent : Fin b → B)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (whole available used bad : Fin 2 → Finset B)
    (rho density : ℝ) (reserve : Fin 2 → ℕ)
    (havailable : ∀ c, available c ⊆ whole c)
    (husedSub : ∀ c, used c ⊆ available c)
    (hbadSub : ∀ c, bad c ⊆ available c)
    (hunif : G.IsUniform rho (whole 0) (whole 1))
    (hwholeDisjoint : Disjoint (whole 0) (whole 1))
    (hdensity : density ≤ G.edgeDensity (whole 0) (whole 1))
    (hfactor : 0 ≤ density - rho)
    (hreserve : ∀ c, rho * (#(whole c) : ℝ) ≤ reserve c)
    (lossBound : Fin 2 → ℕ)
    (hloss : ∀ c,
      #(combinedDeleted whole available used bad c) ≤ lossBound c)
    (htotal : ∀ c,
      lossBound c + sideLoad F orient c + reserve c ≤ #(whole c))
    (heligible : ∀ i,
      let c := branchRootSide F orient i
      lossBound c +
          (1 + reserve c + sideLoadBefore F orient i c) ≤
        #((whole c).filter (G.Adj (externalParent i))))
    (hcomponent : ∀ i c,
      (F.size i : ℝ) + rho * (#(whole c) : ℝ) + 1 ≤
        (density - rho) *
          ((#(whole c) : ℝ) - lossBound c - sideLoad F orient c)) :
    FixedOrientationStepData F G externalParent orient whole
      (ownerCleanedLive (fun c ↦ available c \ used c) bad) rho density := by
  let deleted : Fin 2 → Finset B :=
    combinedDeleted whole available used bad
  let live : Fin 2 → Finset B := residualSide whole deleted
  let exactLoss : Fin 2 → ℕ := fun c ↦ #(deleted c)
  let D : FixedOrientationStepData F G externalParent orient whole live rho
      density := {
    reserve := reserve
    uniform := hunif
    live_subset := residualSide_subset whole deleted
    whole_disjoint := hwholeDisjoint
    density_lower := hdensity
    factor_nonneg := hfactor
    reserve_regular := hreserve
    live_capacity := by
      intro c
      have hdeleted : deleted c ⊆ whole c :=
        combinedDeleted_subset whole available used bad havailable husedSub
          hbadSub c
      have hcap : exactLoss c + sideLoad F orient c + reserve c ≤
          #(whole c) := by
        exact (Nat.add_le_add_right
          (Nat.add_le_add_right (hloss c) (sideLoad F orient c)) _).trans
            (htotal c)
      change sideLoad F orient c + reserve c ≤ #(whole c \ deleted c)
      rw [Finset.card_sdiff_of_subset hdeleted]
      change sideLoad F orient c + reserve c ≤ #(whole c) - exactLoss c
      omega
    parent_neighbours := by
      intro i
      let c := branchRootSide F orient i
      have hwhole : exactLoss c +
          (1 + reserve c + sideLoadBefore F orient i c) ≤
          #((whole c).filter (G.Adj (externalParent i))) := by
        exact (Nat.add_le_add_right (hloss c) _).trans (heligible i)
      exact residualSide_filter_card_ge_of_deleted_card_add_le G whole deleted
        (externalParent i) c
        (1 + reserve c + sideLoadBefore F orient i c) hwhole
    component_margin := by
      intro i c
      have hdeleted : deleted c ⊆ whole c :=
        combinedDeleted_subset whole available used bad havailable husedSub
          hbadSub c
      have hlossWhole : lossBound c ≤ #(whole c) := by
        have := htotal c
        omega
      have hprefix : exactLoss c ≤ #(whole c) :=
        (hloss c).trans hlossWhole
      have hliveReal : (#(live c) : ℝ) =
          (#(whole c) : ℝ) - exactLoss c := by
        change (#(residualSide whole deleted c) : ℝ) = _
        rw [residualSide, Finset.card_sdiff_of_subset hdeleted,
          Nat.cast_sub hprefix]
      have hexact : (exactLoss c : ℝ) ≤ lossBound c := by
        exact_mod_cast hloss c
      rw [hliveReal]
      calc
        (F.size i : ℝ) + rho * (#(whole c) : ℝ) + 1 ≤
            (density - rho) *
              ((#(whole c) : ℝ) - lossBound c - sideLoad F orient c) :=
          hcomponent i c
        _ ≤ (density - rho) *
              ((#(whole c) : ℝ) - exactLoss c - sideLoad F orient c) := by
          gcongr }
  have hLive : live =
      ownerCleanedLive (fun c ↦ available c \ used c) bad := by
    funext c
    exact residualSide_combinedDeleted whole available used bad havailable c
  rw [← hLive]
  exact D

/-- Package the fixed-orientation record as the generic local owner datum. -/
noncomputable def fixedOwnerLocalStepDataOfCombinedBounds
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (externalParent : Fin b → B)
    (orient : Fin b → Fin 2 ≃ Fin 2)
    (whole available used bad : Fin 2 → Finset B)
    (rho density : ℝ) (reserve : Fin 2 → ℕ)
    (havailable : ∀ c, available c ⊆ whole c)
    (husedSub : ∀ c, used c ⊆ available c)
    (hbadSub : ∀ c, bad c ⊆ available c)
    (hunif : G.IsUniform rho (whole 0) (whole 1))
    (hwholeDisjoint : Disjoint (whole 0) (whole 1))
    (hdensity : density ≤ G.edgeDensity (whole 0) (whole 1))
    (hfactor : 0 ≤ density - rho)
    (hreserve : ∀ c, rho * (#(whole c) : ℝ) ≤ reserve c)
    (lossBound : Fin 2 → ℕ)
    (hloss : ∀ c,
      #(combinedDeleted whole available used bad c) ≤ lossBound c)
    (htotal : ∀ c,
      lossBound c + sideLoad F orient c + reserve c ≤ #(whole c))
    (heligible : ∀ i,
      let c := branchRootSide F orient i
      lossBound c +
          (1 + reserve c + sideLoadBefore F orient i c) ≤
        #((whole c).filter (G.Adj (externalParent i))))
    (hcomponent : ∀ i c,
      (F.size i : ℝ) + rho * (#(whole c) : ℝ) + 1 ≤
        (density - rho) *
          ((#(whole c) : ℝ) - lossBound c - sideLoad F orient c)) :
    OwnerLocalStepData F G externalParent whole
      (ownerCleanedLive (fun c ↦ available c \ used c) bad) rho density :=
  .fixed (fixedOrientationStepDataOfCombinedBounds F G externalParent orient
    whole available used bad rho density reserve havailable husedSub hbadSub
    hunif hwholeDisjoint hdensity hfactor hreserve lossBound hloss htotal
    heligible hcomponent)

end Erdos547b.ZhaoLemma58FixedCombinedResidual

#print axioms Erdos547b.ZhaoLemma58FixedCombinedResidual.fixedOwnerLocalStepDataOfCombinedBounds
