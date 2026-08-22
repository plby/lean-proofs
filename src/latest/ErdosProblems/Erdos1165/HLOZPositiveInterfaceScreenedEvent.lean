/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPositiveInterfaceTruncatedSharpTail

/-!
# The honest screened positive-interface event

The local sharp-window comparison applies only after the adjacent-shell
window has been reconstructed on an exact `(external trace, support)` atom.
This file takes the countable union of those literal stopped screens and
packages the resulting event as a whole cofinal interface product.

In particular, this event is not definitionally identified with an arbitrary
unbalanced `thresholdedGrowthFailure`; the complementary paths remain a
separate event which must be paid elsewhere.
-/

open Set

namespace Erdos1165.HLOZPositiveInterfaceScreenedEvent

open HLOZAllCreationCofinalConditionalSharpWindow
open HLOZAllCreationCofinalTruncatedSharpWindow
open HLOZPositiveInterfaceAggregateRecovery
open HLOZPositiveInterfaceLocalWindowData
open HLOZPositiveInterfaceTruncatedSharpTail
open LazyDecomposition
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllCreationStoppedCoordinate
open TilingPrefixedStoppedProductDisintegration
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- One cap-screened positive-interface fibre is measurable. -/
theorem measurableSet_positiveInterfaceScreenedFiber
    {t : DominoTiling} {o : Orientation} {m k externalThreshold : ℕ}
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
    (hm : 1 < m) (hk : 0 < k) (threshold : ℕ → ℕ)
    (shell bound cap : ℕ) :
    MeasurableSet (positiveInterfaceScreenedFiber eta hm hk threshold
      shell bound cap) := by
  apply measurableSet_walkLift
  exact measurableSet_prefixedTilingPreStoppingFiberEvent
    ((PositiveInterfaceFiber eta).isStoppingTime cap)
    ((PositiveInterfaceFiber eta).initial cap) t
    ((PositiveInterfaceFiber eta).start cap)
    ((PositiveInterfaceFiber eta).retained cap)
    ((PositiveInterfaceFiber eta).coordinateCap cap)
    ((PositiveInterfaceFiber eta).tail cap)
    (positiveInterfaceScreenedPredicate eta hm hk threshold shell bound cap)

/-- Every screened fibre remains in the exact support atom from which its
coordinate product was reconstructed. -/
theorem positiveInterfaceScreenedFiber_subset_atom
    {t : DominoTiling} {o : Orientation} {m k externalThreshold : ℕ}
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
    (hm : 1 < m) (hk : 0 < k) (threshold : ℕ → ℕ)
    (shell bound cap : ℕ) :
    positiveInterfaceScreenedFiber eta hm hk threshold shell bound cap ⊆
      orientedAllCreationSupportTraceAtom t o m k
        (PositiveInterfaceSupportAt t o m externalThreshold)
        eta.1.1 eta.1.2 := by
  intro s hs
  apply (PositiveInterfaceFiber eta).atom_sound cap
  exact ⟨hs.1, prefixedTilingPreStoppingFiberEvent_mono
    ((PositiveInterfaceFiber eta).stoppingTime cap)
    ((PositiveInterfaceFiber eta).initial cap) t
    ((PositiveInterfaceFiber eta).start cap)
    ((PositiveInterfaceFiber eta).retained cap)
    ((PositiveInterfaceFiber eta).tail cap)
    (fun _q hq ↦ hq.1) hs.2⟩

/-- The global event on which the honest positive-interface sharp window has
actually been reconstructed. -/
def positiveInterfaceScreenedEvent
    (t : DominoTiling) (o : Orientation) (m k externalThreshold : ℕ)
    (hm : 1 < m) (hk : 0 < k) (threshold : ℕ → ℕ)
    (shell bound : ℕ) : Set WalkPath :=
  ⋃ eta : PositiveInterfaceSupportedIndex t o m k externalThreshold,
    ⋃ cap : ℕ,
      positiveInterfaceScreenedFiber eta hm hk threshold shell bound cap

theorem measurableSet_positiveInterfaceScreenedEvent
    (t : DominoTiling) (o : Orientation) (m k externalThreshold : ℕ)
    (hm : 1 < m) (hk : 0 < k) (threshold : ℕ → ℕ)
    (shell bound : ℕ) :
    MeasurableSet (positiveInterfaceScreenedEvent t o m k externalThreshold
      hm hk threshold shell bound) := by
  apply MeasurableSet.iUnion
  intro eta
  apply MeasurableSet.iUnion
  intro cap
  exact measurableSet_positiveInterfaceScreenedFiber eta hm hk threshold
    shell bound cap

/-- The screened event is contained in the rank-creation stage. -/
theorem positiveInterfaceScreenedEvent_subset_stage_valid
    (t : DominoTiling) (o : Orientation) (m k externalThreshold : ℕ)
    (hm : 1 < m) (hk : 0 < k) (threshold : ℕ → ℕ)
    (shell bound : ℕ) :
    positiveInterfaceScreenedEvent t o m k externalThreshold hm hk threshold
        shell bound ⊆
      thresholdReachStage m k ∩ validStepWalk := by
  intro s hs
  rcases Set.mem_iUnion.mp hs with ⟨eta, hs⟩
  rcases Set.mem_iUnion.mp hs with ⟨cap, hs⟩
  rw [← iUnion_supported_orientedAllCreationSupportTraceAtom
    t o m k (PositiveInterfaceSupportAt t o m externalThreshold)]
  exact Set.mem_iUnion.mpr ⟨eta,
    positiveInterfaceScreenedFiber_subset_atom eta hm hk threshold
      shell bound cap hs⟩

/-- Inside one exact atom, membership in the global screened event recovers a
screen at some cap for that same atom. -/
theorem atom_inter_positiveInterfaceScreenedEvent_subset_localScreen
    {t : DominoTiling} {o : Orientation} {m k externalThreshold : ℕ}
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
    (hm : 1 < m) (hk : 0 < k) (threshold : ℕ → ℕ)
    (shell bound : ℕ) :
    orientedAllCreationSupportTraceAtom t o m k
          (PositiveInterfaceSupportAt t o m externalThreshold)
          eta.1.1 eta.1.2 ∩
        positiveInterfaceScreenedEvent t o m k externalThreshold hm hk
          threshold shell bound ⊆
      ⋃ cap, positiveInterfaceScreenedFiber eta hm hk threshold
        shell bound cap := by
  intro s hs
  rcases Set.mem_iUnion.mp hs.2 with ⟨eta', hs'⟩
  rcases Set.mem_iUnion.mp hs' with ⟨cap, hcap⟩
  have hatom' := positiveInterfaceScreenedFiber_subset_atom eta' hm hk
    threshold shell bound cap hcap
  have hval : eta.1 = eta'.1 := by
    by_contra hne
    have hdisjoint := pairwise_disjoint_orientedAllCreationSupportTraceAtom
      t o m k (PositiveInterfaceSupportAt t o m externalThreshold) hne
    exact Set.disjoint_left.mp hdisjoint hs.1 hatom'
  have heta : eta = eta' := Subtype.ext hval
  subst eta'
  exact Set.mem_iUnion.mpr ⟨cap, hcap⟩

/-- The exact positive-interface partition gives a concrete cofinal sharp
product for the screened event.  There is no event-probability premise. -/
noncomputable def positiveInterfaceScreenedProductData
    (t : DominoTiling) (o : Orientation) (m k externalThreshold : ℕ)
    (hm : 1 < m) (hk : 0 < k)
    (harithmetic : HLOZSharpWindowProductClosure.SharpWindowArithmeticAt m)
    (hactive : m / 2 ≤ externalThreshold)
    (threshold : ℕ → ℕ) (shell bound : ℕ) :
    OrientedAllCreationCofinalSharpWindowInterfaceProductData
      t o m k
      (positiveInterfaceScreenedEvent t o m k externalThreshold hm hk
        threshold shell bound)
      threshold shell bound where
  supportAt := PositiveInterfaceSupportAt t o m externalThreshold
  supportData := positiveInterfaceSupportData t o m k externalThreshold
  next_measurable := measurableSet_positiveInterfaceScreenedEvent t o m k
    externalThreshold hm hk threshold shell bound
  next_subset_stage_valid :=
    positiveInterfaceScreenedEvent_subset_stage_valid t o m k
      externalThreshold hm hk threshold shell bound
  tail := fun eta ↦ by
    let data := positiveInterfaceTruncatedSharpTailData eta hm hk
      harithmetic hactive
        (orientedAllCreationSupportTraceAtom t o m k
          (PositiveInterfaceSupportAt t o m externalThreshold)
          eta.1.1 eta.1.2)
        (positiveInterfaceScreenedEvent t o m k externalThreshold hm hk
          threshold shell bound)
        threshold shell bound Subset.rfl
        (atom_inter_positiveInterfaceScreenedEvent_subset_localScreen eta hm hk
          threshold shell bound)
    exact data.toCofinalData

end

end Erdos1165.HLOZPositiveInterfaceScreenedEvent
