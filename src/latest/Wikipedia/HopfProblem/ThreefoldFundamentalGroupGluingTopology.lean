import Wikipedia.HopfProblem.ThreefoldFundamentalGroupGluingTopologyBase
import Wikipedia.HopfProblem.ThreefoldFundamentalGroupGluingTopologyPreimage

/-!
# Path connectedness of the actual threefold star cover

The full regular piece, the three full filling pieces, and every genuine
regular/filling overlap are open and path connected in the constructed
threefold.  The proof uses the actual proper projection with connected
fibres and the established topology of its literal base patches.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

open FibreTopology

attribute [local instance] chartedSpace

local instance : LocallyPathConnectedSpace Space :=
  ChartedSpace.locallyPathConnectedSpace (ℂ × ComplexPlane₂) Space

/-- Connectedness pulls back through the genuine proper projection. -/
theorem projection_preimage_isConnected {s : Set TriangleCompactifiedOrbitSpace}
    (hs : IsConnected s) : IsConnected (projection ⁻¹' s) :=
  isConnected_preimage_of_proper_of_connected_fibres
    projection_proper projection_fibre_isConnected hs

/-- A connected open part of the actual base has path-connected full preimage. -/
theorem projection_preimage_isPathConnected {s : Set TriangleCompactifiedOrbitSpace}
    (hsopen : IsOpen s) (hs : IsConnected s) : IsPathConnected (projection ⁻¹' s) :=
  isPathConnected_preimage_of_proper_of_connected_fibres
    projection_proper projection_fibre_isConnected hsopen hs

theorem liftedPatch_eq_preimage (i : Index) :
    (liftedPatch i : Set Space) = projection ⁻¹'
      (specialBaseCover.patch i : Set TriangleCompactifiedOrbitSpace) := rfl

/-- All four full patches of the constructed threefold are path connected. -/
theorem liftedPatch_isPathConnected (i : Index) :
    IsPathConnected (liftedPatch i : Set Space) :=
  projection_preimage_isPathConnected (specialBaseCover.patch i).isOpen
    (specialBaseCover.patch_isPathConnected i).isConnected

theorem liftedPatch_nonempty (i : Index) : (liftedPatch i : Set Space).Nonempty :=
  (liftedPatch_isPathConnected i).nonempty

theorem liftedPatch_pathConnectedSpace (i : Index) : PathConnectedSpace (liftedPatch i) :=
  isPathConnected_iff_pathConnectedSpace.mp (liftedPatch_isPathConnected i)

/-- The overlap in the threefold is the full preimage of the punctured
coordinate disc in the actual compact base. -/
theorem liftedPatch_regular_inter_eq_preimage (i : Puncture) :
    (liftedPatch none : Set Space) ∩ liftedPatch (some i) =
      projection ⁻¹' ((regularPatch : Set TriangleCompactifiedOrbitSpace) ∩
        specialBaseCover.fillingPatch i) := rfl

/-- Each full regular/filling overlap is genuinely path connected. -/
theorem liftedPatch_regular_inter_isPathConnected (i : Puncture) :
    IsPathConnected ((liftedPatch none : Set Space) ∩ liftedPatch (some i)) :=
  projection_preimage_isPathConnected
    (regularPatch.isOpen.inter (specialBaseCover.fillingPatch i).isOpen)
    (specialBaseCover.regular_inter_fillingPatch_isPathConnected i).isConnected

theorem liftedPatch_regular_inter_nonempty (i : Puncture) :
    ((liftedPatch none : Set Space) ∩ liftedPatch (some i)).Nonempty :=
  (liftedPatch_regular_inter_isPathConnected i).nonempty

theorem liftedPatch_regular_inter_pathConnectedSpace (i : Puncture) :
    PathConnectedSpace ↥((liftedPatch none : Set Space) ∩
      (liftedPatch (some i) : Set Space)) :=
  isPathConnected_iff_pathConnectedSpace.mp (liftedPatch_regular_inter_isPathConnected i)

/-- Distinct actual fillings do not meet in the total space. -/
theorem liftedFilling_disjoint {i j : Puncture} (hij : i ≠ j) :
    Disjoint (liftedPatch (some i) : Set Space) (liftedPatch (some j)) := by
  apply Set.disjoint_left.mpr
  intro x hi hj
  exact Set.disjoint_left.mp (specialBaseCover.fillingPatch_disjoint hij) hi hj

/-- The full regular piece and three actual fillings cover the total space. -/
theorem liftedPatch_iUnion : ⋃ i : Index, (liftedPatch i : Set Space) = univ := by
  change (⋃ i : Index, projection ⁻¹'
    (specialBaseCover.patch i : Set TriangleCompactifiedOrbitSpace)) = univ
  rw [← preimage_iUnion, specialBaseCover.patch_iUnion, preimage_univ]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
