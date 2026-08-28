import Wikipedia.HopfProblem.DegreeCollapseEmbeddedHandleCell
import Wikipedia.HopfProblem.DegreeCollapseCellComponentCriterion
import Wikipedia.SmoothSixDPoincare.HandleCoreFundamentalGroupRelations

/-!

# Fundamental groups of the specified whole-handle attachment

The existing core-cell van Kampen theorem applies to the original closed
embeddings. Injectivity of the old embedding identifies its core boundary
map with the specified attaching sphere. The resulting exact kernel and
quotient therefore retain that sphere and the actual old inclusion.
Connected attaching spheres also preserve path connectedness in both
directions, without assuming simple connectivity.
-/

noncomputable section

open Set Function Metric Topology ContinuousMap

namespace Wikipedia.HopfProblem.DegreeCollapse.EmbeddedHandle

open Wikipedia.SmoothSixDPoincare PuncturedHandle MorseHandle

variable {N P R X : Type}
  [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [TopologicalSpace R] [TopologicalSpace X] [T2Space X]
  (D : EmbeddedHandle N P R X)

theorem coreBoundaryMap_eq_attaching :
    HandleCoreAttachment.coreBoundaryMap D.oldMap D.handle D.old_closed
      D.handle_closed D.face = D.attaching := by
  apply ContinuousMap.ext
  intro u
  apply D.old_closed.injective
  exact (HandleCoreAttachment.coreBoundaryMap_point D.oldMap D.handle D.old_closed
    D.handle_closed D.face u).trans (D.boundary u)

include D in
theorem pathConnected_iff [PathConnectedSpace (UnitSphere N)] :
    PathConnectedSpace X ↔ PathConnectedSpace R := by
  constructor
  · intro hX
    let : PathConnectedSpace X := hX
    let : PathConnectedSpace ↥(range D.oldMap ∪ range D.core) :=
      FundamentalGroupTools.pathConnected_of_homotopyEquiv D.coreHomotopyEquiv
    let u : UnitSphere N := Classical.arbitrary _
    let : PathConnectedSpace D.corePresentation.old :=
      MorseCancellation.cell_old_pathConnected_of_attaching_component D.corePresentation
        (D.corePresentation.attachingSphere u)
        (fun v ↦ (PathConnectedSpace.joined v u).map
          D.corePresentation.attachingSphere.continuous)
    exact FundamentalGroupTools.pathConnected_of_homotopyEquiv
      D.oldHomeomorph.toHomotopyEquiv
  · intro hR
    let : PathConnectedSpace R := hR
    exact HandleCoreAttachment.total_pathConnected D.oldMap D.handle D.old_closed
      D.handle_closed D.cover D.face

section Connected

variable [PathConnectedSpace R] [PathConnectedSpace (UnitSphere N)]

theorem old_fundamentalGroup_surjective (x : R) :
    Surjective (FundamentalGroup.map D.oldMap x) :=
  HandleCoreAttachment.old_fundamentalGroup_surjective D.oldMap D.handle D.old_closed
    D.handle_closed D.cover D.face x

theorem old_fundamentalGroup_kernel (u : UnitSphere N) :
    (FundamentalGroup.map D.oldMap (D.attaching u)).ker =
      Subgroup.normalClosure (range (FundamentalGroup.map D.attaching u)) := by
  have h := HandleCoreAttachment.old_fundamentalGroup_kernel D.oldMap D.handle D.old_closed
    D.handle_closed D.cover D.face u
  rw [D.coreBoundaryMap_eq_attaching] at h
  exact h

def fundamentalGroupQuotient (u : UnitSphere N) :
    FundamentalGroup R (D.attaching u) ⧸
      Subgroup.normalClosure (range (FundamentalGroup.map D.attaching u)) ≃*
        FundamentalGroup X (D.oldMap (D.attaching u)) :=
  QuotientGroup.liftEquiv _ (D.old_fundamentalGroup_surjective (D.attaching u))
    (D.old_fundamentalGroup_kernel u).symm

@[simp] theorem fundamentalGroupQuotient_mk (u : UnitSphere N)
    (g : FundamentalGroup R (D.attaching u)) :
    D.fundamentalGroupQuotient u (QuotientGroup.mk' _ g) =
      FundamentalGroup.map D.oldMap (D.attaching u) g := rfl

theorem old_fundamentalGroup_bijective [SimplyConnectedSpace (UnitSphere N)] (x : R) :
    Bijective (FundamentalGroup.map D.oldMap x) :=
  HandleCoreAttachment.old_fundamentalGroup_bijective D.oldMap D.handle D.old_closed
    D.handle_closed D.cover D.face x

end Connected

end Wikipedia.HopfProblem.DegreeCollapse.EmbeddedHandle
