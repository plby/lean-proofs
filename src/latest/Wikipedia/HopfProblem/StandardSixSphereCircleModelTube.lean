import Wikipedia.HopfProblem.StandardSixSphereCircleModelTubeIsometries
import Wikipedia.HopfProblem.StandardSixSphereCircleModelTubeFrontier

/-!
# The actual standard six-sphere tubular piece

The open tube is smoothly `S² × B⁴(r)` in the original atlases.  The closed
tube is homeomorphic to `S² × closedB⁴(r)` and embeds as the actual closed
normal-radius region.  Its exact frontier is marked by the previously
fixed `boundaryPoint`; the closed and open restrictions agree pointwise.

This package makes no identification of a global threefold complement.
-/

noncomputable section

namespace Wikipedia.HopfProblem.StandardSixSphereCircleModel.Tube

/-- The marked boundary is the actual topological frontier in the original sphere. -/
def frontierHomeomorph (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    BaseSphere × NormalSphere ≃ₜ ↥(frontier (closedTube r)) :=
  (boundaryHomeomorph r hr hr1).trans
    (Homeomorph.setCongr (frontier_closedTube r hr hr1).symm)

@[simp] theorem frontierHomeomorph_val (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (q : BaseSphere × NormalSphere) :
    (frontierHomeomorph r hr hr1 q).val = (boundaryPoint r hr hr1 q).val := rfl

@[simp] theorem frontierHomeomorph_val_val (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (q : BaseSphere × NormalSphere) :
    (frontierHomeomorph r hr hr1 q).val.val =
      join (boundaryBaseRadius r • q.1.val) (r • q.2.val) := rfl

def frontierIntoClosed (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (p : ↥(frontier (closedTube r))) : ↥(closedTube r) :=
  ⟨p.val, by
    have hp : p.val ∈ {p : Sphere | ‖normal p.val‖ = r} := by
      rw [← frontier_closedTube r hr hr1]
      exact p.property
    exact (show ‖normal p.val.val‖ = r from hp).le⟩

/-- The closed-tube map and its true-frontier parametrization form the exact restriction square. -/
theorem closedHomeomorph_frontier_square (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (q : BaseSphere × NormalSphere) :
    closedHomeomorph r hr1 (boundaryIntoClosed r hr q) =
      frontierIntoClosed r hr hr1 (frontierHomeomorph r hr hr1 q) :=
  closedHomeomorph_boundaryIntoClosed r hr hr1 q

theorem range_boundaryPoint_val (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    Set.range (fun q => (boundaryPoint r hr hr1 q).val) = frontier (closedTube r) := by
  change Set.range (fun q => (frontierHomeomorph r hr hr1 q).val) = frontier (closedTube r)
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact (frontierHomeomorph r hr hr1 q).property
  · intro hp
    exact ⟨(frontierHomeomorph r hr hr1).symm ⟨p, hp⟩,
      congrArg Subtype.val ((frontierHomeomorph r hr hr1).apply_symm_apply ⟨p, hp⟩)⟩

theorem isClosedEmbedding_frontierMap (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    Topology.IsClosedEmbedding (fun q => (frontierHomeomorph r hr hr1 q).val) :=
  isClosed_frontier.isClosedEmbedding_subtypeVal.comp
    (frontierHomeomorph r hr hr1).isClosedEmbedding

theorem frontierHomeomorph_equivariant (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (L : Normal ≃ₗᵢ[ℝ] Normal) (q : BaseSphere × NormalSphere) :
    Isometries.sphereMap L (frontierHomeomorph r hr hr1 q).val =
      (frontierHomeomorph r hr hr1 (boundaryDomainMap L q)).val :=
  congrArg (fun p : ↥(radiusLevel r) => p.val)
    (boundaryHomeomorph_equivariant r hr hr1 L q)

end Wikipedia.HopfProblem.StandardSixSphereCircleModel.Tube
