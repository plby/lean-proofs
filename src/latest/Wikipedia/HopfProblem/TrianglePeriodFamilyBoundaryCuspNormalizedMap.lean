import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryCuspLiftedSquare
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryCuspHeightHomotopy

/-!
# The original cusp boundary map and its actual normalized-circle model

First change only the native logarithmic height, then lift the genuine
reciprocal-coordinate and outer-circle square.  Both homotopies descend
on the entire actual mapping torus and keep every original fibre
coordinate unchanged.  The resulting equality is therefore an equality
of the literal original attachment coefficient on actual singular
homology, in every degree.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.Cusp

open SpecialPeriods SpecialPeriods.Triangle ThreefoldOverlapMappingTorus
open ThreefoldOverlapMappingTorus.Cusp SingularMayerVietoris PeriodTorusHigherHomology

attribute [local instance] triangleTorusAction triangleTorusAction_continuous

/-- The actual endpoint quotient map with the whole lifted outer curve
and the original unaltered fibre coordinate. -/
def normalizedBoundaryMap :
    C(ThreefoldOverlapMappingTorus.Cusp.Boundary, boundaryRegularData.Space) :=
  familyBoundaryMap boundaryRegularData monodromy (baseHomotopySlice nativeLiftedSquare 1)
    nativeFibreCylinder triangleCuspGenerator (nativeLiftedSquare_translate 1)
    nativeFibreCylinder_deck

/-- Its real-cylinder formula retains the actual lifted final base point. -/
@[simp] theorem normalizedBoundaryMap_mk (t : ℝ) (x : RealTorus₄) :
    normalizedBoundaryMap (MappingTorus.mk monodromy (t, x)) =
      boundaryRegularData.quotient (nativeLiftedSquare (1, t), x) := rfl

/-- The genuine whole-boundary homotopy supplied by the lifted analytic outer-circle square. -/
def heightToNormalizedHomotopy :
    (heightBoundaryMap controlledHeight).Homotopy normalizedBoundaryMap :=
  (familyBoundaryHomotopy boundaryRegularData monodromy nativeLiftedSquare
    nativeFibreCylinder triangleCuspGenerator nativeLiftedSquare_translate
    nativeFibreCylinder_deck).cast (by
      apply ContinuousMap.ext
      intro q
      obtain ⟨p, rfl⟩ := MappingTorus.mk_surjective monodromy q
      change boundaryRegularData.quotient (nativeLiftedSquare (0, p.1), p.2) =
        boundaryRegularData.quotient (baseLift controlledHeight p.1, p.2)
      rw [nativeLiftedSquare_zero]) rfl

/-- At every homotopy point the original fibre coordinate is kept exactly. -/
@[simp] theorem heightToNormalizedHomotopy_mk (s : unitInterval) (t : ℝ) (x : RealTorus₄) :
    heightToNormalizedHomotopy (s, MappingTorus.mk monodromy (t, x)) =
      boundaryRegularData.quotient (nativeLiftedSquare (s, t), x) := rfl

/-- A genuine homotopy from the literal original cusp coefficient map,
combining the actual vertical and analytic-square stages. -/
def boundaryToNormalizedHomotopy :
    (boundaryToRegularFamily none).Homotopy normalizedBoundaryMap :=
  (boundaryToRegularFamily_heightHomotopy controlledHeight).trans heightToNormalizedHomotopy

/-- The original actual cusp-to-regular homology map equals this genuine
normalized-circle map, without a supplied monodromy or matrix identification. -/
theorem boundaryRegularHomologyMap_normalized (n : ℕ) :
    boundaryRegularHomologyMap none n = singularHomologyMap normalizedBoundaryMap n :=
  homotopy_homologyMap boundaryToNormalizedHomotopy n

/-- Its projection on every cylinder representative is the actual final covering lift. -/
theorem normalizedBoundaryMap_projection_mk (t : ℝ) (x : RealTorus₄) :
    boundaryRegularData.projection (normalizedBoundaryMap (MappingTorus.mk monodromy (t, x))) =
      triangleRegularProject (nativeLiftedSquare (1, t)) := rfl

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.Cusp
