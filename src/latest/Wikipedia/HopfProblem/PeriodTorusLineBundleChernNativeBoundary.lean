import Wikipedia.HopfProblem.PeriodTorusLineBundleChernNativePaths
import Wikipedia.HopfProblem.PeriodTorusLineBundleChernWindingClassification

/-!
# Genuine native triangle-boundary obstruction

The boundary loop is assembled from actual nonzero sections of the three
actual singular edges, in positive order `01,12,20`.  A single genuine
lift of the singular triangle supplies a frame on its whole domain.  We
prove that its boundary scalar loop is exactly the exponential loop
constructed from the actual factor logarithms.  Its covering-space
winding defines the integer obstruction, before any integer group
cocycle or cohomology class is substituted.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundle.Chern

open PeriodTorusAppellHumbert PeriodTorusLineBundleClassification
open ChernCover FirstHurewicz

variable {p : PeriodDomain} (F : FactorOfAutomorphy p)

/-- The native edge `01`, with its literal vertex endpoints. -/
abbrev nativeTriangleEdge01 (σ : SingularSimplex p.Torus 2) :
    Path (chosenVertexVector F (σ (stdSimplex.vertex 0)))
      (chosenVertexVector F (σ (stdSimplex.vertex 1))) := nativeTriangleFacePath F σ 2

/-- The native edge `12`, with its literal vertex endpoints. -/
abbrev nativeTriangleEdge12 (σ : SingularSimplex p.Torus 2) :
    Path (chosenVertexVector F (σ (stdSimplex.vertex 1)))
      (chosenVertexVector F (σ (stdSimplex.vertex 2))) := nativeTriangleFacePath F σ 0

/-- The native edge `02`, with its literal vertex endpoints. -/
abbrev nativeTriangleEdge02 (σ : SingularSimplex p.Torus 2) :
    Path (chosenVertexVector F (σ (stdSimplex.vertex 0)))
      (chosenVertexVector F (σ (stdSimplex.vertex 2))) := nativeTriangleFacePath F σ 1

/-- The loop of genuine native edge-section vectors around the actual triangle boundary. -/
def nativeTriangleBoundaryLoop (σ : SingularSimplex p.Torus 2) :
    Path (chosenVertexVector F (σ (stdSimplex.vertex 0)))
      (chosenVertexVector F (σ (stdSimplex.vertex 0))) :=
  ((nativeTriangleEdge01 F σ).trans (nativeTriangleEdge12 F σ)).trans
    (nativeTriangleEdge02 F σ).symm

/-- The boundary of the genuine lifted triangle, with the same positive order. -/
def triangleBoundaryLift (σ : SingularSimplex p.Torus 2) :
    Path (simplexLift p σ (stdSimplex.vertex 0)) (simplexLift p σ (stdSimplex.vertex 0)) :=
  ((triangleEdge01 (simplexLift p σ)).trans (triangleEdge12 (simplexLift p σ))).trans
    (triangleEdge02 (simplexLift p σ)).symm

/-- The actual scalar loop of the native boundary section in that triangle frame. -/
def nativeTriangleScalarLoop (σ : SingularSimplex p.Torus 2) : BasedLoop :=
  factorBoundaryScalarLoop F (edgeDisplacement p (σ.comp (simplexFace 1 2)))
    (edgeDisplacement p (σ.comp (simplexFace 1 0)))
    (vertexLift p (σ (stdSimplex.vertex 1))) (vertexLift p (σ (stdSimplex.vertex 2)))
    (triangleMiddleLift σ)

/-- The logarithmic coordinate paths give exactly the original native boundary vectors. -/
theorem nativeTriangleBoundaryLoop_log_coordinates (σ : SingularSimplex p.Torus 2)
    (t : unitInterval) :
    nativeTriangleBoundaryLoop F σ t =
      logCoverMap F (triangleBoundaryLift σ t,
        factorBoundaryLogPath F (edgeDisplacement p (σ.comp (simplexFace 1 2)))
          (edgeDisplacement p (σ.comp (simplexFace 1 0)))
          (vertexLift p (σ (stdSimplex.vertex 1))) (vertexLift p (σ (stdSimplex.vertex 2)))
          (triangleMiddleLift σ) t) := by
  simp only [nativeTriangleBoundaryLoop, triangleBoundaryLift, factorBoundaryLogPath,
    Path.trans_apply]
  split_ifs
  · exact nativeTriangleFacePath_two_log F σ _
  · exact nativeTriangleFacePath_zero_log F σ _
  · exact nativeTriangleFacePath_one_symm_log F σ _

/-- This is a comparison with the actual diagonal quotient, hence with the original
native bundle, not an assigned model for its obstruction. -/
theorem nativeTriangleBoundaryLoop_coordinates (σ : SingularSimplex p.Torus 2)
    (t : unitInterval) :
    nativeTriangleBoundaryLoop F σ t =
      Core.fromAssociated F (associatedMap F
        (triangleBoundaryLift σ t, (nativeTriangleScalarLoop F σ t : ℂ))) := by
  exact nativeTriangleBoundaryLoop_log_coordinates F σ t

theorem nativeTriangleBoundaryLoop_ne_zero (σ : SingularSimplex p.Torus 2)
    (t : unitInterval) : (nativeTriangleBoundaryLoop F σ t).2 ≠ 0 := by
  rw [nativeTriangleBoundaryLoop_log_coordinates]
  exact logCoverMap_ne_zero F _

/-- Projection is the literal positive boundary path of the original singular triangle. -/
theorem triangleBoundaryLift_projection (σ : SingularSimplex p.Torus 2) (t : unitInterval) :
    p.lattice.mkQ (triangleBoundaryLift σ t) =
      ((triangleEdge01 σ).trans (triangleEdge12 σ)).trans (triangleEdge02 σ).symm t := by
  simp only [triangleBoundaryLift, Path.trans_apply]
  split_ifs
  · exact simplexLift_projection p σ _
  · exact simplexLift_projection p σ _
  · exact simplexLift_projection p σ _

theorem nativeTriangleBoundaryLoop_projection (σ : SingularSimplex p.Torus 2)
    (t : unitInterval) :
    (nativeTriangleBoundaryLoop F σ t).proj =
      ((triangleEdge01 σ).trans (triangleEdge12 σ)).trans (triangleEdge02 σ).symm t := by
  rw [nativeTriangleBoundaryLoop_log_coordinates, logCoverMap_proj,
    triangleBoundaryLift_projection]

/-- The integer obstruction is the actual exponential-cover winding of the native
boundary section, expressed in the actual lifted triangle frame. -/
def triangleObstruction (σ : SingularSimplex p.Torus 2) : ℤ :=
  windingNumber (nativeTriangleScalarLoop F σ)

/-- The negative sign follows from the native boundary sections and positive winding. -/
theorem triangleObstruction_eq_neg_defect (σ : SingularSimplex p.Torus 2) :
    triangleObstruction F σ =
      -factorLogIntegerCocycle F (edgeDisplacement p (σ.comp (simplexFace 1 2)))
        (edgeDisplacement p (σ.comp (simplexFace 1 0))) :=
  windingNumber_factorBoundaryScalarLoop F _ _ _ _ _

/-- Vanishing means precisely that this actual native-boundary scalar loop is null-homotopic. -/
theorem triangleObstruction_eq_zero_iff_nullhomotopic (σ : SingularSimplex p.Torus 2) :
    triangleObstruction F σ = 0 ↔
      (nativeTriangleScalarLoop F σ).Homotopic (Path.refl puncturedOne) :=
  windingNumber_eq_zero_iff_nullhomotopic _

end Wikipedia.HopfProblem.PeriodTorusLineBundle.Chern
