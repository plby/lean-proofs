import Wikipedia.HopfProblem.PeriodTorusLineBundleChernNativeEdges
import Wikipedia.HopfProblem.PeriodTorusLineBundleChernBoundaryLog

/-!
# Native boundary paths in one genuine lifted triangle

The actual nonzero edge sections define paths in the original native
bundle.  Expressing them in a single lifted singular triangle gives the
three logarithmic paths whose exponential winding was computed earlier.
The reverse edge includes a genuine exponential period; its sign is
forced by the actual positive boundary order `01,12,20`.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundle.Chern

open PeriodTorusAppellHumbert PeriodTorusLineBundleClassification
open ChernCover FirstHurewicz

variable {p : PeriodDomain} (F : FactorOfAutomorphy p)

/-- The genuine native edge section as a path between the selected vertex vectors. -/
def nativeEdgePath (e : SingularSimplex p.Torus 1) :
    Path (chosenVertexVector F (e (stdSimplex.vertex 0)))
      (chosenVertexVector F (e (stdSimplex.vertex 1))) :=
  (simplexPath (nativeEdgeSection F e)).cast
    (nativeEdgeSection_vertex_zero F e).symm (nativeEdgeSection_vertex_one F e).symm

@[simp] theorem nativeEdgePath_apply (e : SingularSimplex p.Torus 1) (t : unitInterval) :
    nativeEdgePath F e t = nativeEdgeSection F e (stdSimplexHomeomorphUnitInterval.symm t) :=
  rfl

/-- A native edge-section path on a face, with the actual triangle vertices as endpoints. -/
def nativeTriangleFacePath (σ : SingularSimplex p.Torus 2) (i : Fin 3) :
    Path (chosenVertexVector F (σ (stdSimplex.vertex (i.succAbove (0 : Fin 2)))))
      (chosenVertexVector F (σ (stdSimplex.vertex (i.succAbove (1 : Fin 2))))) :=
  (nativeEdgePath F (σ.comp (simplexFace 1 i))).cast
    (congrArg (fun x => chosenVertexVector F (σ x)) (simplexFace_vertex 1 i 0)).symm
    (congrArg (fun x => chosenVertexVector F (σ x)) (simplexFace_vertex 1 i 1)).symm

@[simp] theorem nativeTriangleFacePath_apply (σ : SingularSimplex p.Torus 2)
    (i : Fin 3) (t : unitInterval) :
    nativeTriangleFacePath F σ i t =
      nativeEdgeSection F (σ.comp (simplexFace 1 i))
        (stdSimplexHomeomorphUnitInterval.symm t) := rfl

/-- The actual normalized lift of the middle edge, with its genuine deck endpoint. -/
def triangleMiddleLift (σ : SingularSimplex p.Torus 2) :
    Path (vertexLift p (σ (stdSimplex.vertex 1)))
      (vertexLift p (σ (stdSimplex.vertex 2)) +
        (edgeDisplacement p (σ.comp (simplexFace 1 0)) : ComplexPlane₂)) :=
  (simplexPath (edgeLift p (σ.comp (simplexFace 1 0)))).cast
    (by
      rw [simplexLift_vertex_zero]
      simp only [ContinuousMap.comp_apply, simplexFace_vertex]
      rfl)
    (by
      rw [edgeDisplacement_coe]
      simp only [ContinuousMap.comp_apply, simplexFace_vertex]
      change _ + (_ - vertexLift p (σ (stdSimplex.vertex 2))) = _
      abel)

@[simp] theorem triangleMiddleLift_apply (σ : SingularSimplex p.Torus 2)
    (t : unitInterval) :
    triangleMiddleLift σ t =
      edgeLift p (σ.comp (simplexFace 1 0)) (stdSimplexHomeomorphUnitInterval.symm t) := rfl

theorem simplexCoordinate_interval_symm (t : unitInterval) :
    (simplexCoordinate 1 1 (stdSimplexHomeomorphUnitInterval.symm t) : ℝ) = (t : ℝ) := by
  change (stdSimplexHomeomorphUnitInterval (stdSimplexHomeomorphUnitInterval.symm t) : ℝ) = _
  rw [Homeomorph.apply_symm_apply]

/-- The first logarithmic segment is exactly the first native edge section. -/
theorem nativeTriangleFacePath_two_log (σ : SingularSimplex p.Torus 2) (t : unitInterval) :
    nativeTriangleFacePath F σ 2 t =
      logCoverMap F (triangleEdge01 (simplexLift p σ) t,
        Path.segment 0 (factorLog F (edgeDisplacement p (σ.comp (simplexFace 1 2)))
          (vertexLift p (σ (stdSimplex.vertex 1)))) t) := by
  rw [nativeTriangleFacePath_apply, nativeEdgeSection_face_two, simplexCoordinate_interval_symm]
  simp only [triangleEdge01_apply, Path.segment_apply, AffineMap.lineMap_apply_module,
    smul_zero, zero_add]

/-- The logarithmic middle segment is exactly the native middle-edge section
in the frame of the genuine triangle lift. -/
theorem nativeTriangleFacePath_zero_log (σ : SingularSimplex p.Torus 2) (t : unitInterval) :
    nativeTriangleFacePath F σ 0 t =
      logCoverMap F (triangleEdge12 (simplexLift p σ) t,
        factorBoundaryMiddleLog F (edgeDisplacement p (σ.comp (simplexFace 1 2)))
          (edgeDisplacement p (σ.comp (simplexFace 1 0)))
          (vertexLift p (σ (stdSimplex.vertex 1)))
          (vertexLift p (σ (stdSimplex.vertex 2))) (triangleMiddleLift σ) t) := by
  rw [nativeTriangleFacePath_apply, nativeEdgeSection_face_zero, simplexCoordinate_interval_symm]
  rfl

/-- The final logarithmic segment differs from the reverse-edge coordinate
by the actual constant exponential period. -/
theorem factorBoundaryReverseLog_exp (l m : p.lattice) (z : ComplexPlane₂)
    (t : unitInterval) :
    Complex.exp (Path.segment (factorLog F l (z + m) + factorLog F m z)
      (factorBoundaryLogEndpoint F l m z) t) =
      Complex.exp ((unitInterval.symm t : ℝ) • factorLog F (l + m) z) := by
  have hseg : Path.segment (factorLog F l (z + m) + factorLog F m z)
      (factorBoundaryLogEndpoint F l m z) t =
      (unitInterval.symm t : ℝ) • factorLog F (l + m) z +
        factorBoundaryLogEndpoint F l m z := by
    rw [Path.segment_apply]
    simp only [AffineMap.lineMap_apply_module, factorBoundaryLogEndpoint,
      Complex.real_smul, unitInterval.coe_symm_eq, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  rw [hseg, Complex.exp_add, factorBoundaryLogEndpoint_exp, mul_one]

/-- Equal genuine exponential coordinates represent the same original native vector. -/
theorem logCoverMap_eq_of_exp_eq (z : ComplexPlane₂) {a b : ℂ}
    (h : Complex.exp a = Complex.exp b) : logCoverMap F (z, a) = logCoverMap F (z, b) := by
  apply Core.toAssociated_injective F
  rw [logCoverMap_toAssociated, logCoverMap_toAssociated, h]

/-- The last logarithmic segment is exactly the reverse native edge section. -/
theorem nativeTriangleFacePath_one_symm_log (σ : SingularSimplex p.Torus 2)
    (t : unitInterval) :
    (nativeTriangleFacePath F σ 1).symm t =
      logCoverMap F ((triangleEdge02 (simplexLift p σ)).symm t,
        Path.segment
          (factorLog F (edgeDisplacement p (σ.comp (simplexFace 1 2)))
              (vertexLift p (σ (stdSimplex.vertex 2)) +
                (edgeDisplacement p (σ.comp (simplexFace 1 0)) : ComplexPlane₂)) +
            factorLog F (edgeDisplacement p (σ.comp (simplexFace 1 0)))
              (vertexLift p (σ (stdSimplex.vertex 2))))
          (factorBoundaryLogEndpoint F (edgeDisplacement p (σ.comp (simplexFace 1 2)))
            (edgeDisplacement p (σ.comp (simplexFace 1 0)))
            (vertexLift p (σ (stdSimplex.vertex 2)))) t) := by
  rw [Path.symm_apply, Function.comp_apply, nativeTriangleFacePath_apply,
    nativeEdgeSection_face_one, simplexCoordinate_interval_symm, edgeDisplacement_triangle]
  apply logCoverMap_eq_of_exp_eq
  exact (factorBoundaryReverseLog_exp F _ _ _ t).symm

end Wikipedia.HopfProblem.PeriodTorusLineBundle.Chern
