import Wikipedia.HopfProblem.PeriodTorusLineBundleChernLogCover
import Wikipedia.HopfProblem.PeriodTorusLineBundleChernCover

/-!
# Actual nonzero native bundle sections on singular edges

For each vertex choose the vector represented by its selected covering
representative and scalar one.  On each actual singular edge, its genuine
covering lift and the actual factor logarithm give a continuous nonzero
section joining these selected vertex vectors.  The three edge sections
of a singular triangle are compared in the single genuine lift of that
triangle.  In particular, the middle face uses the actual deck change,
not a prescribed cohomology coefficient.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundle.Chern

open PeriodTorusAppellHumbert PeriodTorusLineBundleClassification
open ChernCover FirstHurewicz

variable {p : PeriodDomain} (F : FactorOfAutomorphy p)

/-- The actual nonzero vector selected at a vertex of the period torus. -/
def chosenVertexVector (x : p.Torus) : (Core.data F).core.TotalSpace :=
  logCoverMap F (vertexLift p x, 0)

@[simp] theorem chosenVertexVector_proj (x : p.Torus) :
    (chosenVertexVector F x).proj = x := vertexLift_projection p x

theorem chosenVertexVector_ne_zero (x : p.Torus) :
    (chosenVertexVector F x).2 ≠ 0 := logCoverMap_ne_zero F _

/-- A continuous nonzero section along the actual singular edge. -/
def nativeEdgeSection (e : SingularSimplex p.Torus 1) :
    C(Simplex 1, (Core.data F).core.TotalSpace) where
  toFun s := logCoverMap F (edgeLift p e s,
    (simplexCoordinate 1 1 s : ℝ) •
      factorLog F (edgeDisplacement p e) (vertexLift p (e (stdSimplex.vertex 1))))
  continuous_toFun := (logCoverMap_holomorphic F).continuous.comp
    ((edgeLift p e).continuous.prodMk
      ((continuous_subtype_val.comp (simplexCoordinate 1 1).continuous).smul
        continuous_const))

@[simp] theorem nativeEdgeSection_proj (e : SingularSimplex p.Torus 1) (s : Simplex 1) :
    (nativeEdgeSection F e s).proj = e s := simplexLift_projection p e s

theorem nativeEdgeSection_ne_zero (e : SingularSimplex p.Torus 1) (s : Simplex 1) :
    (nativeEdgeSection F e s).2 ≠ 0 := logCoverMap_ne_zero F _

/-- The edge section begins at the actual selected first-vertex vector. -/
@[simp] theorem nativeEdgeSection_vertex_zero (e : SingularSimplex p.Torus 1) :
    nativeEdgeSection F e (stdSimplex.vertex (S := ℝ) (0 : Fin 2)) =
      chosenVertexVector F (e (stdSimplex.vertex 0)) := by
  simp [nativeEdgeSection, simplexCoordinate_coe, stdSimplex.vertex, edgeLift,
    chosenVertexVector]

/-- The logarithm at the endpoint gives precisely the actual deck identification. -/
@[simp] theorem nativeEdgeSection_vertex_one (e : SingularSimplex p.Torus 1) :
    nativeEdgeSection F e (stdSimplex.vertex (S := ℝ) (1 : Fin 2)) =
      chosenVertexVector F (e (stdSimplex.vertex 1)) := by
  have he : edgeLift p e (stdSimplex.vertex (S := ℝ) (1 : Fin 2)) =
      vertexLift p (e (stdSimplex.vertex 1)) + (edgeDisplacement p e : ComplexPlane₂) := by
    rw [edgeDisplacement_coe]
    abel
  have ht : (simplexCoordinate 1 1 (stdSimplex.vertex (S := ℝ) (1 : Fin 2)) : ℝ) = 1 := by
    change (Pi.single (1 : Fin 2) (1 : ℝ) : Fin 2 → ℝ) 1 = 1
    exact Pi.single_eq_same 1 1
  change logCoverMap F (_, _) = _
  rw [ht, one_smul, he]
  simpa only [logDeck, zero_add, chosenVertexVector] using
    logCoverMap_logDeck F (edgeDisplacement p e) (vertexLift p (e (stdSimplex.vertex 1)), 0)

/-- The genuine lattice displacements on the three faces satisfy the triangle law. -/
theorem edgeDisplacement_triangle (σ : SingularSimplex p.Torus 2) :
    edgeDisplacement p (σ.comp (simplexFace 1 1)) =
      edgeDisplacement p (σ.comp (simplexFace 1 2)) +
        edgeDisplacement p (σ.comp (simplexFace 1 0)) := by
  apply p.latticeEquiv.injective
  simpa only [map_add, edgeCocycleValue] using edgeCocycleValue_triangle p σ

/-- In the genuine triangle lift the edge `01` needs no frame change. -/
theorem nativeEdgeSection_face_two (σ : SingularSimplex p.Torus 2) (s : Simplex 1) :
    nativeEdgeSection F (σ.comp (simplexFace 1 2)) s =
      logCoverMap F (simplexLift p σ (simplexFace 1 2 s),
        (simplexCoordinate 1 1 s : ℝ) •
          factorLog F (edgeDisplacement p (σ.comp (simplexFace 1 2)))
            (vertexLift p (σ (stdSimplex.vertex 1)))) := by
  change logCoverMap F (_, _) = _
  rw [simplexLift_face_two]
  simp only [ContinuousMap.comp_apply, simplexFace_vertex]
  rfl

/-- In the same genuine triangle lift the edge `02` also needs no frame change. -/
theorem nativeEdgeSection_face_one (σ : SingularSimplex p.Torus 2) (s : Simplex 1) :
    nativeEdgeSection F (σ.comp (simplexFace 1 1)) s =
      logCoverMap F (simplexLift p σ (simplexFace 1 1 s),
        (simplexCoordinate 1 1 s : ℝ) •
          factorLog F (edgeDisplacement p (σ.comp (simplexFace 1 1)))
            (vertexLift p (σ (stdSimplex.vertex 2)))) := by
  change logCoverMap F (_, _) = _
  rw [simplexLift_face_one]
  simp only [ContinuousMap.comp_apply, simplexFace_vertex]
  rfl

/-- On the middle edge the actual deck transformation changes the scalar coordinate
by the logarithm of the actual factor. -/
theorem nativeEdgeSection_face_zero (σ : SingularSimplex p.Torus 2) (s : Simplex 1) :
    nativeEdgeSection F (σ.comp (simplexFace 1 0)) s =
      logCoverMap F (simplexLift p σ (simplexFace 1 0 s),
        factorLog F (edgeDisplacement p (σ.comp (simplexFace 1 2)))
            (edgeLift p (σ.comp (simplexFace 1 0)) s) +
          (simplexCoordinate 1 1 s : ℝ) •
            factorLog F (edgeDisplacement p (σ.comp (simplexFace 1 0)))
              (vertexLift p (σ (stdSimplex.vertex 2)))) := by
  let l := edgeDisplacement p (σ.comp (simplexFace 1 2))
  let m := edgeDisplacement p (σ.comp (simplexFace 1 0))
  have he : edgeLift p (σ.comp (simplexFace 1 0)) s + (l : ComplexPlane₂) =
      simplexLift p σ (simplexFace 1 0 s) := by
    rw [simplexLift_face_zero]
    change _ - p.periodVector (p.latticeEquiv l) + (l : ComplexPlane₂) = _
    rw [p.periodVector_latticeEquiv]
    abel
  have h := (logCoverMap_logDeck F l
    (edgeLift p (σ.comp (simplexFace 1 0)) s,
      (simplexCoordinate 1 1 s : ℝ) • factorLog F m
        (vertexLift p (σ (stdSimplex.vertex 2))))).symm
  dsimp only [logDeck] at h
  rw [he, add_comm ((simplexCoordinate 1 1 s : ℝ) • _)] at h
  have hi : (0 : Fin 3).succAbove (1 : Fin 2) = (2 : Fin 3) := by decide
  simpa only [nativeEdgeSection, ContinuousMap.coe_mk, ContinuousMap.comp_apply,
    simplexFace_vertex, hi, l, m] using h

end Wikipedia.HopfProblem.PeriodTorusLineBundle.Chern
