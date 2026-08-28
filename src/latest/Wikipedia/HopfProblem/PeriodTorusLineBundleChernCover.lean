import Wikipedia.HopfProblem.PeriodTorusLineBundleChernCoverLifts
import Wikipedia.HopfProblem.PeriodTorusLineBundleChernCocycleBasic

/-!
# The actual lattice-valued edge cocycle of a period-torus covering

Lift each singular edge starting at the selected representative of its
first vertex. Its endpoint differs from the selected representative of
its second vertex by an actual period. Lifting a whole singular triangle
proves the additive edge identity. On a positively oriented straight
period loop the value is the given integral period vector.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundle.ChernCover

open FirstHurewicz

/-- The actual normalized lift of a singular edge. -/
abbrev edgeLift (p : PeriodDomain) (σ : SingularSimplex p.Torus 1) :
    C(Simplex 1, ComplexPlane₂) := simplexLift p σ

/-- The difference between the lifted endpoint and the selected endpoint
representative is in the actual period lattice. -/
theorem edge_endpoint_sub_mem_lattice (p : PeriodDomain)
    (σ : SingularSimplex p.Torus 1) :
    edgeLift p σ (stdSimplex.vertex (S := ℝ) (1 : Fin 2)) -
      vertexLift p (σ (stdSimplex.vertex (S := ℝ) (1 : Fin 2))) ∈ p.lattice := by
  apply (Submodule.Quotient.mk_eq_zero p.lattice).mp
  change p.lattice.mkQ (simplexLift p σ _ - vertexLift p (σ _)) = 0
  rw [map_sub, simplexLift_projection, vertexLift_projection, sub_self]

/-- The genuine deck displacement, as an element of the actual lattice. -/
def edgeDisplacement (p : PeriodDomain) (σ : SingularSimplex p.Torus 1) : p.lattice :=
  ⟨edgeLift p σ (stdSimplex.vertex (S := ℝ) (1 : Fin 2)) -
      vertexLift p (σ (stdSimplex.vertex (S := ℝ) (1 : Fin 2))),
    edge_endpoint_sub_mem_lattice p σ⟩

@[simp] theorem edgeDisplacement_coe (p : PeriodDomain)
    (σ : SingularSimplex p.Torus 1) :
    (edgeDisplacement p σ : ComplexPlane₂) =
      edgeLift p σ (stdSimplex.vertex (S := ℝ) (1 : Fin 2)) -
        vertexLift p (σ (stdSimplex.vertex (S := ℝ) (1 : Fin 2))) := rfl

/-- Integral coordinates of the actual lifted endpoint displacement. -/
def edgeCocycleValue (p : PeriodDomain) (σ : SingularSimplex p.Torus 1) : Lattice :=
  p.latticeEquiv (edgeDisplacement p σ)

/-- The coordinate value is precisely the actual endpoint difference. -/
theorem periodVector_edgeCocycleValue (p : PeriodDomain)
    (σ : SingularSimplex p.Torus 1) :
    p.periodVector (edgeCocycleValue p σ) =
      edgeLift p σ (stdSimplex.vertex (S := ℝ) (1 : Fin 2)) -
        vertexLift p (σ (stdSimplex.vertex (S := ℝ) (1 : Fin 2))) :=
  p.periodVector_latticeEquiv (edgeDisplacement p σ)

/-- The integral deck coordinate of an edge is uniquely determined by
its actual lifted endpoint. -/
theorem edgeCocycleValue_eq_iff (p : PeriodDomain)
    (σ : SingularSimplex p.Torus 1) (c : Lattice) :
    edgeCocycleValue p σ = c ↔
      edgeLift p σ (stdSimplex.vertex (S := ℝ) (1 : Fin 2)) =
        vertexLift p (σ (stdSimplex.vertex (S := ℝ) (1 : Fin 2))) + p.periodVector c := by
  rw [← p.periodVector_injective.eq_iff, periodVector_edgeCocycleValue]
  rw [sub_eq_iff_eq_add, add_comm (p.periodVector c)]

/-- Any actual continuous edge lift computes the same coordinate after
subtracting its initial point and the selected vertex representatives. -/
theorem periodVector_edgeCocycleValue_of_lift (p : PeriodDomain)
    (σ : SingularSimplex p.Torus 1) (Γ : C(Simplex 1, ComplexPlane₂))
    (hΓ : p.lattice.mkQ ∘ Γ = σ) :
    p.periodVector (edgeCocycleValue p σ) =
      Γ (stdSimplex.vertex (S := ℝ) (1 : Fin 2)) -
        Γ (stdSimplex.vertex (S := ℝ) (0 : Fin 2)) +
          vertexLift p (σ (stdSimplex.vertex (S := ℝ) (0 : Fin 2))) -
            vertexLift p (σ (stdSimplex.vertex (S := ℝ) (1 : Fin 2))) := by
  rw [periodVector_edgeCocycleValue]
  change simplexLift p σ _ - _ = _
  rw [simplexLift_eq_translate p σ Γ hΓ]
  abel

/-- Face coordinates can be computed using one actual lift of the whole triangle. -/
theorem periodVector_edgeCocycleValue_face (p : PeriodDomain)
    (σ : SingularSimplex p.Torus 2) (i : Fin 3) :
    p.periodVector (edgeCocycleValue p (σ.comp (simplexFace 1 i))) =
      simplexLift p σ (stdSimplex.vertex (S := ℝ) (i.succAbove (1 : Fin 2))) -
        simplexLift p σ (stdSimplex.vertex (S := ℝ) (i.succAbove (0 : Fin 2))) +
          vertexLift p (σ (stdSimplex.vertex (S := ℝ) (i.succAbove (0 : Fin 2)))) -
            vertexLift p (σ (stdSimplex.vertex (S := ℝ) (i.succAbove (1 : Fin 2)))) := by
  have hΓ : p.lattice.mkQ ∘ ((simplexLift p σ).comp (simplexFace 1 i)) =
      σ.comp (simplexFace 1 i) := by
    funext s
    exact simplexLift_projection p σ (simplexFace 1 i s)
  simpa only [ContinuousMap.comp_apply, simplexFace_vertex] using
    periodVector_edgeCocycleValue_of_lift p (σ.comp (simplexFace 1 i))
      ((simplexLift p σ).comp (simplexFace 1 i)) hΓ

/-- The actual lifted triangle proves `λ02 = λ01 + λ12`. -/
theorem edgeCocycleValue_triangle (p : PeriodDomain) (σ : SingularSimplex p.Torus 2) :
    edgeCocycleValue p (σ.comp (simplexFace 1 1)) =
      edgeCocycleValue p (σ.comp (simplexFace 1 2)) +
        edgeCocycleValue p (σ.comp (simplexFace 1 0)) := by
  apply p.periodVector_injective
  rw [map_add, periodVector_edgeCocycleValue_face, periodVector_edgeCocycleValue_face,
    periodVector_edgeCocycleValue_face]
  change simplexLift p σ (stdSimplex.vertex (2 : Fin 3)) -
      simplexLift p σ (stdSimplex.vertex (0 : Fin 3)) + vertexLift p (σ (stdSimplex.vertex 0)) -
        vertexLift p (σ (stdSimplex.vertex 2)) =
      (simplexLift p σ (stdSimplex.vertex 1) - simplexLift p σ (stdSimplex.vertex 0) +
        vertexLift p (σ (stdSimplex.vertex 0)) - vertexLift p (σ (stdSimplex.vertex 1))) +
      (simplexLift p σ (stdSimplex.vertex 2) - simplexLift p σ (stdSimplex.vertex 1) +
        vertexLift p (σ (stdSimplex.vertex 1)) - vertexLift p (σ (stdSimplex.vertex 2)))
  abel

/-- The literal edge cocycle of the genuine period universal covering. -/
def edgeCocycle (p : PeriodDomain) : ChernCocycle.EdgeCocycle p.Torus Lattice where
  toFun := edgeCocycleValue p
  triangle := edgeCocycleValue_triangle p

@[simp] theorem edgeCocycle_apply (p : PeriodDomain) (σ : SingularSimplex p.Torus 1) :
    edgeCocycle p σ = edgeCocycleValue p σ := rfl

/-- The edge `02` is already normalized as a restriction of the triangle lift. -/
theorem simplexLift_face_one (p : PeriodDomain) (σ : SingularSimplex p.Torus 2)
    (s : Simplex 1) :
    edgeLift p (σ.comp (simplexFace 1 1)) s = simplexLift p σ (simplexFace 1 1 s) := by
  rw [simplexLift_face]
  change simplexLift p σ (simplexFace 1 1 s) + vertexLift p (σ (stdSimplex.vertex 0)) -
    simplexLift p σ (stdSimplex.vertex 0) = _
  rw [simplexLift_vertex_zero]
  abel

/-- The edge `01` is already normalized as a restriction of the triangle lift. -/
theorem simplexLift_face_two (p : PeriodDomain) (σ : SingularSimplex p.Torus 2)
    (s : Simplex 1) :
    edgeLift p (σ.comp (simplexFace 1 2)) s = simplexLift p σ (simplexFace 1 2 s) := by
  rw [simplexLift_face]
  change simplexLift p σ (simplexFace 1 2 s) + vertexLift p (σ (stdSimplex.vertex 0)) -
    simplexLift p σ (stdSimplex.vertex 0) = _
  rw [simplexLift_vertex_zero]
  abel

/-- The normalized lift of edge `12` differs from the triangle's face
restriction by minus the actual period of edge `01`. -/
theorem simplexLift_face_zero (p : PeriodDomain) (σ : SingularSimplex p.Torus 2)
    (s : Simplex 1) :
    edgeLift p (σ.comp (simplexFace 1 0)) s =
      simplexLift p σ (simplexFace 1 0 s) -
        p.periodVector (edgeCocycleValue p (σ.comp (simplexFace 1 2))) := by
  rw [simplexLift_face, periodVector_edgeCocycleValue]
  rw [simplexLift_face_two, simplexFace_vertex]
  simp only [ContinuousMap.comp_apply, simplexFace_vertex]
  change simplexLift p σ (simplexFace 1 0 s) + vertexLift p (σ (stdSimplex.vertex 1)) -
      simplexLift p σ (stdSimplex.vertex 1) =
    simplexLift p σ (simplexFace 1 0 s) -
      (simplexLift p σ (stdSimplex.vertex 1) - vertexLift p (σ (stdSimplex.vertex 1)))
  abel

/-- The actual straight lifted period loop fixes both the sign and the
integral column marking of the covering cocycle. -/
@[simp] theorem edgeCocycleValue_periodLoop (p : PeriodDomain) (c : Lattice) :
    edgeCocycleValue p (pathSimplex (p.periodLoop c)) = c := by
  let Γ : C(Simplex 1, ComplexPlane₂) :=
    pathSimplex (Path.segment (0 : ComplexPlane₂) (p.periodVector c))
  have hΓ : p.lattice.mkQ ∘ Γ = pathSimplex (p.periodLoop c) := by
    funext s
    change p.lattice.mkQ (pathSimplex (Path.segment (0 : ComplexPlane₂)
      (p.periodVector c)) s) = pathSimplex (p.periodLoop c) s
    rw [pathSimplex_apply, pathSimplex_apply, p.periodLoop_apply]
    simp only [Path.segment_apply, AffineMap.lineMap_apply_module, smul_zero, zero_add]
  apply p.periodVector_injective
  rw [periodVector_edgeCocycleValue_of_lift p (pathSimplex (p.periodLoop c)) Γ hΓ]
  simp only [Γ, pathSimplex_vertex_one, pathSimplex_vertex_zero, vertexLift_zero,
    sub_zero, add_zero]

@[simp] theorem edgeCocycle_periodLoop (p : PeriodDomain) (c : Lattice) :
    edgeCocycle p (pathSimplex (p.periodLoop c)) = c := edgeCocycleValue_periodLoop p c

end Wikipedia.HopfProblem.PeriodTorusLineBundle.ChernCover
