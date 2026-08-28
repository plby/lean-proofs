import Wikipedia.HopfProblem.CuspDoubleCurves
import Wikipedia.HopfProblem.ToricHexagon

/-!
# The source ordering of the normalization hexagon

The six curves in Lemma 9.12 of `tex/s6.tex` are numbered clockwise, whereas
`ToricComponent.hexagonRay` is numbered counterclockwise.  This file records
that change of order for the actual ray divisors and their actual toric
origins.  In particular, the source's point `P` is the upper triple point
and its point `Q` is the lower triple point of the cusp quotient.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.CuspQuotient.NormalizationCurves

open ToricCharts ToricFan ToricSpace ToricComponent Triangle

/-- The first three boundary directions in the order of Lemma 9.12. -/
def sourceDirection : Fin 3 → (Fin 2 → ℤ) :=
  ![![1, 0], ![1, -1], ![0, -1]]

/-- The unoriented double-curve indices corresponding to the source order. -/
def sourceEdgeIndex : Fin 3 → Fin 3 := ![0, 2, 1]

/-- The clockwise source numbering in the existing counterclockwise hexagon. -/
def sourceHexagonIndex : Fin 6 → Fin 6 := ![0, 5, 4, 3, 2, 1]

/-- The six rays `e₁, e₁-e₂, -e₂, -e₁, e₂-e₁, e₂`. -/
def sourceRay (i : Fin 6) : Fin 2 → ℤ := hexagonRay (sourceHexagonIndex i)

/-- The chart origin at the intersection of source curves `i` and `i+1`. -/
def sourceTriangleIndex : Fin 6 → Fin 6 := ![5, 4, 3, 2, 1, 0]

def sourceTriangle (i : Fin 6) : Triangle := zeroTriangle (sourceTriangleIndex i)

theorem sourceHexagonIndex_injective : Function.Injective sourceHexagonIndex := by decide

theorem sourceRay_injective : Function.Injective sourceRay :=
  hexagonRay_injective.comp sourceHexagonIndex_injective

theorem sourceRay_ne_zero (i : Fin 6) : sourceRay i ≠ 0 :=
  hexagonRay_ne_zero (sourceHexagonIndex i)

@[simp] theorem sourceRay_cast (k : Fin 3) :
    sourceRay (Fin.castLE (by decide : 3 ≤ 6) k) = sourceDirection k := by
  fin_cases k <;> rfl

theorem sourceDirection_eq_edgeDirection (k : Fin 3) :
    sourceDirection k =
      if k = 2 then -edgeDirection (sourceEdgeIndex k)
      else edgeDirection (sourceEdgeIndex k) := by
  fin_cases k <;> decide

theorem sourceRay_opposite (i : Fin 6) : sourceRay (i + 3) = -sourceRay i := by
  fin_cases i <;> decide

theorem sourceRay_relation (i : Fin 6) :
    sourceRay (i + 2) = sourceRay (i + 1) - sourceRay i := by
  fin_cases i <;> decide

theorem sourceTriangle_vertices (i : Fin 6) :
    range (sourceTriangle i).vertex = {0, sourceRay i, sourceRay (i + 1)} := by
  have h : Finset.univ.image (sourceTriangle i).vertex =
      {0, sourceRay i, sourceRay (i + 1)} := by
    fin_cases i <;> decide
  simpa only [Finset.coe_image, Finset.coe_univ, image_univ,
    Finset.coe_insert, Finset.coe_singleton] using
    congrArg (fun s : Finset (Fin 2 → ℤ) => (s : Set (Fin 2 → ℤ))) h

/-- The literal torus-fixed points `p₁₂, p₂₃, …, p₆₁` on `E₀`. -/
def sourceVertex (i : Fin 6) : rayDivisor 0 :=
  ⟨inclusion (sourceTriangle i) 0,
    (mem_rayDivisor_inclusion 0 (sourceTriangle i) 0).mpr
      ⟨zeroCoordinate (sourceTriangleIndex i), rfl,
        zeroTriangle_vertex (sourceTriangleIndex i)⟩⟩

@[simp] theorem sourceVertex_coe (i : Fin 6) :
    (sourceVertex i : Space) = inclusion (sourceTriangle i) 0 := rfl

theorem sourceVertex_injective : Function.Injective sourceVertex := by
  intro i j hij
  have h := (inclusion_origin_injective (sourceTriangle i) (sourceTriangle j)).mp
    (congrArg Subtype.val hij)
  have hinj : Function.Injective sourceTriangle := by decide
  exact hinj h

theorem sourceVertex_mem_boundary_iff (i : Fin 6) (v : Fin 2 → ℤ) :
    sourceVertex i ∈ componentBoundary v ↔
      v = 0 ∨ v = sourceRay i ∨ v = sourceRay (i + 1) := by
  change inclusion (sourceTriangle i) 0 ∈ rayDivisor v ↔ _
  rw [mem_rayDivisor_inclusion]
  simp only [Pi.zero_apply, true_and]
  change v ∈ range (sourceTriangle i).vertex ↔ _
  rw [sourceTriangle_vertices]
  simp only [mem_insert_iff, mem_singleton_iff]

theorem sourceVertex_mem_sourceBoundary_iff (i j : Fin 6) :
    sourceVertex i ∈ componentBoundary (sourceRay j) ↔ j = i ∨ j = i + 1 := by
  rw [sourceVertex_mem_boundary_iff]
  simp only [sourceRay_ne_zero, sourceRay_injective.eq_iff, false_or]

theorem sourceVertex_mem_boundary_left (i : Fin 6) :
    sourceVertex i ∈ componentBoundary (sourceRay i) :=
  (sourceVertex_mem_sourceBoundary_iff i i).mpr (Or.inl rfl)

theorem sourceVertex_mem_boundary_right (i : Fin 6) :
    sourceVertex i ∈ componentBoundary (sourceRay (i + 1)) :=
  (sourceVertex_mem_sourceBoundary_iff i (i + 1)).mpr (Or.inr rfl)

theorem sourceTriangle_shift_opposite (i : Fin 6) :
    (sourceTriangle i).shift (-sourceRay i) = sourceTriangle (i + 2) := by
  fin_cases i <;> decide

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)

/-- The shear identifying opposite curves carries `pᵢ,ᵢ₊₁` to `pᵢ₊₂,ᵢ₊₃`.
This holds for every correction matrix: a torus multiplier fixes an origin. -/
theorem oppositeBoundaryMap_sourceVertex (i : Fin 6) :
    (oppositeBoundaryMap C (sourceRay i)
      ⟨sourceVertex i, sourceVertex_mem_boundary_left i⟩).1 = sourceVertex (i + 2) := by
  apply Subtype.ext
  change twistedTranslate C (cuspVector (sourceRay i))
    (inclusion (sourceTriangle i) 0) = inclusion (sourceTriangle (i + 2)) 0
  rw [twistedTranslate_origin, cuspVector_cuspVector, sourceTriangle_shift_opposite]

variable (ε : ℝ) (hε : 0 < ε)

@[simp] theorem componentProjection_sourceVertex_chart (i : Fin 6) :
    componentProjection C ε hε (sourceVertex i) =
      centralChartMap C ε hε (sourceTriangle i) centralOrigin := rfl

/-- Source-even vertices represent `P`; these are upper triangles in the
existing toric atlas. -/
theorem componentProjection_sourceVertex (i : Fin 6) :
    componentProjection C ε hε (sourceVertex i) =
      if i.val % 2 = 0 then upperTriplePoint C ε hε else lowerTriplePoint C ε hε := by
  rw [componentProjection_sourceVertex_chart, centralChartMap_origin_reference]
  fin_cases i <;> rfl

theorem componentProjection_sourceVertex_eq_upper_iff (i : Fin 6) :
    componentProjection C ε hε (sourceVertex i) = upperTriplePoint C ε hε ↔
      i.val % 2 = 0 := by
  rw [componentProjection_sourceVertex]
  by_cases hi : i.val % 2 = 0
  · simp only [hi, if_true]
  · simp only [hi, if_false, triplePoints_distinct]

theorem componentProjection_sourceVertex_eq_lower_iff (i : Fin 6) :
    componentProjection C ε hε (sourceVertex i) = lowerTriplePoint C ε hε ↔
      i.val % 2 = 1 := by
  rw [componentProjection_sourceVertex]
  by_cases hi : i.val % 2 = 0
  · simp [hi, Ne.symm (triplePoints_distinct C ε hε)]
  · have hi' : i.val % 2 = 1 := by omega
    simp [hi']

/-- Equality of the six source vertex images is exactly equality of parity
in the actual quotient, with no additional vertex identifications imposed. -/
theorem componentProjection_sourceVertex_eq_iff (i j : Fin 6) :
    componentProjection C ε hε (sourceVertex i) =
      componentProjection C ε hε (sourceVertex j) ↔ i.val % 2 = j.val % 2 := by
  rw [componentProjection_sourceVertex_chart, componentProjection_sourceVertex_chart,
    centralChartMap_origin_eq_iff]
  fin_cases i <;> fin_cases j <;> decide

/-- The source's `P` is the common image of `p₁₂, p₃₄, p₅₆`. -/
theorem source_P_vertex_table :
    componentProjection C ε hε (sourceVertex 0) = upperTriplePoint C ε hε ∧
    componentProjection C ε hε (sourceVertex 2) = upperTriplePoint C ε hε ∧
    componentProjection C ε hε (sourceVertex 4) = upperTriplePoint C ε hε := by
  exact ⟨(componentProjection_sourceVertex_eq_upper_iff C ε hε 0).mpr (by decide),
    (componentProjection_sourceVertex_eq_upper_iff C ε hε 2).mpr (by decide),
    (componentProjection_sourceVertex_eq_upper_iff C ε hε 4).mpr (by decide)⟩

/-- The source's `Q` is the common image of `p₂₃, p₄₅, p₆₁`. -/
theorem source_Q_vertex_table :
    componentProjection C ε hε (sourceVertex 1) = lowerTriplePoint C ε hε ∧
    componentProjection C ε hε (sourceVertex 3) = lowerTriplePoint C ε hε ∧
    componentProjection C ε hε (sourceVertex 5) = lowerTriplePoint C ε hε := by
  exact ⟨(componentProjection_sourceVertex_eq_lower_iff C ε hε 1).mpr (by decide),
    (componentProjection_sourceVertex_eq_lower_iff C ε hε 3).mpr (by decide),
    (componentProjection_sourceVertex_eq_lower_iff C ε hε 5).mpr (by decide)⟩

end Wikipedia.HopfProblem.CuspQuotient.NormalizationCurves
