import Wikipedia.HopfProblem.CuspAxisCharts
import Wikipedia.HopfProblem.AffineSphere

/-!
# The double curves as topological Riemann spheres

The two affine axis parametrizations give a homeomorphism from the one-point
compactification of `ℂ` to each actual double curve, with the two distinguished
points mapping to its triple points. The analytic atlas is developed separately.
-/

noncomputable section

open Set Topology OnePoint
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspQuotient

open ToricCharts ToricSpace ToricFan Triangle

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

def curveCharts (i : Fin 3) : TwoAffineCharts (doubleCurve C ε hε i) where
  left z := ⟨axisMap C ε hε referenceTriangle i z,
    axisMap_mem_doubleCurve C ε hε referenceTriangle i z⟩
  right z := ⟨axisMap C ε hε (upperNeighbour i) i z,
    axisMap_mem_doubleCurve C ε hε (upperNeighbour i) i z⟩
  continuous_left := (axisMap_continuous C ε hε referenceTriangle i).subtype_mk _
  continuous_right := (axisMap_continuous C ε hε (upperNeighbour i) i).subtype_mk _
  left_injective _ _ h := axisMap_injective C ε hε referenceTriangle i (congrArg Subtype.val h)
  right_injective _ _ h := axisMap_injective C ε hε (upperNeighbour i) i (congrArg Subtype.val h)
  inversion _ hz := Subtype.ext (axisMap_inversion C ε hε i hz)
  endpoints_ne h := axisMap_reference_zero_ne_upper C ε hε i (congrArg Subtype.val h)
  covered y := by
    have hy := (doubleCurve_eq_two_axis_ranges C ε hε i).subset y.2
    obtain ⟨z, hz⟩ | ⟨z, hz⟩ := hy
    · exact Or.inl ⟨z, Subtype.ext hz⟩
    · exact Or.inr ⟨z, Subtype.ext hz⟩

variable (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

def curveSphereHomeomorph (i : Fin 3) : OnePoint ℂ ≃ₜ doubleCurve C ε hε i := by
  let := quotient_t2Space C ε hε hε1 hC hR
  exact (curveCharts C ε hε i).homeomorph

@[simp] theorem curveSphereHomeomorph_coe (i : Fin 3) (z : ℂ) :
    (curveSphereHomeomorph C ε hε hε1 hC hR i (z : OnePoint ℂ) : QuotientSpace C ε) =
      axisMap C ε hε referenceTriangle i z := rfl

@[simp] theorem curveSphereHomeomorph_zero (i : Fin 3) :
    (curveSphereHomeomorph C ε hε hε1 hC hR i (0 : ℂ) : QuotientSpace C ε) =
      lowerTriplePoint C ε hε := by
  rw [curveSphereHomeomorph_coe, axisMap_zero]
  rfl

@[simp] theorem curveSphereHomeomorph_infty (i : Fin 3) :
    (curveSphereHomeomorph C ε hε hε1 hC hR i (∞ : OnePoint ℂ) : QuotientSpace C ε) =
      upperTriplePoint C ε hε := by
  change axisMap C ε hε (upperNeighbour i) i 0 = _
  rw [axisMap_zero, centralChartMap_origin_reference, upperNeighbour_upper]
  rfl

include hε1 hC hR in
theorem curve_left_isOpenEmbedding (i : Fin 3) :
    IsOpenEmbedding (curveCharts C ε hε i).left := by
  let := quotient_t2Space C ε hε hε1 hC hR
  exact (curveCharts C ε hε i).left_isOpenEmbedding

include hε1 hC hR in
theorem curve_right_isOpenEmbedding (i : Fin 3) :
    IsOpenEmbedding (curveCharts C ε hε i).right := by
  let := quotient_t2Space C ε hε hε1 hC hR
  exact (curveCharts C ε hε i).right_isOpenEmbedding

end Wikipedia.HopfProblem.CuspQuotient
