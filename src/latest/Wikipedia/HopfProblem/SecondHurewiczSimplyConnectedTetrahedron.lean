import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTetrahedronFaces
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTetrahedronPerimeter
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTetrahedronSubdivision

/-!
# The tetrahedron relation in Mathlib's native second homotopy group

An actual singular tetrahedron whose entire one-skeleton is based gives the
usual signed relation between its four actual triangular faces. The proof
compares two explicit fillings of the same boundary quadrilateral and then
uses genuine square subdivision. It does not invoke Hurewicz injectivity,
a presentation of the homotopy group, or any connectivity hypothesis.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

open FirstHurewicz

variable {X : Type} [TopologicalSpace X] {x : X}

/-- The two pairs of actual faces give the same native second homotopy class. -/
theorem basedTetrahedron_pair_relation (τ : BasedTetrahedron x) :
    basedTriangleClass (basedTetrahedronFace τ 3) +
        basedTriangleClass (basedTetrahedronFace τ 1) =
      basedTriangleClass (basedTetrahedronFace τ 0) +
        basedTriangleClass (basedTetrahedronFace τ 2) := by
  have hA := subdivision_additiveClass (tetrahedronQuadrilateralLoop τ)
    (tetrahedronQuadrilateralLoop_diagonal τ)
  rw [tetrahedronLowerLoop_eq_face, tetrahedronUpperLoop_eq_face] at hA
  have hB := subdivision_additiveClass (tetrahedronShiftedQuadrilateralLoop τ)
    (tetrahedronShiftedQuadrilateralLoop_diagonal τ)
  rw [tetrahedronShiftedLowerLoop_eq_face, tetrahedronShiftedUpperLoop_eq_face] at hB
  change Additive.ofMul (⟦tetrahedronShiftedQuadrilateralLoop τ⟧ : π_ 2 X x) =
    basedTriangleClass (basedTetrahedronFace τ 0) +
      basedTriangleClass (cyclicBasedTriangle
        (cyclicBasedTriangle (basedTetrahedronFace τ 2))) at hB
  simp only [basedTriangleClass_cyclic] at hB
  exact hA.symm.trans ((congrArg Additive.ofMul (tetrahedronFillings_class τ)).trans hB)

/-- The alternating sum of the four face classes is zero. -/
theorem basedTetrahedron_boundary_relation (τ : BasedTetrahedron x) :
    basedTriangleClass (basedTetrahedronFace τ 0) -
        basedTriangleClass (basedTetrahedronFace τ 1) +
        basedTriangleClass (basedTetrahedronFace τ 2) -
        basedTriangleClass (basedTetrahedronFace τ 3) = 0 := by
  calc
    _ = (basedTriangleClass (basedTetrahedronFace τ 0) +
        basedTriangleClass (basedTetrahedronFace τ 2)) -
        (basedTriangleClass (basedTetrahedronFace τ 3) +
        basedTriangleClass (basedTetrahedronFace τ 1)) := by abel
    _ = 0 := sub_eq_zero.mpr (basedTetrahedron_pair_relation τ).symm

/-- The literal singular-chain signs `(-1)^i`, acting in native additive `π₂`. -/
theorem basedTetrahedron_signed_relation (τ : BasedTetrahedron x) :
    ∑ i : Fin 4, (-1 : ℤ) ^ i.val • basedTriangleClass (basedTetrahedronFace τ i) = 0 := by
  have h := basedTetrahedron_boundary_relation τ
  simpa [Fin.sum_univ_succ, sub_eq_add_neg, add_assoc] using h

/-- The facewise version accepts the original continuous tetrahedron map directly. -/
theorem tetrahedron_signed_relation_ofFaces (τ : C(Simplex 3, X))
    (h : ∀ i : Fin 4, ∀ s ∈ triangleBoundary, (τ.comp (simplexFace 2 i)) s = x) :
    ∑ i : Fin 4, (-1 : ℤ) ^ i.val •
      basedTriangleClass (⟨τ.comp (simplexFace 2 i), h i⟩ : BasedTriangle x) = 0 :=
  basedTetrahedron_signed_relation (BasedTetrahedron.ofFaces τ h)

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
