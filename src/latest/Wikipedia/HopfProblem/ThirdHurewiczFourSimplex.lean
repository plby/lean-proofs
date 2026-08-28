import Wikipedia.HopfProblem.ThirdHurewiczFourSimplexSums
import Wikipedia.HopfProblem.ThirdHurewiczCubeSubdivisionRecovery

/-!
# The signed five-face relation in Mathlib's native third homotopy group

A continuous singular four-simplex which is based on its whole geometric
two-skeleton gives the alternating relation among its five actual faces.
The proof compares two explicit based cube fillings, uses native cube
subdivision, and identifies the five surviving ordered tetrahedra with
their original singular faces. There is no Hurewicz-injectivity hypothesis,
abstract presentation, or connectivity assumption.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.ThirdHurewicz

open FirstHurewicz

variable {X : Type} [TopologicalSpace X] {x : X}

/-- Native subdivision of the first filling recovers its two original faces. -/
theorem fourSimplexLoopA_class (τ : BasedFourSimplex x) :
    nativeCubeClass (fourSimplexLoopA τ) =
      basedThreeSimplexClass (basedFourSimplexFace τ 3) +
        basedThreeSimplexClass (basedFourSimplexFace τ 1) :=
  (nativeCubeSubdivision_class (fourSimplexLoopA τ) (fourSimplexLoopA_internal τ)).trans
    (fourSimplexTetrahedraA_sum τ)

/-- Native subdivision of the second filling recovers the other three faces. -/
theorem fourSimplexLoopB_class (τ : BasedFourSimplex x) :
    nativeCubeClass (fourSimplexLoopB τ) =
      -(basedThreeSimplexClass (basedFourSimplexFace τ 4) +
        basedThreeSimplexClass (basedFourSimplexFace τ 2) +
        basedThreeSimplexClass (basedFourSimplexFace τ 0)) :=
  (nativeCubeSubdivision_class (fourSimplexLoopB τ) (fourSimplexLoopB_internal τ)).trans
    (fourSimplexTetrahedraB_sum τ)

/-- The two-versus-three relation between the actual based three-dimensional faces. -/
theorem basedFourSimplex_pair_relation (τ : BasedFourSimplex x) :
    basedThreeSimplexClass (basedFourSimplexFace τ 3) +
        basedThreeSimplexClass (basedFourSimplexFace τ 1) =
      basedThreeSimplexClass (basedFourSimplexFace τ 4) +
        basedThreeSimplexClass (basedFourSimplexFace τ 2) +
        basedThreeSimplexClass (basedFourSimplexFace τ 0) := by
  have h := fourSimplexFillings_additiveClass τ
  rw [fourSimplexLoopA_class, fourSimplexLoopB_class, neg_neg] at h
  exact h

/-- The five-face alternating boundary relation in the original additive `π₃`. -/
theorem basedFourSimplex_boundary_relation (τ : BasedFourSimplex x) :
    basedThreeSimplexClass (basedFourSimplexFace τ 0) -
        basedThreeSimplexClass (basedFourSimplexFace τ 1) +
        basedThreeSimplexClass (basedFourSimplexFace τ 2) -
        basedThreeSimplexClass (basedFourSimplexFace τ 3) +
        basedThreeSimplexClass (basedFourSimplexFace τ 4) = 0 := by
  calc
    _ = (basedThreeSimplexClass (basedFourSimplexFace τ 4) +
        basedThreeSimplexClass (basedFourSimplexFace τ 2) +
        basedThreeSimplexClass (basedFourSimplexFace τ 0)) -
        (basedThreeSimplexClass (basedFourSimplexFace τ 3) +
        basedThreeSimplexClass (basedFourSimplexFace τ 1)) := by abel
    _ = 0 := sub_eq_zero.mpr (basedFourSimplex_pair_relation τ).symm

/-- The literal singular-chain signs `(-1)^i`, acting in native additive `π₃`. -/
theorem basedFourSimplex_signed_relation (τ : BasedFourSimplex x) :
    ∑ i : Fin 5, (-1 : ℤ) ^ i.val • basedThreeSimplexClass (basedFourSimplexFace τ i) = 0 := by
  have h := basedFourSimplex_boundary_relation τ
  simpa [Fin.sum_univ_succ, sub_eq_add_neg, add_assoc] using h

/-- A direct endpoint for the original four-simplex and facewise boundary data. -/
theorem fourSimplex_signed_relation_ofFaces (τ : C(Simplex 4, X))
    (h : ∀ i : Fin 5, ∀ s ∈ threeSimplexBoundary, (τ.comp (simplexFace 3 i)) s = x) :
    ∑ i : Fin 5, (-1 : ℤ) ^ i.val •
      basedThreeSimplexClass (⟨τ.comp (simplexFace 3 i), h i⟩ : BasedThreeSimplex x) = 0 :=
  basedFourSimplex_signed_relation (BasedFourSimplex.ofFaces τ h)

end Wikipedia.HopfProblem.ThirdHurewicz
