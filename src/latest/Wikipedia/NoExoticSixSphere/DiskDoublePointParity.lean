import Wikipedia.NoExoticSixSphere.DiskDoublePointSingularBoundary
import Wikipedia.NoExoticSixSphere.DiskDoublePointInteriorCurve
import Wikipedia.NoExoticSixSphere.HalfLineInteriorChart
import Wikipedia.NoExoticSixSphere.CompactHalfLineBoundary

/-!
# Even native singularity count for the actual proper generic disk

The actual compact Hausdorff swap quotient is covered by its proved
off-diagonal and reflection-quotient charts. Coordinate zero is exactly
the actual diagonal boundary. The compact one-dimensional boundary theorem
and the original singular-boundary bijection give an even singular count.
No immersion, framing comparison, or quadratic kernel vanishing is inferred.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.DiskDoublePoints

open GLOrthonormalization InvolutionQuotient

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M) (g : Vector 4 → M)
  (hg : ∀ x ∈ closedBall 0 1, ContMDiffAt (𝓡 4) (𝓡 7) ∞ g x)
  (ρ : ℝ) (hρ1 : ρ < 1)
  (hi : ∀ x ∈ closedBall 0 1, ρ ≤ ‖x‖ → Injective (fderiv ℝ (e.toFun ∘ g) x))
  (C : Set (PartialDiffeomorph (𝓡 7) (𝓡 7) M (Vector 7) ∞))
  (hC : ∀ y : M, ∃ c ∈ C, y ∈ c.source)
  (hgen : ∀ c ∈ C, OperatorRank.RegularFourSevenOn
    (fun x ↦ fderiv ℝ (c ∘ g) x) {x | ‖x‖ < ρ ∧ g x ∈ c.source})
  (hinside : closure (points g) ⊆ ball 0 1 ×ˢ ball 0 1)
  (hreg : CompactRetractionAffineFamily.RegularDoublePointsOn g (ball 0 1) (ball 0 1) C)

include e hg hρ1 hi hC hgen hinside hreg

theorem exists_unordered_halfLine_chart (q : Unordered g) :
    ∃ d : OpenPartialHomeomorph (Unordered g) HalfLine,
      q ∈ d.source ∧ ∀ y ∈ d.source, (d y).val = 0 ↔ y ∈ diagonalOrbits g := by
  let : T2Space M := e.closedEmbedding.isEmbedding.t2Space
  by_cases hq : q ∈ diagonalOrbits g
  · obtain ⟨d, hdq, _, hiff⟩ :=
      exists_unordered_boundary_chart e g hg ρ hρ1 hi C hC hgen q hq
    exact ⟨d, hdq, hiff⟩
  · obtain ⟨c, hcq, hdis⟩ :=
      exists_unordered_chart_of_not_mem_diagonal g hg hinside C hC hreg q hq
    refine ⟨c.trans positiveHalfLine, ⟨hcq, mem_univ _⟩, ?_⟩
    intro y hy
    change Real.exp (c y) = 0 ↔ y ∈ diagonalOrbits g
    exact iff_of_false (Real.exp_ne_zero _) ((disjoint_left.mp hdis) hy.1)

theorem finite_even_singularSet : (singularSet g).Finite ∧ Even (singularSet g).ncard := by
  let := t2Space_unordered g
  let := compactSpace_unordered g
  choose d hd hzero using
    exists_unordered_halfLine_chart e g hg ρ hρ1 hi C hC hgen hinside hreg
  have hb := CurveDecomposition.finite_even_boundary_of_compact_atlas
    (diagonalOrbits g) d hd hzero
  refine ⟨GenericFourDisk.finite_singular_of_chart_jets e g hg ρ hρ1 hi C hC hgen, ?_⟩
  rw [singularBoundary_ncard e g hg ρ hρ1 hi C hC hgen]
  exact hb.2

end NoExoticSixSphere.DiskDoublePoints
