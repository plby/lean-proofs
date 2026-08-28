import Wikipedia.NoExoticSixSphere.RelativeSimplexFiberPairHomotopy

/-!
# Boundary-fixed relative simplex homotopies preserve the actual fiber class

Apply the original homotopy to each barycentric cone path. The first
vertex stays fixed, so these are paths in the same inclusion fiber.
For a boundary point the whole cone lies in the simplex boundary, and
the lifted homotopy is literally stationary. The genuine relative prism
then proves equality of the resulting fiber-homology classes.
-/

noncomputable section

open Set
open scoped unitInterval
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris
open SecondHurewicz.SimplyConnected OrbitPair

namespace NoExoticSixSphere.RelativeSimplexFiberClass

open RelativeSimplexCycles RelativeFiberHomology

variable {X : Type} [TopologicalSpace X] (U : Set X) (a : U)

def liftedHomotopy (n : ℕ) (smp₀ smp₁ : RelativeSimplex U (n + 1))
    (hv₀ : smp₀.val (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 2))) = a.val)
    (hv₁ : smp₁.val (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 2))) = a.val)
    (H : smp₀.val.HomotopyRel smp₁.val (simplexBoundary (n + 1))) :
    (liftedSimplex U a n smp₀ hv₀).HomotopyRel
      (liftedSimplex U a n smp₁ hv₁) (simplexBoundary n) := by
  have hU (r : I) (s : Simplex (n + 1)) (hs : s ∈ simplexBoundary (n + 1)) :
      H (r, s) ∈ U := by
    rw [H.eq_fst r hs]
    exact smp₀.property s hs
  have hv (r : I) : H (r, stdSimplex.vertex (S := ℝ) (0 : Fin (n + 2))) = a.val :=
    (H.eq_fst r (SimplexVertexCone.firstVertex_mem_boundary n)).trans hv₀
  refine {
    toHomotopy := liftedPairHomotopy U a n smp₀ smp₁ hv₀ hv₁ H.toHomotopy hU hv
    prop' := ?_ }
  intro r s hs
  apply Subtype.ext
  apply Prod.ext
  · exact Subtype.ext (H.eq_fst r (simplexFace_mem_boundary n 0 s))
  · ext t
    exact H.eq_fst r (SimplexVertexCone.cone_boundary n t s hs)

theorem fiberClass_eq_of_homotopyRel (n : ℕ) (smp₀ smp₁ : RelativeSimplex U (n + 3))
    (hv₀ : smp₀.val (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 4))) = a.val)
    (hv₁ : smp₁.val (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 4))) = a.val)
    (H : smp₀.val.HomotopyRel smp₁.val (simplexBoundary (n + 3))) :
    fiberClass U a n smp₁ hv₁ = fiberClass U a n smp₀ hv₀ := by
  let K := liftedHomotopy U a (n + 2) smp₀ smp₁ hv₀ hv₁ H
  unfold fiberClass
  apply congrArg (fiberHomologyEquiv U a n).symm
  apply homologyClass_eq_of_homotopy _ (n + 1) _ _ K.toHomotopy
  intro t s hs
  change K (t, s) ∈ RelativeFiberSubspacePaths.subspace U a
  rw [K.eq_fst t hs]
  exact liftedSimplex_boundary U a (n + 2) smp₀ hv₀ s hs

end NoExoticSixSphere.RelativeSimplexFiberClass
