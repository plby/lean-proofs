import Wikipedia.NoExoticSixSphere.RelativeSimplexFiberClass
import Wikipedia.NoExoticSixSphere.RelativeSimplexClassHomotopy

/-!
# Fiber classes are invariant under pair homotopies fixing the first vertex

The simplex boundary may move within the source. Its cone paths still
give a homotopy in the original inclusion fiber, and their boundary
paths remain entirely in the source. Fixing only the first vertex is
enough to retain the same fiber basepoint.
-/

noncomputable section

open Set
open scoped unitInterval
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris
open SecondHurewicz.SimplyConnected OrbitPair

namespace NoExoticSixSphere.RelativeSimplexFiberClass

open RelativeSimplexCycles RelativeFiberHomology

variable {X : Type} [TopologicalSpace X] (U : Set X) (a : U)

def liftedPairHomotopy (n : ℕ) (smp₀ smp₁ : RelativeSimplex U (n + 1))
    (hv₀ : smp₀.val (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 2))) = a.val)
    (hv₁ : smp₁.val (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 2))) = a.val)
    (H : smp₀.val.Homotopy smp₁.val)
    (hU : ∀ r s, s ∈ simplexBoundary (n + 1) → H (r, s) ∈ U)
    (hv : ∀ r, H (r, stdSimplex.vertex (S := ℝ) (0 : Fin (n + 2))) = a.val) :
    (liftedSimplex U a n smp₀ hv₀).Homotopy (liftedSimplex U a n smp₁ hv₁) := by
  let p : C(I × Simplex n, U) :=
    ⟨fun z ↦ ⟨H (z.1, simplexFace n 0 z.2),
      hU z.1 _ (simplexFace_mem_boundary n 0 z.2)⟩,
      (H.continuous.comp (continuous_fst.prodMk
        ((simplexFace n 0).continuous.comp continuous_snd))).subtype_mk _⟩
  let B : ((subtypeInclusion U).comp p).Homotopy
      (ContinuousMap.const (I × Simplex n) a.val) :=
    { toContinuousMap := H.toContinuousMap.comp ⟨fun z ↦
        (z.2.1, SimplexVertexCone.cone n (z.1, z.2.2)),
        (continuous_fst.comp continuous_snd).prodMk
          ((SimplexVertexCone.cone n).continuous.comp
            (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))⟩
      map_zero_left := fun z ↦ congrArg (fun s ↦ H (z.1, s))
        (SimplexVertexCone.cone_zero n z.2)
      map_one_left := fun z ↦
        (congrArg (fun s ↦ H (z.1, s)) (SimplexVertexCone.cone_one n z.2)).trans (hv z.1) }
  let K := HomotopyFiber.lift (subtypeInclusion U) a.val p B
  refine { toContinuousMap := K, map_zero_left := ?_, map_one_left := ?_ }
  · intro s
    apply Subtype.ext
    apply Prod.ext
    · exact Subtype.ext (H.apply_zero (simplexFace n 0 s))
    · ext t
      exact H.apply_zero (SimplexVertexCone.cone n (t, s))
  · intro s
    apply Subtype.ext
    apply Prod.ext
    · exact Subtype.ext (H.apply_one (simplexFace n 0 s))
    · ext t
      exact H.apply_one (SimplexVertexCone.cone n (t, s))

theorem liftedPairHomotopy_boundary (n : ℕ) (smp₀ smp₁ : RelativeSimplex U (n + 1))
    (hv₀ : smp₀.val (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 2))) = a.val)
    (hv₁ : smp₁.val (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 2))) = a.val)
    (H : smp₀.val.Homotopy smp₁.val)
    (hU : ∀ r s, s ∈ simplexBoundary (n + 1) → H (r, s) ∈ U)
    (hv : ∀ r, H (r, stdSimplex.vertex (S := ℝ) (0 : Fin (n + 2))) = a.val)
    (r : I) (s : Simplex n) (hs : s ∈ simplexBoundary n) :
    liftedPairHomotopy U a n smp₀ smp₁ hv₀ hv₁ H hU hv (r, s) ∈
      RelativeFiberSubspacePaths.subspace U a :=
  fun t ↦ hU r _ (SimplexVertexCone.cone_boundary n t s hs)

theorem fiberClass_eq_of_pairHomotopy (n : ℕ) (smp₀ smp₁ : RelativeSimplex U (n + 3))
    (hv₀ : smp₀.val (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 4))) = a.val)
    (hv₁ : smp₁.val (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 4))) = a.val)
    (H : smp₀.val.Homotopy smp₁.val)
    (hU : ∀ r s, s ∈ simplexBoundary (n + 3) → H (r, s) ∈ U)
    (hv : ∀ r, H (r, stdSimplex.vertex (S := ℝ) (0 : Fin (n + 4))) = a.val) :
    fiberClass U a n smp₁ hv₁ = fiberClass U a n smp₀ hv₀ := by
  unfold fiberClass
  apply congrArg (fiberHomologyEquiv U a n).symm
  exact homologyClass_eq_of_homotopy _ (n + 1) _ _
    (liftedPairHomotopy U a (n + 2) smp₀ smp₁ hv₀ hv₁ H hU hv)
    (liftedPairHomotopy_boundary U a (n + 2) smp₀ smp₁ hv₀ hv₁ H hU hv)

end NoExoticSixSphere.RelativeSimplexFiberClass
