import Wikipedia.HopfProblem.OrbitPairCoincidenceGerm

/-! # Native coincidence transversality under a common source diffeomorphism -/

noncomputable section

open Function
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair.Coincidence

open Wikipedia.SmoothSixDPoincare

variable {E G H K X N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K}
  [TopologicalSpace X] [ChartedSpace H X]
  [TopologicalSpace N] [ChartedSpace K N]

theorem transverseAt_comp_diffeomorph_iff (D : Diffeomorph I I X X ∞)
    {u v : X → N} (x : X)
    (hu : MDifferentiableAt I J u (D x)) (hv : MDifferentiableAt I J v (D x)) :
    TransverseAt (I := I) (J := J) (u ∘ D) (v ∘ D) x ↔
      TransverseAt (I := I) (J := J) u v (D x) := by
  let A : E →L[ℝ] G := mfderiv I J u (D x)
  let B : E →L[ℝ] G := mfderiv I J v (D x)
  let C : E →L[ℝ] E := mfderiv I I D x
  let A' : E →L[ℝ] G := mfderiv I J (u ∘ D) x
  let B' : E →L[ℝ] G := mfderiv I J (v ∘ D) x
  have hA : A' = A.comp C := mfderiv_comp x hu (D.contMDiff.mdifferentiableAt (by simp))
  have hB : B' = B.comp C := mfderiv_comp x hv (D.contMDiff.mdifferentiableAt (by simp))
  have hC : Bijective C := PartialChart.bijective_mfderiv D.toPartialDiffeomorph (Set.mem_univ x)
  have he : B' - A' = (B - A).comp C := by
    rw [hA, hB]
    ext w
    rfl
  change Surjective (B' - A') ↔ Surjective (B - A)
  rw [he]
  constructor
  · intro hs z
    obtain ⟨w, hw⟩ := hs z
    exact ⟨C w, hw⟩
  · intro hs
    exact hs.comp hC.surjective

end Wikipedia.HopfProblem.OrbitPair.Coincidence
