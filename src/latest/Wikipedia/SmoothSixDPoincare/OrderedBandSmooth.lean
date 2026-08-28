import Wikipedia.SmoothSixDPoincare.OrderedMorseBandData

/-!
# The retained band homeomorphism is the original smooth level identification

Its recorded pointwise agreement with the ambient diffeomorphism gives the
level-set image and reconstructs a diffeomorphism with exactly this underlying
homeomorphism. No different choice of band map is substituted.
-/

noncomputable section

open Set
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.SurgeryWindows.BandData

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
  {S : SurgeryWindows E f} {i j : Fin S.count} (B : S.BandData i j)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] in
theorem level_image :
    B.ambient '' {x : M | f x = S.upper (S.point i)} =
      {x : M | f x = S.lower (S.point j)} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (B.level_coe ⟨x, hx⟩) ▸ (B.level ⟨x, hx⟩).property
  · intro hy
    let x := B.level.symm ⟨y, hy⟩
    refine ⟨x.val, x.property, ?_⟩
    exact (B.level_coe x).symm.trans (congrArg Subtype.val (B.level.apply_symm_apply ⟨y, hy⟩))

omit [T2Space M] [CompactSpace M] in
theorem exists_levelDiffeomorph (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) :
    letI := RegularLevel.chartedSpace hf (S.data (S.point i)).upper_regular
    letI := RegularLevel.chartedSpace hf (S.data (S.point j)).lower_regular
    ∃ b : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        (S.data (S.point i)).UpperLevel (S.data (S.point j)).LowerLevel ∞,
      b.toHomeomorph = B.level := by
  let _ := RegularLevel.chartedSpace hf (S.data (S.point i)).upper_regular
  let _ := RegularLevel.chartedSpace hf (S.data (S.point j)).lower_regular
  obtain ⟨b, hb⟩ := RegularLevel.exists_levelDiffeomorph_of_ambient hf
    (S.data (S.point i)).upper_regular (S.data (S.point j)).lower_regular
      B.ambient B.level_image
  refine ⟨b, ?_⟩
  apply Homeomorph.ext
  intro x
  exact Subtype.ext ((hb x).trans (B.level_coe x).symm)

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.SurgeryWindows.BandData
