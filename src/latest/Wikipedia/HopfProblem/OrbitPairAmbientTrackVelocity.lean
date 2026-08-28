import Wikipedia.HopfProblem.OrbitPairEmbeddedFieldExtension
import Wikipedia.HopfProblem.OrbitPairEmbeddedFamilyTrack
import Wikipedia.HopfProblem.OrbitPairFamilyTimeVelocity

/-!
# A constructed ambient field agreeing with the embedded track velocity

Apply native tangent-field extension to the proper embedded family track.
The resulting field is globally smooth on the original time-times-target
manifold and agrees pointwise with the actual time velocity of the track.
Its clock away from the track and its compact support are treated separately.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair.NativeFamily

variable {E G H K M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {J : ModelWithCorners ℝ G K} [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]
  [T2Space N] [SigmaCompactSpace N]

theorem exists_ambient_track_velocity {F : ℝ × M → N}
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F)
    (hi : ∀ t, Injective (fun x => F (t, x)))
    (himm : ∀ t x, Injective (mfderiv I J (fun y => F (t, y)) x)) :
    ∃ v : (p : ℝ × N) → TangentSpace (𝓘(ℝ, ℝ).prod J) p,
      ContMDiff (𝓘(ℝ, ℝ).prod J) (𝓘(ℝ, ℝ).prod J).tangent ∞
        (fun p => (⟨p, v p⟩ : TangentBundle (𝓘(ℝ, ℝ).prod J) (ℝ × N))) ∧
      ∀ q : ℝ × M, v (track F q) = (1, timeVelocity (I := I) (J := J) F q) := by
  have htrack : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod J) ∞ (track F) :=
    contMDiff_fst.prodMk hF
  obtain ⟨v, hv, hmatch⟩ := NativeImmersion.exists_field_extension htrack
    (isClosedEmbedding_track hF.continuous hi)
    (fun p => injective_mfderiv_track p (hF.mdifferentiableAt (by simp)) (himm p.1 p.2))
    (smooth_timeVelocity htrack)
  exact ⟨v, hv, fun q => (hmatch q).trans (timeVelocity_track hF q)⟩

end Wikipedia.HopfProblem.OrbitPair.NativeFamily
