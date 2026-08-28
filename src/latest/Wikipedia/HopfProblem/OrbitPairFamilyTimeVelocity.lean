import Wikipedia.HopfProblem.OrbitPairNativeFamilyTrack
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# The native time velocity of a smooth manifold family

The time direction in the source cylinder is a smooth tangent section,
constructed from the real unit section and the spatial zero section.
Applying the actual tangent map gives the smooth velocity along the
family. For its time-retaining track the first velocity component is
exactly one.
-/

noncomputable section

open Set Function Bundle
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair.NativeFamily

variable {E G H K M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]

theorem smooth_timeSection :
    ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I).tangent ∞
      (fun p : ℝ × M => (⟨p, (1, 0)⟩ : TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))) := by
  have hR : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).tangent) ∞
      (fun t : ℝ => (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
  have hM : ContMDiff I I.tangent ∞ (fun x : M => (⟨x, 0⟩ : TangentBundle I M)) :=
    Bundle.contMDiff_zeroSection ℝ (TangentSpace I)
  have hs : ContMDiff ((𝓘(ℝ, ℝ).tangent).prod I.tangent) (𝓘(ℝ, ℝ).prod I).tangent ∞
      (equivTangentBundleProd 𝓘(ℝ, ℝ) ℝ I M).symm :=
    contMDiff_equivTangentBundleProd_symm
  exact hs.comp ((hR.comp contMDiff_fst).prodMk (hM.comp contMDiff_snd))

def timeVelocity (F : ℝ × M → N) (p : ℝ × M) : TangentSpace J (F p) :=
  mfderiv (𝓘(ℝ, ℝ).prod I) J F p (1, 0)

theorem smooth_timeVelocity {F : ℝ × M → N}
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) J.tangent ∞
      (fun p => (⟨F p, timeVelocity (I := I) (J := J) F p⟩ : TangentBundle J N)) := by
  have hd : ContMDiff (𝓘(ℝ, ℝ).prod I).tangent J.tangent ∞
      (tangentMap (𝓘(ℝ, ℝ).prod I) J F) := hF.contMDiff_tangentMap (by simp)
  exact hd.comp smooth_timeSection

theorem timeVelocity_track {F : ℝ × M → N}
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F) (p : ℝ × M) :
    timeVelocity (I := I) (J := 𝓘(ℝ, ℝ).prod J) (track F) p =
      (1, timeVelocity (I := I) (J := J) F p) := by
  have hd : (mfderiv (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod J) (track F) p :
      (ℝ × E) →L[ℝ] (ℝ × G)) =
      (ContinuousLinearMap.fst ℝ ℝ E).prod (mfderiv (𝓘(ℝ, ℝ).prod I) J F p) := by
    have h := mfderiv_prodMk (x := p) mdifferentiableAt_fst (hF.mdifferentiableAt (by simp))
    rw [mfderiv_fst] at h
    exact h
  change mfderiv (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod J) (track F) p (1, 0) = _
  rw [hd]
  rfl

end Wikipedia.HopfProblem.OrbitPair.NativeFamily
