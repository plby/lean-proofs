import Wikipedia.NoExoticSixSphere.CompactManifoldEmbeddingDimension
import Wikipedia.NoExoticSixSphere.SixSphereStableCollapseData
import Wikipedia.NoExoticSixSphere.CubicalStableSixVanishing

/-!
# A candidate's actual framed collapse in fixed dimensions 13 and 7

The generic linear compression is proved, so the original smooth candidate
embeds in dimension thirteen. Its normal rank is seven, where the existing
normal-framing theorem applies. This constructs an actual map S¹³ → S⁷
and its native homotopy class, not a formal element in a replacement group.
Vanishing of the class is not asserted.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.SixSphereThirteen

open SmoothCube

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 6)) M] [IsManifold (𝓡 6) ∞ M]
  (h : M ≃ₜ Sphere 6)

def embedding : EuclideanEmbedding 6 M := by
  letI : CompactSpace M := compactSpace_of_homeomorph h
  let e := Classical.choice (nonempty_euclideanEmbedding_of_homeomorph h)
  exact e.compress 13 (by decide)

theorem embedding_dimension : (embedding h).ambientDimension = 13 := rfl

def frame : SmoothRangeFrame (𝓡 6) (embedding h).normalProjection (embedding h).NormalModel :=
  Classical.choice ((embedding h).nonempty_normalFrame_of_homeomorph_sixSphere h
    (by change 7 ≤ 7; exact le_rfl))

def collapseData : (embedding h).FramedCollapseData (frame h) := by
  letI : CompactSpace M := compactSpace_of_homeomorph h
  letI : Nonempty M := h.toEquiv.nonempty
  exact (embedding h).framedCollapseData (frame h)

def sphereMap : C(Sphere 13, Sphere 7) := (collapseData h).sphereMap

theorem sphereMap_pole : sphereMap h (spherePole 13) = spherePole 7 := by
  have hp := (collapseData h).sphereMap_infty
  simp only [sphereInfinity, euclideanOnePointSphere_infty] at hp
  exact hp

def basedMap : BasedMap 13 (Sphere 7) (spherePole 7) := ⟨sphereMap h, sphereMap_pole h⟩

def nativeClass : StableSixSphereMaps.NativeStage 5 := sphereClass (basedMap h)

def stableClass : CubicalStableSix.Group := CubicalStableSix.ofNative (nativeClass h)

theorem nativeClass_eq_original :
    nativeClass h = (collapseData h).nativeSixthStageClass
      (by rw [embedding_dimension]; decide) := rfl

theorem stableClass_eq_original :
    stableClass h = (collapseData h).cubicalStableClass
      (by rw [embedding_dimension]; decide) := rfl

theorem stableClass_eq_one_iff : stableClass h = 1 ↔
    ∃ r : ℕ, (SphereMapSuspension.iterate (sphereMap h) r).Nullhomotopic :=
  (collapseData h).cubicalStableClass_eq_one_iff_finite (by rw [embedding_dimension]; decide)

end NoExoticSixSphere.SixSphereThirteen
