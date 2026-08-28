import Wikipedia.NoExoticSixSphere.TimeCollarBoundaryCapKernel
import Wikipedia.NoExoticSixSphere.OpenEmbeddingCapPairing
import Wikipedia.NoExoticSixSphere.ModelAtlasTransport

/-!
# The cap kernel on an independently charted presentation of the boundary

A supplied boundary homeomorphism gives the actual inclusion into the half.
Only the auxiliary, doubly-subtyped boundary receives transported charts;
the supplied manifold retains its original atlas. The genuine cap pairing
and original homology maps identify the two kernels and their annihilators.
-/

noncomputable section

open Function ContinuousMap
open scoped Manifold ContDiff

namespace NoExoticSixSphere.TimeCollarDuality

open GLOrthonormalization
open Wikipedia.HopfProblem.DegreeCollapse Wikipedia.HopfProblem.DegreeCollapse.TimeCollar
open Wikipedia.HopfProblem.SphereHomologyCoefficients
open Wikipedia.HopfProblem.SingularMayerVietoris Wikipedia.HopfProblem.PeriodTorusHigherHomology

attribute [local instance] modHomologyModule

variable {M B X : Type} [TopologicalSpace M] [TopologicalSpace B] [TopologicalSpace X]
  {t : M → ℝ}

def presentationInclusion (h : X ≃ₜ boundary t) : C(X, NonnegativeHalf t) :=
  (subtypeInclusion (boundary t)).comp (h : C(X, boundary t))

theorem presentationInclusion_homology (h : X ≃ₜ boundary t) (p n : ℕ)
    (a : ModHomology p X n) :
    modHomologyMap p (subtypeInclusion (boundary t)) n
        (modHomologyMap p (h : C(X, boundary t)) n a) =
      modHomologyMap p (presentationInclusion h) n a :=
  (LinearMap.congr_fun
    (modHomologyMap_comp p (h : C(X, boundary t)) (subtypeInclusion (boundary t)) n) a).symm

variable [ChartedSpace (Vector 7) M] [IsManifold (𝓡 7) ∞ M] [T2Space M] [CompactSpace M]
  (C : TimeCollar t B)
  [ChartedSpace (Vector 6) X] [T2Space X] [CompactSpace X]
  [Subsingleton (SingularHomology X 2)]
  [Subsingleton (SingularHomology (NonnegativeHalf t) 2)]

local instance : Fact (Module.finrank ℝ (Vector 6) = (3 + 2) + 1) := ⟨by simp⟩

include C in
theorem presentationCapKernel_selfOrthogonal (h : X ≃ₜ boundary t)
    (b : ModHomology 2 X 3) :
    (∀ a : ModHomology 2 X 3, modHomologyMap 2 (presentationInclusion h) 3 a = 0 →
      ZeroSecondHomologyCap.pairing (E := Vector 6) X a b = 0) ↔
      modHomologyMap 2 (presentationInclusion h) 3 b = 0 := by
  let : ChartedSpace (Vector 6) (boundary t) := ModelAtlasTransport.atlas h.symm
  let : CompactSpace (boundary t) := boundaryCompactSpace C
  let : Subsingleton (SingularHomology (boundary t) 2) :=
    (homotopyEquivHomologyEquiv h.symm.toHomotopyEquiv 2).injective.subsingleton
  have hpair (a b : ModHomology 2 X 3) :=
    ZeroSecondHomologyCap.pairing_openEmbedding (E := Vector 6)
      (h : C(X, boundary t)) h.isOpenEmbedding a b
  constructor
  · intro hb
    rw [← presentationInclusion_homology h 2 3 b]
    apply (boundaryCapKernel_selfOrthogonal C _).mp
    intro a ha
    obtain ⟨a, rfl⟩ := (modHomologyHomeomorphEquiv 2 h 3).surjective a
    exact (hpair a b).trans (hb a ((presentationInclusion_homology h 2 3 a).symm.trans ha))
  · intro hb a ha
    exact (hpair a b).symm.trans
      ((boundaryCapKernel_selfOrthogonal C _).mpr
        ((presentationInclusion_homology h 2 3 b).trans hb) _
        ((presentationInclusion_homology h 2 3 a).trans ha))

end NoExoticSixSphere.TimeCollarDuality
