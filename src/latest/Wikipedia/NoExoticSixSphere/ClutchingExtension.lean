import Wikipedia.NoExoticSixSphere.FrameGluing

/-!
# A clutching-map extension produces a global continuous frame

An extension over the southern hemisphere modifies the southern frame to match
the northern one. The two then glue on the actual closed hemisphere cover.
The existence of such an extension is not assumed without an explicit argument.
-/

namespace NoExoticSixSphere

variable {E F K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup K] [NormedSpace ℝ K]

namespace HemisphereClutching

variable (P : UnitSphere E → F →L[ℝ] F) (v : UnitSphere E)
  (aN : ContinuousRangeTransport (fun _ : ClosedHemisphere v ↦ P v)
    (fun x : ClosedHemisphere v ↦ P x.1))
  (aS : ContinuousRangeTransport (fun _ : ClosedHemisphere (antipode v) ↦ P (antipode v))
    (fun x : ClosedHemisphere (antipode v) ↦ P x.1))
  (qN : K ≃L[ℝ] (P v).range) (qS : K ≃L[ℝ] (P (antipode v)).range)
  (hP : IsIdempotentElem (P (antipode v)))
  (g : C(ClosedHemisphere (antipode v), InvertibleOperators K))
  (hg : ∀ x : Equator v, g (equatorSouth v x) = map P v aN aS qN qS hP x)

include hg in
/-- The extended coordinate change makes the two hemisphere frames agree on their overlap. -/
theorem frames_agree (x : Equator v) :
    (continuousFrameOfConstantTransport aN qN).equiv (equatorNorth v x) =
      ((continuousFrameOfConstantTransport aS qS).twist g).equiv (equatorSouth v x) := by
  apply ContinuousLinearEquiv.ext
  funext w
  change (qN.trans (aN.rangeEquiv (equatorNorth v x))) w =
    (qS.trans (aS.rangeEquiv (equatorSouth v x))) ((g (equatorSouth v x)).1 w)
  rw [hg x]
  change (qN.trans (aN.rangeEquiv (equatorNorth v x))) w =
    (qS.trans (aS.rangeEquiv (equatorSouth v x))) (equiv P v aN aS qN qS x w)
  exact ((qS.trans (aS.rangeEquiv (equatorSouth v x))).apply_symm_apply _).symm

/-- A continuous extension of the actual clutching map yields an actual global frame. -/
noncomputable def frameOfExtension : ContinuousRangeFrame P K :=
  ContinuousRangeFrame.glue (closedHemisphere v) (closedHemisphere (antipode v))
    (ClosedHemisphere.isClosed v) (ClosedHemisphere.isClosed (antipode v)) (hemispheres_cover v)
    (continuousFrameOfConstantTransport aN qN)
    ((continuousFrameOfConstantTransport aS qS).twist g) (by
      intro x hx hy
      have heq : x ∈ equator v := by
        rw [← hemispheres_inter]
        exact ⟨hx, hy⟩
      exact frames_agree P v aN aS qN qS hP g hg ⟨x, heq⟩)

end HemisphereClutching

/-- Hemisphere contraction plus a clutching-map extension produces a global frame on a sphere. -/
noncomputable def sphereFrameOfClutchingExtension [FiniteDimensional ℝ E]
    (P : UnitSphere E → F →L[ℝ] F) (hP : ∀ x, IsIdempotentElem (P x)) (hc : Continuous P)
    (v : UnitSphere E) (qN : K ≃L[ℝ] (P v).range)
    (qS : K ≃L[ℝ] (P (antipode v)).range)
    (g : C(ClosedHemisphere (antipode v), InvertibleOperators K))
    (hg : ∀ x : Equator v, g (equatorSouth v x) = sphereClutchingMap P hP hc v qN qS x) :
    ContinuousRangeFrame P K :=
  HemisphereClutching.frameOfExtension P v
    (hemisphereTransport P hP hc v) (hemisphereTransport P hP hc (antipode v)) qN qS
    (hP (antipode v)) g hg

end NoExoticSixSphere
