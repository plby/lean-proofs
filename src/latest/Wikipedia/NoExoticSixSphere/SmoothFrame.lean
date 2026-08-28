import Wikipedia.NoExoticSixSphere.ProjectionHomotopy

/-!
# Smooth frames transported from a constant projection

A smooth frame here is a family of actual linear equivalences from one fixed
model space to the projection ranges, smooth after ambient inclusion. A
projection homotopy starting at a constant projection supplies such a frame.
The six-sphere application is supplied later by `NormalFraming.lean`.
-/

open scoped Manifold ContDiff

namespace NoExoticSixSphere

variable {F K : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup K] [NormedSpace ℝ K]
  {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- A global smooth frame of actual projection ranges, not merely pointwise bases. -/
structure SmoothRangeFrame (I : ModelWithCorners ℝ B H) (P : M → F →L[ℝ] F) (K : Type*)
    [NormedAddCommGroup K] [NormedSpace ℝ K] where
  equiv : ∀ x, K ≃L[ℝ] (P x).range
  smooth : ContMDiff I 𝓘(ℝ, K →L[ℝ] F) ∞
    (fun x ↦ (P x).range.subtypeL.comp (equiv x).toContinuousLinearMap)

/-- Transporting one fixed frame gives an actual smooth frame on the target ranges. -/
noncomputable def smoothFrameOfConstantTransport {P₀ : F →L[ℝ] F} {Q : M → F →L[ℝ] F}
    (a : SmoothRangeTransport I (fun _ ↦ P₀) Q) (q : K ≃L[ℝ] P₀.range) :
    SmoothRangeFrame I Q K where
  equiv x := q.trans (a.rangeEquiv x)
  smooth := by
    have heq : (fun x ↦ (Q x).range.subtypeL.comp
        (q.trans (a.rangeEquiv x)).toContinuousLinearMap) =
        (fun x ↦ (a.toFun x).comp (P₀.range.subtypeL.comp q.toContinuousLinearMap)) := by
      funext x
      apply ContinuousLinearMap.ext
      intro v
      rfl
    rw [heq]
    exact a.smooth.clm_comp contMDiff_const

variable [CompleteSpace F] [CompactSpace M]
  {T : Type*} [TopologicalSpace T] [PreconnectedSpace T]

/-- A projection homotopy from a constant family yields a global smooth frame at its endpoint. -/
theorem nonempty_smoothRangeFrame_of_homotopy (P : T → M → F →L[ℝ] F)
    (hP : ∀ t x, IsIdempotentElem (P t x))
    (hc : Continuous (fun p : T × M ↦ P p.1 p.2))
    (hs : ∀ t, ContMDiff I 𝓘(ℝ, F →L[ℝ] F) ∞ (P t))
    (s t : T) (P₀ : F →L[ℝ] F) (hstart : P s = fun _ ↦ P₀)
    (q : K ≃L[ℝ] P₀.range) : Nonempty (SmoothRangeFrame I (P t) K) := by
  have ha : Nonempty (SmoothRangeTransport I (fun _ ↦ P₀) (P t)) := by
    simpa only [hstart] using nonempty_smoothRangeTransport_of_homotopy P hP hc hs s t
  obtain ⟨a⟩ := ha
  exact ⟨smoothFrameOfConstantTransport a q⟩

end NoExoticSixSphere
