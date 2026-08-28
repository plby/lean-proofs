import Wikipedia.NoExoticSixSphere.ProjectionDiskFrame

/-!
# A full orthonormal projection frame on a compact contracted space

Transport along the supplied actual contraction produces a continuous range
frame. Rectangular Gram--Schmidt makes it orthonormal without changing any
projection range. Only the rank at the contraction point is required.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel

open GLOrthonormalization

theorem exists_projectionFrame_of_contraction {X : Type*} [TopologicalSpace X]
    [CompactSpace X] {N n : ℕ} (x₀ : X)
    (H : (ContinuousMap.id X).Homotopy (ContinuousMap.const X x₀))
    (P : C(X, Vector N →L[ℝ] Vector N)) (hP : ∀ x, IsIdempotentElem (P x))
    (hr : Module.finrank ℝ (P x₀).range = n) :
    ∃ t : C(X, Space N n), ∀ x, (t x).val.range = (P x).range := by
  let Q : unitInterval → X → Vector N →L[ℝ] Vector N := fun s x ↦ P (H (s, x))
  have hQ (s : unitInterval) (x : X) : IsIdempotentElem (Q s x) := hP (H (s, x))
  have hc : Continuous (fun z : unitInterval × X ↦ Q z.1 z.2) :=
    P.continuous.comp H.continuous
  have hzero : Q 0 = P := by
    funext x
    exact congrArg P (H.map_zero_left x)
  have hone : Q 1 = fun _ ↦ P x₀ := by
    funext x
    exact congrArg P (H.map_one_left x)
  obtain ⟨q⟩ := FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq
    (show Module.finrank ℝ (Vector n) = Module.finrank ℝ (P x₀).range by
      rw [finrank_euclideanSpace_fin, hr])
  have ha : Nonempty (ContinuousRangeFrame P (Vector n)) := by
    simpa only [hzero] using
      nonempty_continuousRangeFrame_of_homotopy Q hQ hc 1 0 (P x₀) hone q
  obtain ⟨a⟩ := ha
  exact ProjectionDisk.exists_frame_of_rangeFrame P a

end NoExoticSixSphere.Stiefel
