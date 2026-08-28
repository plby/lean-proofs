import Wikipedia.NoExoticSixSphere.Hemisphere

/-!
# Continuous projection frames over closed hemispheres

The explicit hemisphere contraction gives actual continuous ambient transport
from the pole's range to every fiber on the hemisphere. This requires no smooth
structure on the hemisphere or on the intermediate homotopy slices.
-/

open unitInterval

namespace NoExoticSixSphere

variable {E F K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup K] [NormedSpace ℝ K]
  (P : UnitSphere E → F →L[ℝ] F)
  (hP : ∀ x, IsIdempotentElem (P x)) (hc : Continuous P)

include hP hc in
/-- A projection family on the sphere is continuously trivialized over each closed hemisphere. -/
theorem nonempty_hemisphereTransport (v : UnitSphere E) :
    Nonempty (ContinuousRangeTransport
      (fun _ : ClosedHemisphere v ↦ P v) (fun x : ClosedHemisphere v ↦ P x.1)) := by
  let H := (ClosedHemisphere.contraction v).symm
  let Q : I → ClosedHemisphere v → F →L[ℝ] F := fun t x ↦ P (H (t, x)).1
  have hQ : ∀ t x, IsIdempotentElem (Q t x) := fun t x ↦ hP (H (t, x)).1
  have hQc : Continuous (fun p : I × ClosedHemisphere v ↦ Q p.1 p.2) :=
    hc.comp (continuous_subtype_val.comp H.continuous)
  have hzero : Q 0 = fun _ ↦ P v := by
    funext x
    change P (H (0, x)).1 = P v
    rw [H.apply_zero]
    rfl
  have hone : Q 1 = fun x ↦ P x.1 := by
    funext x
    change P (H (1, x)).1 = P x.1
    rw [H.apply_one]
    rfl
  simpa only [hzero, hone] using nonempty_continuousRangeTransport_of_homotopy Q hQ hQc 0 1

/-- A chosen continuous hemisphere transport, constructed by contraction. -/
noncomputable def hemisphereTransport (v : UnitSphere E) :
    ContinuousRangeTransport (fun _ : ClosedHemisphere v ↦ P v)
      (fun x : ClosedHemisphere v ↦ P x.1) :=
  Classical.choice (nonempty_hemisphereTransport P hP hc v)

/-- A fixed basis at the pole extends to a continuous frame throughout its hemisphere. -/
noncomputable def hemisphereFrame (v : UnitSphere E) (q : K ≃L[ℝ] (P v).range) :
    ContinuousRangeFrame (fun x : ClosedHemisphere v ↦ P x.1) K :=
  continuousFrameOfConstantTransport (hemisphereTransport P hP hc v) q

end NoExoticSixSphere
