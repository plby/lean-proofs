import StackExchange.Puzzling139335.CentralRotation.BoundaryOrientation.CircleLift.Existence
import StackExchange.Puzzling139335.CentralRotation.BoundaryOrientation.CircleLift.Period

/-!
# Increasing and decreasing lifts of a circle homeomorphism

Every homeomorphism of the unit additive circle has a continuous real lift.
The lift is either strictly increasing with unit displacement, or strictly
decreasing with displacement minus one.  These are conclusions of the covering
and interval arguments, not hypotheses imposed on the homeomorphism.
-/

namespace Puzzling139335.CentralRotation.BoundaryOrientation

/-- A circle homeomorphism has a real homeomorphism lift, with one of the two
possible orientations and the corresponding unit-period identity. -/
theorem exists_monotone_homeomorph_lift
    (e : AddCircle (1 : ℝ) ≃ₜ AddCircle (1 : ℝ)) :
    ∃ G : ℝ ≃ₜ ℝ,
      (∀ t : ℝ, (G t : AddCircle (1 : ℝ)) = e (t : AddCircle (1 : ℝ))) ∧
      ((StrictMono G ∧ ∀ t : ℝ, G (t + 1) = G t + 1) ∨
        (StrictAnti G ∧ ∀ t : ℝ, G (t + 1) = G t - 1)) := by
  let r : ℝ := AddCircle.equivIco (1 : ℝ) 0 (e 0)
  have hr : (r : AddCircle (1 : ℝ)) = e 0 := AddCircle.coe_equivIco
  obtain ⟨G, _, hlift⟩ := exists_real_homeomorph_lift e r hr
  refine ⟨G, hlift, ?_⟩
  rcases G.continuous.strictMono_of_inj G.injective with hmono | hanti
  · exact Or.inl ⟨hmono, increasing_lift_add_one e G.continuous hlift hmono⟩
  · exact Or.inr ⟨hanti, decreasing_lift_add_one e G.continuous hlift hanti⟩

/-- The inverse of a real homeomorphism lift is a lift of the inverse circle
homeomorphism. -/
theorem homeomorph_inverse_lifts
    {e : AddCircle (1 : ℝ) ≃ₜ AddCircle (1 : ℝ)} {G : ℝ ≃ₜ ℝ}
    (hlift : ∀ t : ℝ, (G t : AddCircle (1 : ℝ)) = e (t : AddCircle (1 : ℝ)))
    (t : ℝ) : (G.symm t : AddCircle (1 : ℝ)) = e.symm (t : AddCircle (1 : ℝ)) := by
  apply e.injective
  rw [e.apply_symm_apply]
  simpa only [G.apply_symm_apply] using (hlift (G.symm t)).symm

/-- The two possible orientations of an arbitrary circle homeomorphism,
expressed by an actual global continuous lift to the real line. -/
theorem exists_monotone_lift
    (e : AddCircle (1 : ℝ) ≃ₜ AddCircle (1 : ℝ)) :
    ∃ φ : ℝ → ℝ, Continuous φ ∧
      (∀ t : ℝ, (φ t : AddCircle (1 : ℝ)) = e (t : AddCircle (1 : ℝ))) ∧
      ((StrictMono φ ∧ ∀ t : ℝ, φ (t + 1) = φ t + 1) ∨
        (StrictAnti φ ∧ ∀ t : ℝ, φ (t + 1) = φ t - 1)) := by
  obtain ⟨G, hlift, horder⟩ := exists_monotone_homeomorph_lift e
  exact ⟨G, G.continuous, hlift, horder⟩

end Puzzling139335.CentralRotation.BoundaryOrientation
