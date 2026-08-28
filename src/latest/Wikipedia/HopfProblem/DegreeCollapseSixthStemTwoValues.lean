import Wikipedia.HopfProblem.DegreeCollapseMiddleSuspensionSurjective
import Wikipedia.HopfProblem.DegreeCollapseSixthStemFourValues

/-!
# The entire original stable sixth stem has two specified possible values

All three required native desuspensions are now surjective. Consequently
the S4 stage covers the full stable sixth stem, and the existing
quaternionic-kernel calculation applies to EVERY stable class.
The alternatives are the identity and the actual third-stem square.
This proves an upper bound of two, not nontriviality or Arf detection.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.SixthStemTwoValues

open NoExoticSixSphere CubicalStableSix StableThirdComposition

theorem sphere_five_stable_surjective : Function.Surjective (ofNative (k := 3)) := by
  intro z
  obtain ⟨x, hx⟩ := SixSphereDesuspension.stable_surjective z
  obtain ⟨a, rfl⟩ := MiddleSuspensionSurjective.middle_suspension_surjective x
  exact ⟨a, (ofNative_stepHom 3 a).symm.trans hx⟩

theorem sphere_four_stable_surjective : Function.Surjective (ofNative (k := 2)) := by
  intro z
  obtain ⟨x, hx⟩ := sphere_five_stable_surjective z
  obtain ⟨a, rfl⟩ := FourSphereDesuspension.suspension_surjective x
  exact ⟨a, (ofNative_stepHom 2 a).symm.trans hx⟩

theorem stable_eq_one_or_square (z : CubicalStableSix.Group) :
    z = 1 ∨ z = stableSquare := by
  obtain ⟨x, rfl⟩ := sphere_four_stable_surjective z
  exact SixthSphereFourImage.stable_eq_one_or_square x

theorem stable_pow_two (z : CubicalStableSix.Group) : z ^ 2 = 1 := by
  rcases stable_eq_one_or_square z with h | h
  · rw [h, one_pow]
  · rw [h, stableSquare_pow_two]

def twoValues (b : Bool) : CubicalStableSix.Group := if b then stableSquare else 1

theorem twoValues_surjective : Function.Surjective twoValues := by
  intro z
  rcases stable_eq_one_or_square z with h | h
  · exact ⟨false, h.symm⟩
  · exact ⟨true, h.symm⟩

theorem card_le_two : Nat.card CubicalStableSix.Group ≤ 2 := by
  simpa only [Nat.card_eq_fintype_card, Fintype.card_bool] using
    Nat.card_le_card_of_surjective twoValues twoValues_surjective

theorem native_card_le_two (k : ℕ) (hk : 6 ≤ k) :
    Nat.card (StableSixSphereMaps.NativeStage k) ≤ 2 :=
  (Nat.card_congr (stableMulEquiv k hk).toEquiv).trans_le card_le_two

theorem native_pow_two (k : ℕ) (hk : 6 ≤ k) (c : StableSixSphereMaps.NativeStage k) :
    c ^ 2 = 1 := by
  apply (stableMulEquiv k hk).injective
  rw [map_pow, map_one]
  exact stable_pow_two _

theorem native_eq_one_or_square (k : ℕ) (c : StableSixSphereMaps.NativeStage (k + 6)) :
    c = 1 ∨ c = squareClass k := by
  rcases stable_eq_one_or_square (ofNative c) with h | h
  · exact Or.inl ((ofNative_eq_one_iff_native (by omega) c).mp h)
  · exact Or.inr ((ofNative_injective (by omega))
      (h.trans (stableSquare_eq_stage k).symm))

theorem polynomial_square_stable :
    ofNative QuaternionicHopf.suspendedSmashClass = stableSquare := by
  rw [QuaternionicHopf.suspendedSmashClass_eq]
  have hi : stableSquare⁻¹ = stableSquare := by
    apply mul_left_cancel (a := stableSquare)
    rw [mul_inv_cancel, ← pow_two, stableSquare_pow_two]
  exact SixthStemSquareComparison.stableClass_eq_inverse.trans hi

theorem stable_eq_one_or_polynomial_square (z : CubicalStableSix.Group) :
    z = 1 ∨ z = ofNative QuaternionicHopf.suspendedSmashClass := by
  rw [polynomial_square_stable]
  exact stable_eq_one_or_square z

theorem native_eight_eq_one_or_polynomial_square (c : StableSixSphereMaps.NativeStage 8) :
    c = 1 ∨ c = QuaternionicHopf.suspendedSmashClass := by
  rcases stable_eq_one_or_polynomial_square (ofNative c) with h | h
  · exact Or.inl ((ofNative_eq_one_iff_native (by decide) c).mp h)
  · exact Or.inr ((ofNative_injective (by decide)) h)


end Wikipedia.HopfProblem.DegreeCollapse.SixthStemTwoValues
