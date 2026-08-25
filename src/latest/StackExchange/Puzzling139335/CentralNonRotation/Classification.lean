import StackExchange.Puzzling139335.PlaneIsometries.Chasles

/-!
# Isometries whose square is a translation

Translations, reversing isometries, and half-turns all belong to this class.
The only remaining branch is a direct rotation with coefficient different
from both one and minus one.
-/

namespace Puzzling139335.CentralNonRotation

open PlaneIsometries ComplexConjugate

theorem square_translation_of_translation (g : Plane ≃ᵃⁱ[ℝ] Plane)
    {t : Plane} (hg : ∀ x, g x = x + t) :
    ∀ x, g (g x) = x + (t + t) := by
  intro x
  rw [hg, hg, add_assoc]

theorem square_translation_of_halfTurn (c : Plane) :
    ∀ x, AffineIsometryEquiv.pointReflection ℝ c
      (AffineIsometryEquiv.pointReflection ℝ c x) = x + (0 : Plane) := by
  intro x
  rw [AffineIsometryEquiv.pointReflection_involutive (𝕜 := ℝ) c x, add_zero]

/-- Exhaustively, either the square of the isometry is a translation or its
linear part is a proper rotation other than a half-turn. -/
theorem square_translation_or_other_rotation (g : Plane ≃ᵃⁱ[ℝ] Plane) :
    (∃ v : Plane, ∀ x, g (g x) = x + v) ∨
      (∃ a : Circle, a ≠ 1 ∧ a ≠ -1 ∧
        ∀ x, complexEquiv (g x) =
          (a : ℂ) * complexEquiv x + complexEquiv (g 0)) := by
  obtain ⟨a, hg | hg⟩ := affine_complex_classification g
  · by_cases ha : a = 1
    · left
      have htranslation : ∀ x, g x = x + g 0 := by
        apply affine_direct_translation g
        simpa only [ha, Circle.coe_one, one_mul] using hg
      exact ⟨g 0 + g 0, square_translation_of_translation g htranslation⟩
    by_cases hminus : a = -1
    · left
      refine ⟨0, ?_⟩
      intro x
      apply complexEquiv.injective
      rw [hg, hg]
      simp [hminus]
    · exact Or.inr ⟨a, ha, hminus, hg⟩
  · exact Or.inl ⟨complexEquiv.symm
      (complexReversingDisplacement a (complexEquiv (g 0))),
      affine_reversing_square g a hg⟩

end Puzzling139335.CentralNonRotation
