import StackExchange.Puzzling139335.N4MiddleInvolutions.Reflection.Support
import StackExchange.Puzzling139335.N4MiddleInvolutions.Basic

/-!
# A central symmetry of a reflected union swaps its actual pieces

The connected interiors put the reflected pieces on opposite sides of the
mirror. If a center of symmetry of the union lies on that mirror, its
half-turn exchanges the two actual pieces, including their common points.
-/

open Set

namespace Puzzling139335.N4MiddleInvolutions.Reflection

theorem normalValue_pointReflection (ν C x : Plane) :
    normalValue ν (AffineIsometryEquiv.pointReflection ℝ C x) =
      2 * normalValue ν C - normalValue ν x := by
  simp only [normalValue, pointReflection_coord]
  ring

theorem pointReflection_image_of_reflected_union {P Q : Set Plane}
    (hP : IsJordanRegion P) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (hinv : Function.Involutive e) (he : e '' P = Q)
    (hdis : Disjoint (interior P) (interior Q)) {ν : Plane} {k : ℝ}
    (hunit : ν 0 ^ 2 + ν 1 ^ 2 = 1)
    (hform : ∀ x, e x = x - (2 * (normalValue ν x - k)) • ν)
    {C : Plane} (hfix : e C = C)
    (hcentral : AffineIsometryEquiv.pointReflection ℝ C '' (P ∪ Q) = P ∪ Q) :
    AffineIsometryEquiv.pointReflection ℝ C '' P = Q := by
  obtain ⟨μ, c, hμ, heμ, hside⟩ :=
    exists_oriented_normal hP e he hdis hunit hform
  have hnormal (x : Plane) : normalValue μ (e x) = 2 * c - normalValue μ x := by
    rw [heμ, normalValue_reflect μ x c hμ]
  have hC : normalValue μ C = c := by
    have h := hnormal C
    rw [hfix] at h
    linarith
  have hQside : ∀ x ∈ Q, normalValue μ x ≤ c := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := he.symm ▸ hx
    rw [hnormal]
    linarith [hside y hy]
  have hback : e '' Q = P := image_back_of_involution e hinv he
  have hPofGe {x : Plane} (hx : x ∈ P ∪ Q) (hge : c ≤ normalValue μ x) : x ∈ P := by
    rcases hx with hx | hx
    · exact hx
    · have hlevel : normalValue μ x = c := le_antisymm (hQside x hx) hge
      have hxback : e x ∈ P := hback ▸ mem_image_of_mem e hx
      simpa only [fixed_of_normalValue_eq e heμ hlevel] using hxback
  have hQofLe {x : Plane} (hx : x ∈ P ∪ Q) (hle : normalValue μ x ≤ c) : x ∈ Q := by
    rcases hx with hx | hx
    · have hlevel : normalValue μ x = c := le_antisymm hle (hside x hx)
      have hxforward : e x ∈ Q := he ▸ mem_image_of_mem e hx
      simpa only [fixed_of_normalValue_eq e heμ hlevel] using hxforward
    · exact hx
  have hHmap : MapsTo (AffineIsometryEquiv.pointReflection ℝ C) (P ∪ Q) (P ∪ Q) :=
    fun x hx => hcentral ▸ mem_image_of_mem _ hx
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    apply hQofLe (hHmap (Or.inl hx))
    rw [normalValue_pointReflection, hC]
    linarith [hside x hx]
  · intro y hy
    refine ⟨AffineIsometryEquiv.pointReflection ℝ C y, ?_,
      AffineIsometryEquiv.pointReflection_involutive C y⟩
    apply hPofGe (hHmap (Or.inr hy))
    rw [normalValue_pointReflection, hC]
    linarith [hQside y hy]

/-- Axis-form version, deriving the normal coordinate from the actual
ordinary reflection. -/
theorem pointReflection_image_of_axis_reflected_union {P Q : Set Plane}
    (hP : IsJordanRegion P) (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' P = Q)
    (hdis : Disjoint (interior P) (interior Q)) (c : ℂ) (u : Circle)
    (hform : ∀ p, PlaneIsometries.complexEquiv (e p) =
      c + (u : ℂ) * starRingEnd ℂ ((PlaneIsometries.complexEquiv p - c) / (u : ℂ)))
    {C : Plane} (hfix : e C = C)
    (hcentral : AffineIsometryEquiv.pointReflection ℝ C '' (P ∪ Q) = P ∪ Q) :
    AffineIsometryEquiv.pointReflection ℝ C '' P = Q := by
  obtain ⟨ν, k, hν, heν⟩ := exists_unit_normal_form e c u hform
  exact pointReflection_image_of_reflected_union hP e
    (involutive_of_axis_form e c u hform) he hdis hν heν hfix hcentral

end Puzzling139335.N4MiddleInvolutions.Reflection
