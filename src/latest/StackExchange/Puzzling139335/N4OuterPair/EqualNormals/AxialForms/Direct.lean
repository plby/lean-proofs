import StackExchange.Puzzling139335.N4MiddleInvolutions.Basic
import StackExchange.Puzzling139335.PlaneIsometries

/-!
# The direct axial form and its forced center

The coordinate formula determines an actual half-turn.  It therefore
exchanges the two sets in both directions, making their union centrally
symmetric.  Horizontal invariance of that compact nonempty union fixes the
half-turn center, forcing its vertical displacement to vanish.  No action
of the horizontal reflection on the individual pieces is assumed.
-/

open Set

namespace Puzzling139335.N4OuterPair.EqualNormals.AxialForms

open N4MiddleInvolutions

/-- The direct axial coordinate form is the half-turn about its explicitly
computed center. -/
theorem direct_halfTurn_form (g : Plane ≃ᵃⁱ[ℝ] Plane) (δ : ℝ)
    (hg : ∀ p, (g p) 0 = 1 - p 0 ∧ (g p) 1 = 1 - p 1 + δ) :
    g = AffineIsometryEquiv.pointReflection ℝ (!₂[1 / 2, (1 + δ) / 2] : Plane) := by
  apply DFunLike.ext
  intro p
  apply PlaneIsometries.plane_ext
  · rw [(hg p).1, pointReflection_coord]
    change 1 - p 0 = 2 * (1 / 2 : ℝ) - p 0
    ring
  · rw [(hg p).2, pointReflection_coord]
    change 1 - p 1 + δ = 2 * ((1 + δ) / 2) - p 1
    ring

/-- Involutivity follows from the coordinate formula, independently of the
sets on which the isometry will be used. -/
theorem direct_involutive (g : Plane ≃ᵃⁱ[ℝ] Plane) (δ : ℝ)
    (hg : ∀ p, (g p) 0 = 1 - p 0 ∧ (g p) 1 = 1 - p 1 + δ) :
    Function.Involutive g := by
  rw [direct_halfTurn_form g δ hg]
  exact AffineIsometryEquiv.pointReflection_involutive
    (𝕜 := ℝ) (!₂[1 / 2, (1 + δ) / 2] : Plane)

/-- Horizontal invariance of the actual compact two-piece union forces the
half-turn's center onto the horizontal midline. -/
theorem direct_parameter_eq_zero (g : Plane ≃ᵃⁱ[ℝ] Plane) (δ : ℝ)
    (hg : ∀ p, (g p) 0 = 1 - p 0 ∧ (g p) 1 = 1 - p 1 + δ)
    {P Q : Set Plane} (hcompact : IsCompact (P ∪ Q)) (hne : (P ∪ Q).Nonempty)
    (hpair : g '' P = Q)
    (hhorizontal : ReflectionSeparation.horizontal '' (P ∪ Q) = P ∪ Q) : δ = 0 := by
  have hcentral :
      AffineIsometryEquiv.pointReflection ℝ (!₂[1 / 2, (1 + δ) / 2] : Plane) ''
        (P ∪ Q) = P ∪ Q := by
    rw [← direct_halfTurn_form g δ hg]
    exact image_union_of_involution g (direct_involutive g δ hg) hpair
  have hcenter := center_fixed_of_invariant_central_set hcompact hne hcentral
    ReflectionSeparation.horizontal hhorizontal
  have hy := congrArg (fun p : Plane => p 1) hcenter
  rw [ReflectionSeparation.horizontal_apply_one] at hy
  change 1 - (1 + δ) / 2 = (1 + δ) / 2 at hy
  linarith

/-- With zero axial displacement the direct form fixes the square's center. -/
theorem direct_center_fixed_of_zero (g : Plane ≃ᵃⁱ[ℝ] Plane) (δ : ℝ)
    (hg : ∀ p, (g p) 0 = 1 - p 0 ∧ (g p) 1 = 1 - p 1 + δ)
    (hδ : δ = 0) : g squareCenter = squareCenter := by
  apply PlaneIsometries.plane_ext
  · rw [(hg squareCenter).1]
    norm_num
  · rw [(hg squareCenter).2, hδ]
    norm_num

/-- The center-fixing conclusion for an actual direct axial pair. -/
theorem direct_center_fixed (g : Plane ≃ᵃⁱ[ℝ] Plane) (δ : ℝ)
    (hg : ∀ p, (g p) 0 = 1 - p 0 ∧ (g p) 1 = 1 - p 1 + δ)
    {P Q : Set Plane} (hcompact : IsCompact (P ∪ Q)) (hne : (P ∪ Q).Nonempty)
    (hpair : g '' P = Q)
    (hhorizontal : ReflectionSeparation.horizontal '' (P ∪ Q) = P ∪ Q) :
    g squareCenter = squareCenter :=
  direct_center_fixed_of_zero g δ hg
    (direct_parameter_eq_zero g δ hg hcompact hne hpair hhorizontal)

theorem direct_parameter_eq_zero_and_center_fixed (g : Plane ≃ᵃⁱ[ℝ] Plane) (δ : ℝ)
    (hg : ∀ p, (g p) 0 = 1 - p 0 ∧ (g p) 1 = 1 - p 1 + δ)
    {P Q : Set Plane} (hcompact : IsCompact (P ∪ Q)) (hne : (P ∪ Q).Nonempty)
    (hpair : g '' P = Q)
    (hhorizontal : ReflectionSeparation.horizontal '' (P ∪ Q) = P ∪ Q) :
    δ = 0 ∧ g squareCenter = squareCenter := by
  have hδ := direct_parameter_eq_zero g δ hg hcompact hne hpair hhorizontal
  exact ⟨hδ, direct_center_fixed_of_zero g δ hg hδ⟩

end Puzzling139335.N4OuterPair.EqualNormals.AxialForms
