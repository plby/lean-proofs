import StackExchange.Puzzling139335.CentralRotation.FirstOverlap.Termination
import StackExchange.Puzzling139335.CentralRotation.FirstOverlap.CurveOpen

/-!
# First overlap of the actual boundary-arc orbit

This interface writes every relative interior as the actual image arc with
its two image endpoints removed. `exists_first_overlap_of_image_gap` in the
imported module is the equivalent image-of-the-open-source-arc formulation.
-/

open Set Function Schoenflies

namespace Puzzling139335.CentralRotation.FirstOverlap

/-- The exact set-domain identity forces a first relative-interior overlap
of a positive image of the source arc with the target arc. Every earlier
positive image remains inside the ambient Jordan arc and has disjoint relative
interior from the target. -/
theorem exists_first_overlap
    {N Γ J : Set Schoenflies.Plane} {n₀ n₁ p q a b : Schoenflies.Plane}
    (hN : IsArcBetween N n₀ n₁) (hΓ : IsArcBetween Γ p q)
    (hJ : IsArcBetween J a b) (hJN : J ⊆ N)
    {F : Schoenflies.Plane → Schoenflies.Plane} (hF : Isometry F)
    (hfirst : F '' Γ ⊆ N)
    (hgap : F '' (N \ (J \ {a, b})) = N \ ((F '' Γ) \ {F p, F q})) :
    ∃ m : ℕ, 1 ≤ m ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ m → F^[k] '' Γ ⊆ N) ∧
      (((F^[m] '' Γ) \ {F^[m] p, F^[m] q}) ∩ (J \ {a, b})).Nonempty ∧
      (∀ k : ℕ, 1 ≤ k → k < m →
        Disjoint ((F^[k] '' Γ) \ {F^[k] p, F^[k] q}) (J \ {a, b})) := by
  have hgap' : F '' (N \ (J \ {a, b})) = N \ F '' (Γ \ {p, q}) := by
    simpa only [Set.image_sdiff hF.injective, Set.image_pair] using hgap
  simpa only [iterate_image_arc_interior hF.injective] using
    exists_first_overlap_of_image_gap hN hΓ hJ hJN hF hfirst hgap'

end Puzzling139335.CentralRotation.FirstOverlap
