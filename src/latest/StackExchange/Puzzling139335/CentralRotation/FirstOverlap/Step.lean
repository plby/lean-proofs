import StackExchange.Puzzling139335.CentralRotation.ArcPacking
import StackExchange.Puzzling139335.CentralRotation.FirstOverlap.Orbit
import StackExchange.Puzzling139335.CentralRotation.FirstOverlap.SubarcOpen

/-! # A nonoverlapping boundary arc advances through the exact gap identity -/

open Set Function Schoenflies

namespace Puzzling139335.CentralRotation.FirstOverlap

/-- Every iterate of an actual isometry is an isometry. -/
theorem isometry_iterate {X : Type*} [PseudoEMetricSpace X]
    {F : X → X} (hF : Isometry F) (n : ℕ) : Isometry F^[n] := by
  induction n with
  | zero => exact isometry_id
  | succ n ih => exact ih.comp hF

/-- Injectivity identifies the relative interior of an image arc with the
image of the arc's relative interior. -/
theorem iterate_image_arc_interior {X : Type*} {F : X → X}
    (hF : Injective F) (n : ℕ) (Γ : Set X) (p q : X) :
    F^[n] '' (Γ \ {p, q}) = (F^[n] '' Γ) \ {F^[n] p, F^[n] q} := by
  rw [Set.image_sdiff (hF.iterate n), Set.image_pair]

/-- If one positive orbit arc has not yet met the target's relative interior,
the entire arc lies in the gap-identity domain, including its endpoints.
The next image is therefore in the ambient arc and avoids the first image's
relative interior. -/
theorem next_subset_gap
    {N Γ J : Set Schoenflies.Plane} {n₀ n₁ p q a b : Schoenflies.Plane}
    (hN : IsArcBetween N n₀ n₁) (hΓ : IsArcBetween Γ p q)
    (hJ : IsArcBetween J a b) (hJN : J ⊆ N)
    {F : Schoenflies.Plane → Schoenflies.Plane} (hF : Isometry F)
    (hgap : F '' (N \ (J \ {a, b})) = N \ F '' (Γ \ {p, q}))
    {n : ℕ} (hinside : F^[n] '' Γ ⊆ N)
    (hdisj : Disjoint (F^[n] '' (Γ \ {p, q})) (J \ {a, b})) :
    F^[n + 1] '' Γ ⊆ N \ F '' (Γ \ {p, q}) := by
  have hK : IsArcBetween (F^[n] '' Γ) (F^[n] p) (F^[n] q) :=
    ArcPacking.isArcBetween_image_isometry hΓ (isometry_iterate hF n)
  have hactual : Disjoint ((F^[n] '' Γ) \ {F^[n] p, F^[n] q})
      (J \ {a, b}) := by
    simpa only [iterate_image_arc_interior hF.injective] using hdisj
  have hwhole := disjoint_of_disjoint_arc_interiors hN hJ hK hJN hinside hactual
  have hdomain : F^[n] '' Γ ⊆ N \ (J \ {a, b}) := by
    intro x hx
    exact ⟨hinside hx, fun hxJ => disjoint_left.mp hwhole hx hxJ⟩
  calc
    F^[n + 1] '' Γ = F '' (F^[n] '' Γ) := by
      rw [Function.iterate_succ', image_comp]
    _ ⊆ F '' (N \ (J \ {a, b})) := image_mono hdomain
    _ = N \ F '' (Γ \ {p, q}) := hgap

end Puzzling139335.CentralRotation.FirstOverlap
