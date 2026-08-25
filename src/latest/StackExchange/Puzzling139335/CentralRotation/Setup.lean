import StackExchange.Puzzling139335.AntipodalEndpoints
import StackExchange.Puzzling139335.CentralRotation.GapIdentity

/-! # Geometric boundary data for a central two-piece Jordan cut -/

open Set Schoenflies

namespace Puzzling139335.JordanCrosscut

variable {C Γ M N : Set Plane} {p q c : Plane}

/-- Mapping the actual closed sides of a crosscut maps their whole boundaries. -/
theorem image_boundary_of_image_sides
    (h : JordanCrosscut C Γ p q) (houter : IsCutPair C p q M N)
    (g : Plane ≃ᵃⁱ[ℝ] Plane)
    (hg : g '' closure (inside (M ∪ Γ)) = closure (inside (N ∪ Γ))) :
    g '' (M ∪ Γ) = N ∪ Γ := by
  have hM := jordan_curve_theorem (h.isJordanCurve_union houter)
  have hN := jordan_curve_theorem (h.isJordanCurve_union houter.symm)
  calc
    g '' (M ∪ Γ) = g '' frontier (closure (inside (M ∪ Γ))) := by
      rw [frontier_closure_inside hM]
    _ = frontier (g '' closure (inside (M ∪ Γ))) := g.toHomeomorph.image_frontier _
    _ = N ∪ Γ := by rw [hg, frontier_closure_inside hN]

/-- Congruence of the actual sides forces the central half-turn to interchange
their two outer boundary arcs.  The antipodal endpoint condition is proved. -/
theorem halfTurn_image_outer_of_congruent_sides
    (h : JordanCrosscut C Γ p q) (houter : IsCutPair C p q M N)
    (hcongr : Congruent (closure (inside (M ∪ Γ))) (closure (inside (N ∪ Γ))))
    (hsym : AffineIsometryEquiv.pointReflection ℝ c '' C = C) :
    AffineIsometryEquiv.pointReflection ℝ c '' M = N := by
  let e := (AffineIsometryEquiv.pointReflection ℝ c).toHomeomorph
  have he : e '' C = C := hsym
  have hinv : Function.Involutive e :=
    AffineIsometryEquiv.pointReflection_involutive (𝕜 := ℝ) c
  have hfix (x : Plane) : e x = x ↔ x = c :=
    AffineIsometryEquiv.pointReflection_fixed_iff
  have hcnot : c ∉ C := h.curve.not_mem_of_involution_unique_fixed e he hinv
    (AffineIsometryEquiv.pointReflection_self (𝕜 := ℝ) c) (fun x hx => (hfix x).mp hx)
  have hfree : ∀ x ∈ C, e x ≠ x := by
    intro x hx hxe
    exact hcnot ((hfix x).mp hxe ▸ hx)
  have hq : q = e p := h.endpoints_antipodal_of_congruent_sides houter hcongr hsym
  have hcut : IsCutPair C p (e p) M N := hq ▸ houter
  exact hcut.image_fst_eq_snd_of_free_involution e he hinv hfree

/-- The exact orbit gap identity follows directly from a congruence of the
two closed Jordan sides and central symmetry of their outer boundary. -/
theorem rotation_gap_identity
    (h : JordanCrosscut C Γ p q) (houter : IsCutPair C p q M N)
    (g F : Plane ≃ᵃⁱ[ℝ] Plane)
    (hg : g '' closure (inside (M ∪ Γ)) = closure (inside (N ∪ Γ)))
    (hsym : AffineIsometryEquiv.pointReflection ℝ c '' C = C)
    (hF : ∀ x, F x = AffineIsometryEquiv.pointReflection ℝ c (g.symm x)) :
    F '' (N \ g '' (Γ \ {p, q})) = N \ F '' (Γ \ {p, q}) := by
  have hboundary := h.image_boundary_of_image_sides houter g hg
  have houterImage := h.halfTurn_image_outer_of_congruent_sides houter ⟨g, hg⟩ hsym
  exact CentralRotation.GapIdentity.image_gap_of_boundary_intersections
    g.toHomeomorph (AffineIsometryEquiv.pointReflection ℝ c).toHomeomorph F.toHomeomorph
    (h.inter_arc_eq houter) (h.inter_arc_eq houter.symm) hboundary houterImage hF

end Puzzling139335.JordanCrosscut
