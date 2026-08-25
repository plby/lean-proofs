import StackExchange.Puzzling139335.JordanCrosscut
import StackExchange.Puzzling139335.JordanInvolution

/-!
# The actual closed sides of a centrally symmetric Jordan crosscut

The two sides are defined by filling the Jordan curves made from the crosscut
and the two outer arcs.  Their interiors are disjoint, their union fills the
outer curve, and their common contacts with the outer frontier are exactly
the two endpoints.  In particular the finite-contact hypothesis used by
translation cancellation is a consequence of the crosscut data.

Central symmetry of the outer curve puts the center inside the filled domain.
If it belongs to neither side's interior, it therefore lies on the crosscut.
-/

open Set Schoenflies

namespace Puzzling139335.JordanCrosscut

variable {C Γ M N : Set Plane} {p q c x : Plane}

/-- The interiors of the two actual closed sides are disjoint. -/
theorem closure_sides_disjoint_interiors
    (h : JordanCrosscut C Γ p q) (hc : IsCutPair C p q M N) :
    Disjoint (interior (closure (inside (M ∪ Γ))))
      (interior (closure (inside (N ∪ Γ)))) := by
  rw [interior_closure_inside (jordan_curve_theorem (h.isJordanCurve_union hc)),
    interior_closure_inside (jordan_curve_theorem (h.isJordanCurve_union hc.symm))]
  exact h.disjoint_sides hc

/-- The frontier of the union of the two closed sides is the original curve. -/
theorem closure_sides_frontier_union
    (h : JordanCrosscut C Γ p q) (hc : IsCutPair C p q M N) :
    frontier (closure (inside (M ∪ Γ)) ∪ closure (inside (N ∪ Γ))) = C := by
  rw [← h.closure_inside_eq_union hc]
  exact frontier_closure_inside (jordan_curve_theorem h.curve)

/-- The only common contacts of the two closed sides on their outer frontier
are the endpoints of the crosscut. -/
theorem closure_sides_outer_contact_eq
    (h : JordanCrosscut C Γ p q) (hc : IsCutPair C p q M N) :
    closure (inside (M ∪ Γ)) ∩ closure (inside (N ∪ Γ)) ∩
      frontier (closure (inside (M ∪ Γ)) ∪ closure (inside (N ∪ Γ))) = {p, q} := by
  rw [h.closure_sides_inter hc, h.closure_sides_frontier_union hc]
  exact h.inter_eq

/-- The common outer contacts of a proper crosscut form a finite set. -/
theorem closure_sides_outer_contact_finite
    (h : JordanCrosscut C Γ p q) (hc : IsCutPair C p q M N) :
    (closure (inside (M ∪ Γ)) ∩ closure (inside (N ∪ Γ)) ∩
      frontier (closure (inside (M ∪ Γ)) ∪ closure (inside (N ∪ Γ)))).Finite := by
  rw [h.closure_sides_outer_contact_eq hc]
  exact Set.Finite.insert p (finite_singleton q)

/-- Central symmetry of the outer curve preserves the union of the actual
closed sides; symmetry of this union is not an extra hypothesis. -/
theorem closure_sides_pointReflection_image_union
    (h : JordanCrosscut C Γ p q) (hc : IsCutPair C p q M N)
    (hsym : AffineIsometryEquiv.pointReflection ℝ c '' C = C) :
    AffineIsometryEquiv.pointReflection ℝ c ''
      (closure (inside (M ∪ Γ)) ∪ closure (inside (N ∪ Γ))) =
      closure (inside (M ∪ Γ)) ∪ closure (inside (N ∪ Γ)) := by
  let e := (AffineIsometryEquiv.pointReflection ℝ c).toHomeomorph
  change e '' (closure (inside (M ∪ Γ)) ∪ closure (inside (N ∪ Γ))) =
    closure (inside (M ∪ Γ)) ∪ closure (inside (N ∪ Γ))
  rw [← h.closure_inside_eq_union hc, e.image_closure, homeomorph_image_inside,
    show e '' C = C from hsym]

/-- The center of a centrally symmetric outer Jordan curve lies in its
filled domain's interior. -/
theorem center_mem_interior_closure_inside_of_pointReflection
    (h : JordanCrosscut C Γ p q)
    (hsym : AffineIsometryEquiv.pointReflection ℝ c '' C = C) :
    c ∈ interior (closure (inside C)) := by
  have hregion : IsJordanRegion (closure (inside C)) := ⟨C, h.curve, rfl⟩
  apply hregion.center_mem_interior_of_pointReflection
  let e := (AffineIsometryEquiv.pointReflection ℝ c).toHomeomorph
  change e '' closure (inside C) = closure (inside C)
  rw [e.image_closure, homeomorph_image_inside, show e '' C = C from hsym]

/-- The center lies in the bounded complementary region of the outer curve. -/
theorem center_mem_inside_of_pointReflection
    (h : JordanCrosscut C Γ p q)
    (hsym : AffineIsometryEquiv.pointReflection ℝ c '' C = C) :
    c ∈ inside C := by
  have hc := h.center_mem_interior_closure_inside_of_pointReflection hsym
  rwa [interior_closure_inside (jordan_curve_theorem h.curve)] at hc

/-- Central symmetry puts the center in the interior of the union of the
two actual sides. -/
theorem center_mem_interior_union
    (h : JordanCrosscut C Γ p q) (hc : IsCutPair C p q M N)
    (hsym : AffineIsometryEquiv.pointReflection ℝ c '' C = C) :
    c ∈ interior (closure (inside (M ∪ Γ)) ∪ closure (inside (N ∪ Γ))) := by
  rw [← h.closure_inside_eq_union hc]
  exact h.center_mem_interior_closure_inside_of_pointReflection hsym

/-- A point inside the original curve which belongs to neither side's
interior must lie on the crosscut. -/
theorem mem_cut_of_mem_inside_of_not_mem_sides
    (h : JordanCrosscut C Γ p q) (hc : IsCutPair C p q M N)
    (hx : x ∈ inside C)
    (hnotM : x ∉ interior (closure (inside (M ∪ Γ))))
    (hnotN : x ∉ interior (closure (inside (N ∪ Γ)))) : x ∈ Γ := by
  rw [interior_closure_inside (jordan_curve_theorem (h.isJordanCurve_union hc))] at hnotM
  rw [interior_closure_inside (jordan_curve_theorem (h.isJordanCurve_union hc.symm))] at hnotN
  by_contra hxΓ
  have hside : x ∈ inside (M ∪ Γ) ∪ inside (N ∪ Γ) := h.inside_diff_eq hc ▸ ⟨hx, hxΓ⟩
  exact hside.elim hnotM hnotN

/-- If the center is in neither actual side's interior, it lies on the cut.
Both its location in the outer domain and the side alternatives are derived
from the supplied central Jordan crosscut. -/
theorem center_mem_cut_of_not_mem_sides
    (h : JordanCrosscut C Γ p q) (hc : IsCutPair C p q M N)
    (hsym : AffineIsometryEquiv.pointReflection ℝ c '' C = C)
    (hnotM : c ∉ interior (closure (inside (M ∪ Γ))))
    (hnotN : c ∉ interior (closure (inside (N ∪ Γ)))) : c ∈ Γ :=
  h.mem_cut_of_mem_inside_of_not_mem_sides hc
    (h.center_mem_inside_of_pointReflection hsym) hnotM hnotN

end Puzzling139335.JordanCrosscut
