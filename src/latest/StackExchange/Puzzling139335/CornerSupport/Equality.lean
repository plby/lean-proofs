import StackExchange.Puzzling139335.CornerSupport.Equality.Ordered
import StackExchange.Puzzling139335.RectangularHull.Defs

/-!
# The four-corner equality case

Four distinct supporting right corners force a nondegenerate rectangular
convex hull.  The vertices lie in the original set.  No polygonality,
rectifiability, convexity, or nonempty-interior assumption is required.
-/

open Set

namespace Puzzling139335.CornerSupport.Equality

/-- Four distinct supporting right corners can be cyclically ordered as
the vertices of the set's nondegenerate rectangular convex hull. -/
theorem exists_rectangle_of_four_support_corners {P : Set Plane} {a b c d : Plane}
    (ha : SupportCorner P a) (hb : SupportCorner P b)
    (hc : SupportCorner P c) (hd : SupportCorner P d)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ∃ p q r s : Plane, p ∈ P ∧ q ∈ P ∧ r ∈ P ∧ s ∈ P ∧
      (q - p ≠ 0) ∧ (s - p ≠ 0) ∧ inner ℝ (q - p) (s - p) = 0 ∧
      r = p + (q - p) + (s - p) ∧
      convexHull ℝ P = convexHull ℝ ({p, q, r, s} : Set Plane) := by
  have hDirections := four_directions_form_orthogonal_cross
    ha.bisector hb.bisector hc.bisector hd.bisector
    ha.bisector_norm_sq hb.bisector_norm_sq hc.bisector_norm_sq hd.bisector_norm_sq
    (ha.bisectors_inner_nonpos hb hab) (ha.bisectors_inner_nonpos hc hac)
    (ha.bisectors_inner_nonpos hd had) (hb.bisectors_inner_nonpos hc hbc)
    (hb.bisectors_inner_nonpos hd hbd) (hc.bisectors_inner_nonpos hd hcd)
  rcases hDirections with ⟨hbOpp, hdOpp, hOrth⟩ | ⟨hcOpp, hdOpp, hOrth⟩ |
      ⟨hdOpp, hcOpp, hOrth⟩
  · exact ⟨a, c, b, d, ha.mem, hc.mem, hb.mem, hd.mem,
      ordered_support_corners_form_rectangle ha hc hb hd hac had hbOpp hdOpp hOrth⟩
  · exact ⟨a, b, c, d, ha.mem, hb.mem, hc.mem, hd.mem,
      ordered_support_corners_form_rectangle ha hb hc hd hab had hcOpp hdOpp hOrth⟩
  · exact ⟨a, b, d, c, ha.mem, hb.mem, hd.mem, hc.mem,
      ordered_support_corners_form_rectangle ha hb hd hc hab hac hdOpp hcOpp hOrth⟩

/-- The finite-set form used for the distinct intrinsic preimages of square
corners in a dissection. -/
theorem exists_rectangle_of_card_four {P : Set Plane} (t : Finset Plane)
    (hCard : t.card = 4) (hSupport : ∀ v ∈ t, IsSupportCorner P v) :
    ∃ p q r s : Plane, p ∈ P ∧ q ∈ P ∧ r ∈ P ∧ s ∈ P ∧
      (q - p ≠ 0) ∧ (s - p ≠ 0) ∧ inner ℝ (q - p) (s - p) = 0 ∧
      r = p + (q - p) + (s - p) ∧
      convexHull ℝ P = convexHull ℝ ({p, q, r, s} : Set Plane) := by
  classical
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, ht⟩ := Finset.card_eq_four.mp hCard
  obtain ⟨ha⟩ := hSupport a (by simp [ht])
  obtain ⟨hb⟩ := hSupport b (by simp [ht])
  obtain ⟨hc⟩ := hSupport c (by simp [ht])
  obtain ⟨hd⟩ := hSupport d (by simp [ht])
  exact exists_rectangle_of_four_support_corners ha hb hc hd hab hac had hbc hbd hcd

/-- The equality case packaged for the rectangular-hull obstruction. -/
theorem hasRectangularHull_of_card_four {P : Set Plane} (t : Finset Plane)
    (hCard : t.card = 4) (hSupport : ∀ v ∈ t, IsSupportCorner P v) :
    HasRectangularHull P := by
  obtain ⟨p, q, r, s, _, _, _, _, hu, hv, huv, hr, hHull⟩ :=
    exists_rectangle_of_card_four t hCard hSupport
  apply HasRectangularHull.of_vertices (a := p) hu hv huv
  have hq : p + (q - p) = q := by abel
  have hs : p + (s - p) = s := by abel
  rw [← hr, hq, hs]
  exact hHull

end Puzzling139335.CornerSupport.Equality
