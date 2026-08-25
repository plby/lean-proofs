import StackExchange.Puzzling139335.RectangularHull.AxisBox
import StackExchange.Puzzling139335.RectangularHull.AnchoredBands
import StackExchange.Puzzling139335.RectangularHull.MixedBands.Symmetry

/-!
# Perpendicular full-side bands cannot be hulls of disjoint Jordan pieces

The required contacts are extracted from the exact convex hulls by extremality.
No boundary-contact or separation assumption is added to the Jordan hypotheses.
-/

open Set

namespace Puzzling139335.RectangularHull

lemma axisBox_endpoint_mem_of_convexHull_eq {P : Set Plane} {l r b t : ℝ} {p : Plane}
    (hHull : convexHull ℝ P = closedAxisBox l r b t) (hlr : l ≤ r) (hbt : b ≤ t)
    (hp0 : p 0 = l ∨ p 0 = r) (hp1 : p 1 = b ∨ p 1 = t) : p ∈ P := by
  apply extremePoints_convexHull_subset (𝕜 := ℝ)
  rw [hHull]
  exact mem_extremePoints_closedAxisBox_of_endpoints hlr hbt hp0 hp1

private lemma subset_square_of_box_hull {P : Set Plane} {l r b t : ℝ}
    (hHull : convexHull ℝ P = closedAxisBox l r b t)
    (hl : 0 ≤ l) (hr : r ≤ 1) (hb : 0 ≤ b) (ht : t ≤ 1) : P ⊆ unitSquare := by
  intro p hp
  have hpH : p ∈ closedAxisBox l r b t := hHull ▸ subset_convexHull ℝ P hp
  exact ⟨⟨hl.trans hpH.1.1, hpH.1.2.trans hr⟩,
    ⟨hb.trans hpH.2.1, hpH.2.2.trans ht⟩⟩

/-- A bottom full-width band and a left full-height band cannot be the
actual convex hulls of two Jordan pieces with disjoint interiors. -/
theorem bottom_left_hulls_impossible {P Q : Set Plane} {h : ℝ}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hdis : Disjoint (interior P) (interior Q)) (hh0 : 0 < h) (hh1 : h < 1)
    (hPHull : convexHull ℝ P = closedAxisBox 0 1 0 h)
    (hQHull : convexHull ℝ Q = closedAxisBox 0 h 0 1) : False := by
  have hPS := subset_square_of_box_hull hPHull (by norm_num) (by norm_num)
    (by norm_num) hh1.le
  have hQS := subset_square_of_box_hull hQHull (by norm_num) hh1.le
    (by norm_num) (by norm_num)
  have hBL : Schoenflies.Plane.mk 0 0 ∈ P :=
    axisBox_endpoint_mem_of_convexHull_eq hPHull (by norm_num) hh0.le
      (Or.inl rfl) (Or.inl rfl)
  have hRh : Schoenflies.Plane.mk 1 h ∈ P :=
    axisBox_endpoint_mem_of_convexHull_eq hPHull (by norm_num) hh0.le
      (Or.inr rfl) (Or.inr rfl)
  have hwB : Schoenflies.Plane.mk h 0 ∈ Q :=
    axisBox_endpoint_mem_of_convexHull_eq hQHull hh0.le (by norm_num)
      (Or.inr rfl) (Or.inl rfl)
  have hTL : Schoenflies.Plane.mk 0 1 ∈ Q :=
    axisBox_endpoint_mem_of_convexHull_eq hQHull hh0.le (by norm_num)
      (Or.inl rfl) (Or.inr rfl)
  exact bottom_left_contacts_impossible hP hQ hPS hQS hdis hh0 hh1.le hh0 hh1.le
    hBL hRh hwB hTL

theorem bottom_right_hulls_impossible {P Q : Set Plane} {h : ℝ}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hdis : Disjoint (interior P) (interior Q)) (hh0 : 0 < h) (hh1 : h < 1)
    (hPHull : convexHull ℝ P = closedAxisBox 0 1 0 h)
    (hQHull : convexHull ℝ Q = closedAxisBox (1 - h) 1 0 1) : False := by
  have hPS := subset_square_of_box_hull hPHull (by norm_num) (by norm_num)
    (by norm_num) hh1.le
  have hQS := subset_square_of_box_hull hQHull (by linarith) (by norm_num)
    (by norm_num) (by norm_num)
  apply bottom_right_contacts_impossible hP hQ hPS hQS hdis hh0 hh1.le hh0 hh1.le
  · exact axisBox_endpoint_mem_of_convexHull_eq hPHull (by norm_num) hh0.le
      (Or.inr rfl) (Or.inl rfl)
  · exact axisBox_endpoint_mem_of_convexHull_eq hPHull (by norm_num) hh0.le
      (Or.inl rfl) (Or.inr rfl)
  · exact axisBox_endpoint_mem_of_convexHull_eq hQHull (by linarith) (by norm_num)
      (Or.inl rfl) (Or.inl rfl)
  · exact axisBox_endpoint_mem_of_convexHull_eq hQHull (by linarith) (by norm_num)
      (Or.inr rfl) (Or.inr rfl)

theorem top_left_hulls_impossible {P Q : Set Plane} {h : ℝ}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hdis : Disjoint (interior P) (interior Q)) (hh0 : 0 < h) (hh1 : h < 1)
    (hPHull : convexHull ℝ P = closedAxisBox 0 1 (1 - h) 1)
    (hQHull : convexHull ℝ Q = closedAxisBox 0 h 0 1) : False := by
  have hPS := subset_square_of_box_hull hPHull (by norm_num) (by norm_num)
    (by linarith) (by norm_num)
  have hQS := subset_square_of_box_hull hQHull (by norm_num) hh1.le
    (by norm_num) (by norm_num)
  apply top_left_contacts_impossible hP hQ hPS hQS hdis hh0 hh1.le hh0 hh1.le
  · exact axisBox_endpoint_mem_of_convexHull_eq hPHull (by norm_num) (by linarith)
      (Or.inl rfl) (Or.inr rfl)
  · exact axisBox_endpoint_mem_of_convexHull_eq hPHull (by norm_num) (by linarith)
      (Or.inr rfl) (Or.inl rfl)
  · exact axisBox_endpoint_mem_of_convexHull_eq hQHull hh0.le (by norm_num)
      (Or.inr rfl) (Or.inr rfl)
  · exact axisBox_endpoint_mem_of_convexHull_eq hQHull hh0.le (by norm_num)
      (Or.inl rfl) (Or.inl rfl)

theorem top_right_hulls_impossible {P Q : Set Plane} {h : ℝ}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hdis : Disjoint (interior P) (interior Q)) (hh0 : 0 < h) (hh1 : h < 1)
    (hPHull : convexHull ℝ P = closedAxisBox 0 1 (1 - h) 1)
    (hQHull : convexHull ℝ Q = closedAxisBox (1 - h) 1 0 1) : False := by
  have hPS := subset_square_of_box_hull hPHull (by norm_num) (by norm_num)
    (by linarith) (by norm_num)
  have hQS := subset_square_of_box_hull hQHull (by linarith) (by norm_num)
    (by norm_num) (by norm_num)
  apply top_right_contacts_impossible hP hQ hPS hQS hdis hh0 hh1.le hh0 hh1.le
  · exact axisBox_endpoint_mem_of_convexHull_eq hPHull (by norm_num) (by linarith)
      (Or.inr rfl) (Or.inr rfl)
  · exact axisBox_endpoint_mem_of_convexHull_eq hPHull (by norm_num) (by linarith)
      (Or.inl rfl) (Or.inl rfl)
  · exact axisBox_endpoint_mem_of_convexHull_eq hQHull (by linarith) (by norm_num)
      (Or.inl rfl) (Or.inr rfl)
  · exact axisBox_endpoint_mem_of_convexHull_eq hQHull (by linarith) (by norm_num)
      (Or.inr rfl) (Or.inl rfl)

/-- The two actual band hulls cannot be anchored on perpendicular sides. -/
theorem sideBand_hulls_impossible_of_ne_and_ne_opposite {P Q : Set Plane} {h : ℝ}
    {s t : Fin 4} (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hdis : Disjoint (interior P) (interior Q)) (hh0 : 0 < h) (hh1 : h < 1)
    (hPHull : convexHull ℝ P = sideBand h s) (hQHull : convexHull ℝ Q = sideBand h t)
    (hne : t ≠ s) (hopp : t ≠ s + 2) : False := by
  fin_cases s <;> fin_cases t <;>
    first
    | exact hne rfl
    | exact hopp rfl
    | exact bottom_left_hulls_impossible hP hQ hdis hh0 hh1 hPHull hQHull
    | exact bottom_right_hulls_impossible hP hQ hdis hh0 hh1 hPHull hQHull
    | exact top_left_hulls_impossible hP hQ hdis hh0 hh1 hPHull hQHull
    | exact top_right_hulls_impossible hP hQ hdis hh0 hh1 hPHull hQHull
    | exact bottom_left_hulls_impossible hQ hP hdis.symm hh0 hh1 hQHull hPHull
    | exact bottom_right_hulls_impossible hQ hP hdis.symm hh0 hh1 hQHull hPHull
    | exact top_left_hulls_impossible hQ hP hdis.symm hh0 hh1 hQHull hPHull
    | exact top_right_hulls_impossible hQ hP hdis.symm hh0 hh1 hQHull hPHull

/-- Side-band hulls of two pieces with disjoint Jordan interiors lie on the
same square side or on opposite square sides. -/
theorem sideBand_hulls_same_or_opposite {P Q : Set Plane} {h : ℝ} {s t : Fin 4}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hdis : Disjoint (interior P) (interior Q)) (hh0 : 0 < h) (hh1 : h < 1)
    (hPHull : convexHull ℝ P = sideBand h s) (hQHull : convexHull ℝ Q = sideBand h t) :
    t = s ∨ t = s + 2 := by
  by_cases hne : t = s
  · exact Or.inl hne
  by_cases hopp : t = s + 2
  · exact Or.inr hopp
  exact False.elim (sideBand_hulls_impossible_of_ne_and_ne_opposite
    hP hQ hdis hh0 hh1 hPHull hQHull hne hopp)

end Puzzling139335.RectangularHull
