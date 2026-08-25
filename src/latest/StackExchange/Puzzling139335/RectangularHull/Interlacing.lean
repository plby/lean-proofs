import StackExchange.Puzzling139335.RectangularHull.Interlacing.Regions
import StackExchange.Puzzling139335.RectangularHull.Interlacing.SquareBoundary
import StackExchange.Puzzling139335.RectangularHull.Interlacing.SquareSwap
import StackExchange.Puzzling139335.RectangularHull.Interlacing.RectangleChart
import StackExchange.Puzzling139335.SquareExterior

/-!
# Boundary interlacing is impossible for two disjoint square pieces

All cut pairs and interior crosscuts are obtained from the Jordan-region
hypotheses.  The final statements require only coordinate inequalities and
membership of the four contacts.
-/

open Set Schoenflies

namespace Puzzling139335.RectangularHull

/-- Two Jordan pieces in the square with disjoint interiors cannot occupy four
strictly alternating points of the bottom side. -/
theorem bottom_side_interlacing_impossible {P Q : Set Plane} {a b c d : ℝ}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hPS : P ⊆ unitSquare) (hQS : Q ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior Q))
    (ha : 0 ≤ a) (hab : a < b) (hbc : b < c) (hcd : c < d) (hd : d ≤ 1)
    (haP : Schoenflies.Plane.mk a 0 ∈ P) (hcP : Schoenflies.Plane.mk c 0 ∈ P)
    (hbQ : Schoenflies.Plane.mk b 0 ∈ Q) (hdQ : Schoenflies.Plane.mk d 0 ∈ Q) :
    False := by
  obtain ⟨A, B, hcut, hbA, hbB, hdB, hdA⟩ :=
    bottom_alternating_cutPair ha hab hbc hcd hd
  exact alternating_contacts_impossible hP hQ isJordanRegion_unitSquare
    hPS hQS hdis hcut haP hcP hbQ hdQ hbA hbB hdB hdA

/-- Dissection pieces inherit the same-side contact obstruction directly from
the geometric definition of a square dissection. -/
theorem squareDissection_bottom_side_interlacing_impossible
    (D : SquareDissection) {i j : Fin 4} (hij : i ≠ j) {a b c d : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hbc : b < c) (hcd : c < d) (hd : d ≤ 1)
    (haP : Schoenflies.Plane.mk a 0 ∈ D.piece i)
    (hcP : Schoenflies.Plane.mk c 0 ∈ D.piece i)
    (hbQ : Schoenflies.Plane.mk b 0 ∈ D.piece j)
    (hdQ : Schoenflies.Plane.mk d 0 ∈ D.piece j) : False :=
  bottom_side_interlacing_impossible (D.jordan i) (D.jordan j)
    (D.piece_subset i) (D.piece_subset j) (D.disjoint_interiors hij)
    ha hab hbc hcd hd haP hcP hbQ hdQ

/-- Contacts of disjoint pieces cannot occur in reversed horizontal order on
the bottom and top sides of the square. -/
theorem bottom_top_interlacing_impossible {P Q : Set Plane} {a b c d : ℝ}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hPS : P ⊆ unitSquare) (hQS : Q ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior Q))
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hd : 0 ≤ d) (hdc : d < c) (hc : c ≤ 1)
    (haP : Schoenflies.Plane.mk a 0 ∈ P) (hcP : Schoenflies.Plane.mk c 1 ∈ P)
    (hbQ : Schoenflies.Plane.mk b 0 ∈ Q) (hdQ : Schoenflies.Plane.mk d 1 ∈ Q) :
    False := by
  obtain ⟨A, B, hcut, hdA, hdB, hbB, hbA⟩ :=
    opposing_alternating_cutPair ha hab hb hd hdc hc
  exact alternating_contacts_impossible hP hQ isJordanRegion_unitSquare
    hPS hQS hdis hcut haP hcP hdQ hbQ hdA hdB hbB hbA

/-- Contacts of disjoint pieces cannot occur in reversed vertical order on
the left and right sides of the square. -/
theorem left_right_interlacing_impossible {P Q : Set Plane} {a b c d : ℝ}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hPS : P ⊆ unitSquare) (hQS : Q ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior Q))
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hd : 0 ≤ d) (hdc : d < c) (hc : c ≤ 1)
    (haP : Schoenflies.Plane.mk 0 a ∈ P) (hcP : Schoenflies.Plane.mk 1 c ∈ P)
    (hbQ : Schoenflies.Plane.mk 0 b ∈ Q) (hdQ : Schoenflies.Plane.mk 1 d ∈ Q) :
    False := by
  obtain ⟨A, B, hcut, hdA, hdB, hbB, hbA⟩ :=
    left_right_alternating_cutPair ha hab hb hd hdc hc
  exact alternating_contacts_impossible hP hQ isJordanRegion_unitSquare
    hPS hQS hdis hcut haP hcP hdQ hbQ hdA hdB hbB hbA

/-- A nondegenerate axis rectangle is a closed Jordan region. -/
theorem isJordanRegion_axisRectangle {l r b t : ℝ} (hlr : l < r) (hbt : b < t) :
    IsJordanRegion (axisRectangle l r b t) := by
  let e := rectangleChart l r b t hlr hbt
  have h := isJordanRegion_unitSquare.image_homeomorph e.symm
  have he : e '' axisRectangle l r b t = unitSquare :=
    rectangleChart_image_rectangle hlr hbt
  rw [← he, image_image] at h
  simpa only [e.symm_apply_apply, image_id'] using h

/-- Within a rectangle, two disjoint Jordan interiors cannot join the two
opposite diagonal pairs of corners.  In particular, two such pieces cannot
both contain all four corners of their common rectangular hull. -/
theorem rectangle_diagonal_contacts_impossible {P Q : Set Plane} {l r b t : ℝ}
    (hlr : l < r) (hbt : b < t)
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hPR : P ⊆ axisRectangle l r b t) (hQR : Q ⊆ axisRectangle l r b t)
    (hdis : Disjoint (interior P) (interior Q))
    (hblP : Schoenflies.Plane.mk l b ∈ P) (htrP : Schoenflies.Plane.mk r t ∈ P)
    (htlQ : Schoenflies.Plane.mk l t ∈ Q) (hbrQ : Schoenflies.Plane.mk r b ∈ Q) :
    False := by
  let e := rectangleChart l r b t hlr hbt
  have he : e '' axisRectangle l r b t = unitSquare :=
    rectangleChart_image_rectangle hlr hbt
  have hPS : e '' P ⊆ unitSquare := he ▸ image_mono hPR
  have hQS : e '' Q ⊆ unitSquare := he ▸ image_mono hQR
  have hbl : Schoenflies.Plane.mk 0 0 ∈ e '' P := by
    simpa only [e, rectangleChart_bottomLeft] using mem_image_of_mem e hblP
  have htr : Schoenflies.Plane.mk 1 1 ∈ e '' P := by
    simpa only [e, rectangleChart_topRight] using mem_image_of_mem e htrP
  have htl : Schoenflies.Plane.mk 0 1 ∈ e '' Q := by
    simpa only [e, rectangleChart_topLeft] using mem_image_of_mem e htlQ
  have hbr : Schoenflies.Plane.mk 1 0 ∈ e '' Q := by
    simpa only [e, rectangleChart_bottomRight] using mem_image_of_mem e hbrQ
  exact left_right_interlacing_impossible (hP.image_homeomorph e) (hQ.image_homeomorph e)
    hPS hQS (disjoint_interiors_image_homeomorph hdis e)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hbl htr htl hbr

end Puzzling139335.RectangularHull
