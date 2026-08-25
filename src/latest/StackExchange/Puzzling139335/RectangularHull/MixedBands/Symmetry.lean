import StackExchange.Puzzling139335.RectangularHull.MixedBands.BoundaryArc
import StackExchange.Puzzling139335.SquareSymmetry.Basic

/-! # Reflected versions of the perpendicular-band contact obstruction -/

open Set

namespace Puzzling139335.RectangularHull

private lemma flip_one_mk (x y : ℝ) :
    SquareSymmetry.cornerFlip 1 (Schoenflies.Plane.mk x y) =
      Schoenflies.Plane.mk (1 - x) y := by
  ext i
  fin_cases i <;>
    norm_num [SquareSymmetry.cornerFlipPoint, corner, Fin.ext_iff]

private lemma flip_two_mk (x y : ℝ) :
    SquareSymmetry.cornerFlip 2 (Schoenflies.Plane.mk x y) =
      Schoenflies.Plane.mk (1 - x) (1 - y) := by
  ext i
  fin_cases i <;>
    norm_num [SquareSymmetry.cornerFlipPoint, corner, Fin.ext_iff]

private lemma flip_three_mk (x y : ℝ) :
    SquareSymmetry.cornerFlip 3 (Schoenflies.Plane.mk x y) =
      Schoenflies.Plane.mk x (1 - y) := by
  ext i
  fin_cases i <;>
    norm_num [SquareSymmetry.cornerFlipPoint, corner, Fin.ext_iff]

private theorem flipped_bottom_left_contacts_impossible (i : Fin 4)
    {P Q : Set Plane} {h w : ℝ}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hPS : P ⊆ unitSquare) (hQS : Q ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior Q))
    (hh0 : 0 < h) (hh1 : h ≤ 1) (hw0 : 0 < w) (hw1 : w ≤ 1)
    (hBL : Schoenflies.Plane.mk 0 0 ∈ SquareSymmetry.cornerFlip i '' P)
    (hRh : Schoenflies.Plane.mk 1 h ∈ SquareSymmetry.cornerFlip i '' P)
    (hwB : Schoenflies.Plane.mk w 0 ∈ SquareSymmetry.cornerFlip i '' Q)
    (hTL : Schoenflies.Plane.mk 0 1 ∈ SquareSymmetry.cornerFlip i '' Q) : False := by
  have hPS' : SquareSymmetry.cornerFlip i '' P ⊆ unitSquare := by
    rw [← SquareSymmetry.cornerFlip_image_unitSquare i]
    exact image_mono hPS
  have hQS' : SquareSymmetry.cornerFlip i '' Q ⊆ unitSquare := by
    rw [← SquareSymmetry.cornerFlip_image_unitSquare i]
    exact image_mono hQS
  exact bottom_left_contacts_impossible
    (hP.image_homeomorph (SquareSymmetry.cornerFlip i).toHomeomorph)
    (hQ.image_homeomorph (SquareSymmetry.cornerFlip i).toHomeomorph)
    hPS' hQS' (disjoint_interiors_image_homeomorph hdis
      (SquareSymmetry.cornerFlip i).toHomeomorph)
    hh0 hh1 hw0 hw1 hBL hRh hwB hTL

theorem bottom_right_contacts_impossible {P Q : Set Plane} {h w : ℝ}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hPS : P ⊆ unitSquare) (hQS : Q ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior Q))
    (hh0 : 0 < h) (hh1 : h ≤ 1) (hw0 : 0 < w) (hw1 : w ≤ 1)
    (hBR : Schoenflies.Plane.mk 1 0 ∈ P)
    (hLh : Schoenflies.Plane.mk 0 h ∈ P)
    (hwB : Schoenflies.Plane.mk (1 - w) 0 ∈ Q)
    (hTR : Schoenflies.Plane.mk 1 1 ∈ Q) : False := by
  apply flipped_bottom_left_contacts_impossible 1 hP hQ hPS hQS hdis hh0 hh1 hw0 hw1
  · simpa only [flip_one_mk, sub_self] using mem_image_of_mem (SquareSymmetry.cornerFlip 1) hBR
  · simpa only [flip_one_mk, sub_zero] using mem_image_of_mem (SquareSymmetry.cornerFlip 1) hLh
  · simpa only [flip_one_mk, show (1 : ℝ) - (1 - w) = w by ring] using
      mem_image_of_mem (SquareSymmetry.cornerFlip 1) hwB
  · simpa only [flip_one_mk, sub_self] using mem_image_of_mem (SquareSymmetry.cornerFlip 1) hTR

theorem top_left_contacts_impossible {P Q : Set Plane} {h w : ℝ}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hPS : P ⊆ unitSquare) (hQS : Q ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior Q))
    (hh0 : 0 < h) (hh1 : h ≤ 1) (hw0 : 0 < w) (hw1 : w ≤ 1)
    (hTL : Schoenflies.Plane.mk 0 1 ∈ P)
    (hRh : Schoenflies.Plane.mk 1 (1 - h) ∈ P)
    (hwT : Schoenflies.Plane.mk w 1 ∈ Q)
    (hBL : Schoenflies.Plane.mk 0 0 ∈ Q) : False := by
  apply flipped_bottom_left_contacts_impossible 3 hP hQ hPS hQS hdis hh0 hh1 hw0 hw1
  · simpa only [flip_three_mk, sub_self] using mem_image_of_mem (SquareSymmetry.cornerFlip 3) hTL
  · simpa only [flip_three_mk, show (1 : ℝ) - (1 - h) = h by ring] using
      mem_image_of_mem (SquareSymmetry.cornerFlip 3) hRh
  · simpa only [flip_three_mk, sub_self] using mem_image_of_mem (SquareSymmetry.cornerFlip 3) hwT
  · simpa only [flip_three_mk, sub_zero] using mem_image_of_mem (SquareSymmetry.cornerFlip 3) hBL

theorem top_right_contacts_impossible {P Q : Set Plane} {h w : ℝ}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hPS : P ⊆ unitSquare) (hQS : Q ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior Q))
    (hh0 : 0 < h) (hh1 : h ≤ 1) (hw0 : 0 < w) (hw1 : w ≤ 1)
    (hTR : Schoenflies.Plane.mk 1 1 ∈ P)
    (hLh : Schoenflies.Plane.mk 0 (1 - h) ∈ P)
    (hwT : Schoenflies.Plane.mk (1 - w) 1 ∈ Q)
    (hBR : Schoenflies.Plane.mk 1 0 ∈ Q) : False := by
  apply flipped_bottom_left_contacts_impossible 2 hP hQ hPS hQS hdis hh0 hh1 hw0 hw1
  · simpa only [flip_two_mk, sub_self] using mem_image_of_mem (SquareSymmetry.cornerFlip 2) hTR
  · simpa only [flip_two_mk, sub_zero, show (1 : ℝ) - (1 - h) = h by ring] using
      mem_image_of_mem (SquareSymmetry.cornerFlip 2) hLh
  · simpa only [flip_two_mk, sub_self, show (1 : ℝ) - (1 - w) = w by ring] using
      mem_image_of_mem (SquareSymmetry.cornerFlip 2) hwT
  · simpa only [flip_two_mk, sub_self, sub_zero] using
      mem_image_of_mem (SquareSymmetry.cornerFlip 2) hBR

end Puzzling139335.RectangularHull
