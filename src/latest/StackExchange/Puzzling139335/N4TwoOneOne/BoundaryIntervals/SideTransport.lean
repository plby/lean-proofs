import StackExchange.Puzzling139335.RectangularHull.Interlacing
import StackExchange.Puzzling139335.SquareSymmetry.Basic

/-!
# Noninterlacing on each side of the square

The bottom-side obstruction is transported by actual plane homeomorphisms
that preserve the square.  No interval structure of a piece's contacts is
assumed.  The common side parametrization increases the varying coordinate
on each side; it is not a single oriented parametrization of the boundary.
-/

open Set

namespace Puzzling139335.N4TwoOneOne.BoundaryIntervals

private theorem transported_bottom_side_interlacing_impossible
    (e : Plane ≃ₜ Plane) (he : e '' unitSquare = unitSquare)
    {P Q : Set Plane} {a b c d : ℝ}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hPS : P ⊆ unitSquare) (hQS : Q ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior Q))
    (ha : 0 ≤ a) (hab : a < b) (hbc : b < c) (hcd : c < d) (hd : d ≤ 1)
    (haP : Schoenflies.Plane.mk a 0 ∈ e '' P)
    (hcP : Schoenflies.Plane.mk c 0 ∈ e '' P)
    (hbQ : Schoenflies.Plane.mk b 0 ∈ e '' Q)
    (hdQ : Schoenflies.Plane.mk d 0 ∈ e '' Q) : False := by
  have hPS' : e '' P ⊆ unitSquare := he ▸ image_mono hPS
  have hQS' : e '' Q ⊆ unitSquare := he ▸ image_mono hQS
  exact RectangularHull.bottom_side_interlacing_impossible
    (hP.image_homeomorph e) (hQ.image_homeomorph e) hPS' hQS'
    (RectangularHull.disjoint_interiors_image_homeomorph hdis e)
    ha hab hbc hcd hd haP hcP hbQ hdQ

/-- Two Jordan regions with disjoint interiors cannot alternate along the left
side, in increasing vertical order. -/
theorem left_side_interlacing_impossible {P Q : Set Plane} {a b c d : ℝ}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hPS : P ⊆ unitSquare) (hQS : Q ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior Q))
    (ha : 0 ≤ a) (hab : a < b) (hbc : b < c) (hcd : c < d) (hd : d ≤ 1)
    (haP : Schoenflies.Plane.mk 0 a ∈ P)
    (hcP : Schoenflies.Plane.mk 0 c ∈ P)
    (hbQ : Schoenflies.Plane.mk 0 b ∈ Q)
    (hdQ : Schoenflies.Plane.mk 0 d ∈ Q) : False := by
  apply transported_bottom_side_interlacing_impossible
    RectangularHull.squareCoordinateSwap
    RectangularHull.squareCoordinateSwap_image_unitSquare
    hP hQ hPS hQS hdis ha hab hbc hcd hd
  · simpa only [RectangularHull.squareCoordinateSwap_mk] using
      mem_image_of_mem RectangularHull.squareCoordinateSwap haP
  · simpa only [RectangularHull.squareCoordinateSwap_mk] using
      mem_image_of_mem RectangularHull.squareCoordinateSwap hcP
  · simpa only [RectangularHull.squareCoordinateSwap_mk] using
      mem_image_of_mem RectangularHull.squareCoordinateSwap hbQ
  · simpa only [RectangularHull.squareCoordinateSwap_mk] using
      mem_image_of_mem RectangularHull.squareCoordinateSwap hdQ

private theorem flip_three_mk (x y : ℝ) :
    SquareSymmetry.cornerFlip 3 (Schoenflies.Plane.mk x y) =
      Schoenflies.Plane.mk x (1 - y) := by
  ext i
  fin_cases i <;>
    norm_num [SquareSymmetry.cornerFlipPoint, corner, Fin.ext_iff]

/-- Two Jordan regions with disjoint interiors cannot alternate along the top
side, in increasing horizontal order. -/
theorem top_side_interlacing_impossible {P Q : Set Plane} {a b c d : ℝ}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hPS : P ⊆ unitSquare) (hQS : Q ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior Q))
    (ha : 0 ≤ a) (hab : a < b) (hbc : b < c) (hcd : c < d) (hd : d ≤ 1)
    (haP : Schoenflies.Plane.mk a 1 ∈ P)
    (hcP : Schoenflies.Plane.mk c 1 ∈ P)
    (hbQ : Schoenflies.Plane.mk b 1 ∈ Q)
    (hdQ : Schoenflies.Plane.mk d 1 ∈ Q) : False := by
  apply transported_bottom_side_interlacing_impossible
    (SquareSymmetry.cornerFlip 3).toHomeomorph
    (SquareSymmetry.cornerFlip_image_unitSquare 3)
    hP hQ hPS hQS hdis ha hab hbc hcd hd
  · simpa only [AffineIsometryEquiv.coe_toHomeomorph, flip_three_mk, sub_self] using
      mem_image_of_mem (SquareSymmetry.cornerFlip 3) haP
  · simpa only [AffineIsometryEquiv.coe_toHomeomorph, flip_three_mk, sub_self] using
      mem_image_of_mem (SquareSymmetry.cornerFlip 3) hcP
  · simpa only [AffineIsometryEquiv.coe_toHomeomorph, flip_three_mk, sub_self] using
      mem_image_of_mem (SquareSymmetry.cornerFlip 3) hbQ
  · simpa only [AffineIsometryEquiv.coe_toHomeomorph, flip_three_mk, sub_self] using
      mem_image_of_mem (SquareSymmetry.cornerFlip 3) hdQ

/-- Two Jordan regions with disjoint interiors cannot alternate along the right
side, in increasing vertical order. -/
theorem right_side_interlacing_impossible {P Q : Set Plane} {a b c d : ℝ}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hPS : P ⊆ unitSquare) (hQS : Q ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior Q))
    (ha : 0 ≤ a) (hab : a < b) (hbc : b < c) (hcd : c < d) (hd : d ≤ 1)
    (haP : Schoenflies.Plane.mk 1 a ∈ P)
    (hcP : Schoenflies.Plane.mk 1 c ∈ P)
    (hbQ : Schoenflies.Plane.mk 1 b ∈ Q)
    (hdQ : Schoenflies.Plane.mk 1 d ∈ Q) : False := by
  have hPS' : RectangularHull.squareCoordinateSwap '' P ⊆ unitSquare :=
    RectangularHull.squareCoordinateSwap_image_unitSquare ▸ image_mono hPS
  have hQS' : RectangularHull.squareCoordinateSwap '' Q ⊆ unitSquare :=
    RectangularHull.squareCoordinateSwap_image_unitSquare ▸ image_mono hQS
  apply top_side_interlacing_impossible
    (hP.image_homeomorph RectangularHull.squareCoordinateSwap)
    (hQ.image_homeomorph RectangularHull.squareCoordinateSwap) hPS' hQS'
    (RectangularHull.disjoint_interiors_image_homeomorph hdis
      RectangularHull.squareCoordinateSwap)
    ha hab hbc hcd hd
  · simpa only [RectangularHull.squareCoordinateSwap_mk] using
      mem_image_of_mem RectangularHull.squareCoordinateSwap haP
  · simpa only [RectangularHull.squareCoordinateSwap_mk] using
      mem_image_of_mem RectangularHull.squareCoordinateSwap hcP
  · simpa only [RectangularHull.squareCoordinateSwap_mk] using
      mem_image_of_mem RectangularHull.squareCoordinateSwap hbQ
  · simpa only [RectangularHull.squareCoordinateSwap_mk] using
      mem_image_of_mem RectangularHull.squareCoordinateSwap hdQ

/-- Side indices are bottom, right, top, left.  The varying coordinate always
increases with `t`, including on the top and left sides. -/
def sidePoint (s : Fin 4) (t : ℝ) : Plane :=
  if s = 0 then Schoenflies.Plane.mk t 0
  else if s = 1 then Schoenflies.Plane.mk 1 t
  else if s = 2 then Schoenflies.Plane.mk t 1
  else Schoenflies.Plane.mk 0 t

@[simp] theorem sidePoint_zero (t : ℝ) :
    sidePoint 0 t = Schoenflies.Plane.mk t 0 := rfl

@[simp] theorem sidePoint_one (t : ℝ) :
    sidePoint 1 t = Schoenflies.Plane.mk 1 t := rfl

@[simp] theorem sidePoint_two (t : ℝ) :
    sidePoint 2 t = Schoenflies.Plane.mk t 1 := rfl

@[simp] theorem sidePoint_three (t : ℝ) :
    sidePoint 3 t = Schoenflies.Plane.mk 0 t := rfl

theorem continuous_sidePoint (s : Fin 4) : Continuous (sidePoint s) := by
  fin_cases s
  · change Continuous (fun t : ℝ => Schoenflies.Plane.mk t 0)
    fun_prop
  · change Continuous (fun t : ℝ => Schoenflies.Plane.mk 1 t)
    fun_prop
  · change Continuous (fun t : ℝ => Schoenflies.Plane.mk t 1)
    fun_prop
  · change Continuous (fun t : ℝ => Schoenflies.Plane.mk 0 t)
    fun_prop

theorem sidePoint_injective (s : Fin 4) : Function.Injective (sidePoint s) := by
  intro x y h
  fin_cases s
  · exact (Schoenflies.Plane.mk_inj h).1
  · exact (Schoenflies.Plane.mk_inj h).2
  · exact (Schoenflies.Plane.mk_inj h).1
  · exact (Schoenflies.Plane.mk_inj h).2

@[simp] theorem sidePoint_mem_unitSquare_iff (s : Fin 4) (t : ℝ) :
    sidePoint s t ∈ unitSquare ↔ t ∈ Icc (0 : ℝ) 1 := by
  fin_cases s <;> simp [sidePoint, unitSquare, Fin.ext_iff]

theorem sidePoint_mem_unitSquare (s : Fin 4) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    sidePoint s t ∈ unitSquare :=
  (sidePoint_mem_unitSquare_iff s t).mpr ht

/-- Uniform noninterlacing theorem for any one of the four square sides. -/
theorem side_interlacing_impossible (s : Fin 4) {P Q : Set Plane} {a b c d : ℝ}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hPS : P ⊆ unitSquare) (hQS : Q ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior Q))
    (ha : 0 ≤ a) (hab : a < b) (hbc : b < c) (hcd : c < d) (hd : d ≤ 1)
    (haP : sidePoint s a ∈ P) (hcP : sidePoint s c ∈ P)
    (hbQ : sidePoint s b ∈ Q) (hdQ : sidePoint s d ∈ Q) : False := by
  fin_cases s
  · exact RectangularHull.bottom_side_interlacing_impossible
      hP hQ hPS hQS hdis ha hab hbc hcd hd haP hcP hbQ hdQ
  · exact right_side_interlacing_impossible
      hP hQ hPS hQS hdis ha hab hbc hcd hd haP hcP hbQ hdQ
  · exact top_side_interlacing_impossible
      hP hQ hPS hQS hdis ha hab hbc hcd hd haP hcP hbQ hdQ
  · exact left_side_interlacing_impossible
      hP hQ hPS hQS hdis ha hab hbc hcd hd haP hcP hbQ hdQ

/-- Distinct pieces in an actual square dissection satisfy the same-side
obstruction, without extra regularity or contact assumptions. -/
theorem squareDissection_side_interlacing_impossible
    (D : SquareDissection) (s : Fin 4) {i j : Fin 4} (hij : i ≠ j) {a b c d : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hbc : b < c) (hcd : c < d) (hd : d ≤ 1)
    (haP : sidePoint s a ∈ D.piece i) (hcP : sidePoint s c ∈ D.piece i)
    (hbQ : sidePoint s b ∈ D.piece j) (hdQ : sidePoint s d ∈ D.piece j) : False :=
  side_interlacing_impossible s (D.jordan i) (D.jordan j)
    (D.piece_subset i) (D.piece_subset j) (D.disjoint_interiors hij)
    ha hab hbc hcd hd haP hcP hbQ hdQ

end Puzzling139335.N4TwoOneOne.BoundaryIntervals
