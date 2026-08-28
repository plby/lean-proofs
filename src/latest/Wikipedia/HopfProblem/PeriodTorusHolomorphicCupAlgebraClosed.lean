import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupAlgebraProduct

/-!
# The literal total cup of closed one-cochains is closed

The mixed calculations use the actual derivation Leibniz laws and
their coface compatibility. All closedness conditions are extracted
from the actual signed total differential.
-/

universe u

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Algebra.Data

variable {R0 R1 R2 R3 : Type u}
  [CommRing R0] [CommRing R1] [CommRing R2] [CommRing R3]
  (D : Data R0 R1 R2 R3)

theorem closed_vertical {x : D.One} (hx : D.d1 x = 0) : D.cofaces.d1 x.1 = 0 :=
  congrArg Prod.fst hx

theorem closed_mixed0 {x : D.One} (hx : D.d1 x = 0) :
    D.deriv1 0 x.1 = D.cofaces.d0 x.2.1 := by
  have h : -D.deriv1 0 x.1 + D.cofaces.d0 x.2.1 = 0 :=
    congrArg (fun y : D.Two => y.2.1.1) hx
  have h' := congrArg (fun y => D.deriv1 0 x.1 + y) h
  simpa [add_assoc] using h'.symm

theorem closed_mixed1 {x : D.One} (hx : D.d1 x = 0) :
    D.deriv1 1 x.1 = D.cofaces.d0 x.2.2 := by
  have h : -D.deriv1 1 x.1 + D.cofaces.d0 x.2.2 = 0 :=
    congrArg (fun y : D.Two => y.2.1.2) hx
  have h' := congrArg (fun y => D.deriv1 1 x.1 + y) h
  simpa [add_assoc] using h'.symm

theorem closed_horizontal {x : D.One} (hx : D.d1 x = 0) : D.curl0 x.2 = 0 :=
  congrArg (fun y : D.Two => y.2.2) hx

theorem closed_horizontal_eq {x : D.One} (hx : D.d1 x = 0) :
    D.deriv0 0 x.2.2 = D.deriv0 1 x.2.1 :=
  sub_eq_zero.mp (D.closed_horizontal hx)

/-- The middle coface of an actual vertical cocycle is the sum of the endpoint cofaces. -/
theorem vertical_middle {a : R1} (ha : D.cofaces.d1 a = 0) :
    D.cofaces.δ1 1 a = D.cofaces.δ1 0 a + D.cofaces.δ1 2 a := by
  apply sub_eq_zero.mp
  calc
    _ = -D.cofaces.d1 a := by
      rw [SheafCupProduct.Coface.Data.d1_apply]
      ring
    _ = 0 := by rw [ha, neg_zero]

/-- The actual mixed `(2,1)` differential component vanishes. -/
theorem mixed_cup_closed (j : Fin 2) {a c : R1} {b d : R0}
    (ha : D.cofaces.d1 a = 0) (hc : D.cofaces.d1 c = 0)
    (hab : D.deriv1 j a = D.cofaces.d0 b)
    (hcd : D.deriv1 j c = D.cofaces.d0 d) :
    D.deriv2 j (D.cofaces.cupOne a c) +
      D.cofaces.d1 (D.mixedCup a b c d) = 0 := by
  simp only [SheafCupProduct.Coface.Data.cupOne, D.leibniz2, D.coface1, hab, hcd,
    mixedCup, SheafCupProduct.Coface.Data.d0_apply,
    SheafCupProduct.Coface.Data.d1_apply, map_sub, map_mul]
  simp only [D.cofaces.coface01_00, D.cofaces.coface01_01, D.cofaces.coface01_11,
    D.vertical_middle ha, D.vertical_middle hc]
  ring

/-- The actual mixed `(1,2)` differential component vanishes. -/
theorem horizontal_cup_closed {a c : R1} {b d : R0 × R0}
    (hab0 : D.deriv1 0 a = D.cofaces.d0 b.1)
    (hab1 : D.deriv1 1 a = D.cofaces.d0 b.2)
    (hcd0 : D.deriv1 0 c = D.cofaces.d0 d.1)
    (hcd1 : D.deriv1 1 c = D.cofaces.d0 d.2)
    (hb : D.deriv0 0 b.2 = D.deriv0 1 b.1)
    (hd : D.deriv0 0 d.2 = D.deriv0 1 d.1) :
    -D.curl1 (D.mixedCup a b.1 c d.1, D.mixedCup a b.2 c d.2) +
      D.cofaces.d0 (D.wedge b d) = 0 := by
  simp only [curl_apply, mixedCup, wedge, map_sub, D.leibniz1, D.coface0,
    hab0, hab1, hcd0, hcd1, hb, hd, SheafCupProduct.Coface.Data.d0_apply, map_mul]
  ring

/-- The signed literal total product of two actual closed cochains is closed. -/
theorem cupOne_isCocycle {x y : D.One} (hx : D.d1 x = 0) (hy : D.d1 y = 0) :
    D.d2 (D.cupOne x y) = 0 := by
  apply Prod.ext
  · exact D.cofaces.cupOne_isCocycle (D.closed_vertical hx) (D.closed_vertical hy)
  · apply Prod.ext
    · apply Prod.ext
      · exact D.mixed_cup_closed 0 (D.closed_vertical hx) (D.closed_vertical hy)
          (D.closed_mixed0 hx) (D.closed_mixed0 hy)
      · exact D.mixed_cup_closed 1 (D.closed_vertical hx) (D.closed_vertical hy)
          (D.closed_mixed1 hx) (D.closed_mixed1 hy)
    · apply Prod.ext
      · exact D.horizontal_cup_closed (D.closed_mixed0 hx) (D.closed_mixed1 hx)
          (D.closed_mixed0 hy) (D.closed_mixed1 hy)
          (D.closed_horizontal_eq hx) (D.closed_horizontal_eq hy)
      · exact Subsingleton.elim _ _

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Algebra.Data
