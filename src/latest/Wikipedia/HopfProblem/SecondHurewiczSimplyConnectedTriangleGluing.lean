import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTriangleSquareGeometry

/-!
# Gluing actual triangle homotopies along the square diagonal

The diagonal is the face opposite vertex one in both of the original
square-chain triangles. Agreement there is enough for continuous gluing.
Fixing their other two faces fixes the original square perimeter.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

open FirstHurewicz

theorem lowerSquareTriangle_quotient (t : Fin 2 → I) (h : (t 1 : ℝ) ≤ t 0) :
    lowerSquareTriangle (triangleQuotient (t 0, t 1)) = t := by
  funext i
  apply Subtype.ext
  fin_cases i
  · change (lowerSquareTriangle (triangleQuotient (t 0, t 1)) 0 : ℝ) = (t 0 : ℝ)
    rw [lowerSquareTriangle_zero, triangleQuotient_one, triangleQuotient_two]
    ring
  · change (lowerSquareTriangle (triangleQuotient (t 0, t 1)) 1 : ℝ) = (t 1 : ℝ)
    rw [lowerSquareTriangle_one, triangleQuotient_two, min_eq_right h]

theorem upperSquareTriangle_quotient (t : Fin 2 → I) (h : (t 0 : ℝ) ≤ t 1) :
    upperSquareTriangle (triangleQuotient (t 1, t 0)) = t := by
  funext i
  apply Subtype.ext
  fin_cases i
  · change (upperSquareTriangle (triangleQuotient (t 1, t 0)) 0 : ℝ) = (t 0 : ℝ)
    rw [upperSquareTriangle_zero, triangleQuotient_two, min_eq_right h]
  · change (upperSquareTriangle (triangleQuotient (t 1, t 0)) 1 : ℝ) = (t 1 : ℝ)
    rw [upperSquareTriangle_one, triangleQuotient_one, triangleQuotient_two]
    ring

theorem triangleQuotient_perimeter_of_le (z : I × I)
    (hper : z.1 = 0 ∨ z.1 = 1 ∨ z.2 = 0 ∨ z.2 = 1)
    (hle : (z.2 : ℝ) ≤ z.1) :
    triangleQuotient z 0 = 0 ∨ triangleQuotient z 2 = 0 := by
  rcases hper with h | h | h | h
  · right
    rw [triangleQuotient_two, h]
    exact min_eq_left z.2.property.1
  · left
    rw [triangleQuotient_zero, h]
    norm_num
  · right
    rw [triangleQuotient_two, h]
    exact min_eq_right z.1.property.1
  · have hu : z.1 = 1 := Subtype.ext
      (le_antisymm z.1.property.2 (by simpa only [h] using hle))
    left
    rw [triangleQuotient_zero, hu]
    norm_num

theorem cubeBoundary_productBoundary (t : Fin 2 → I)
    (ht : t ∈ Cube.boundary (Fin 2)) :
    t 0 = 0 ∨ t 0 = 1 ∨ t 1 = 0 ∨ t 1 = 1 := by
  rcases ht with ⟨i, hi | hi⟩
  · fin_cases i
    · exact Or.inl hi
    · exact Or.inr (Or.inr (Or.inl hi))
  · fin_cases i
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr (Or.inr hi))

variable {X : Type} [TopologicalSpace X]

/-- Continuous diagonal gluing of two actual parameterized triangle maps. -/
def gluedTriangleHomotopyMap (L U : C(I × Simplex 2, X))
    (hdiag : ∀ r s, s 1 = 0 → L (r, s) = U (r, s)) :
    C(I × (Fin 2 → I), X) where
  toFun z := if (z.2 1 : ℝ) ≤ z.2 0 then
    L (z.1, triangleQuotient (z.2 0, z.2 1)) else
    U (z.1, triangleQuotient (z.2 1, z.2 0))
  continuous_toFun := by
    apply Continuous.if_le (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    intro z h
    have he : z.2 1 = z.2 0 := Subtype.ext h
    have hq : triangleQuotient (z.2 0, z.2 1) 1 = 0 := by
      simp only [triangleQuotient_one, he, min_self, sub_self]
    simpa only [he] using hdiag z.1 (triangleQuotient (z.2 0, z.2 1)) hq

theorem gluedTriangleHomotopyMap_boundary (L U : C(I × Simplex 2, X))
    (hdiag : ∀ r s, s 1 = 0 → L (r, s) = U (r, s)) (x : X)
    (hL : ∀ r s, s 0 = 0 ∨ s 2 = 0 → L (r, s) = x)
    (hU : ∀ r s, s 0 = 0 ∨ s 2 = 0 → U (r, s) = x)
    (r : I) (t : Fin 2 → I) (ht : t ∈ Cube.boundary (Fin 2)) :
    gluedTriangleHomotopyMap L U hdiag (r, t) = x := by
  have hp := cubeBoundary_productBoundary t ht
  change (if (t 1 : ℝ) ≤ t 0 then _ else _) = x
  split_ifs with h
  · exact hL r _ (triangleQuotient_perimeter_of_le (t 0, t 1) hp h)
  · have hp' : t 1 = 0 ∨ t 1 = 1 ∨ t 0 = 0 ∨ t 0 = 1 := by
      rcases hp with hp | hp | hp | hp
      · exact Or.inr (Or.inr (Or.inl hp))
      · exact Or.inr (Or.inr (Or.inr hp))
      · exact Or.inl hp
      · exact Or.inr (Or.inl hp)
    exact hU r _ (triangleQuotient_perimeter_of_le (t 1, t 0) hp' (le_of_not_ge h))

/-- Compatible homotopies of the original principal triangles glue to a
homotopy of the original native square relative to its whole boundary. -/
def gluedTriangleHomotopy {x : X} {p q : GenLoop (Fin 2) X x}
    (L : (p.val.comp lowerSquareTriangle).Homotopy (q.val.comp lowerSquareTriangle))
    (U : (p.val.comp upperSquareTriangle).Homotopy (q.val.comp upperSquareTriangle))
    (hdiag : ∀ r s, s 1 = 0 → L (r, s) = U (r, s))
    (hL : ∀ r s, s 0 = 0 ∨ s 2 = 0 → L (r, s) = x)
    (hU : ∀ r s, s 0 = 0 ∨ s 2 = 0 → U (r, s) = x) :
    p.val.HomotopyRel q.val (Cube.boundary (Fin 2)) where
  toContinuousMap := gluedTriangleHomotopyMap L.toContinuousMap U.toContinuousMap hdiag
  map_zero_left t := by
    change (if (t 1 : ℝ) ≤ t 0 then _ else _) = p.val t
    split_ifs with h
    · change L (0, triangleQuotient (t 0, t 1)) = p.val t
      rw [L.apply_zero]
      change p.val (lowerSquareTriangle (triangleQuotient (t 0, t 1))) = p.val t
      rw [lowerSquareTriangle_quotient t h]
    · change U (0, triangleQuotient (t 1, t 0)) = p.val t
      rw [U.apply_zero]
      change p.val (upperSquareTriangle (triangleQuotient (t 1, t 0))) = p.val t
      rw [upperSquareTriangle_quotient t (le_of_not_ge h)]
  map_one_left t := by
    change (if (t 1 : ℝ) ≤ t 0 then _ else _) = q.val t
    split_ifs with h
    · change L (1, triangleQuotient (t 0, t 1)) = q.val t
      rw [L.apply_one]
      change q.val (lowerSquareTriangle (triangleQuotient (t 0, t 1))) = q.val t
      rw [lowerSquareTriangle_quotient t h]
    · change U (1, triangleQuotient (t 1, t 0)) = q.val t
      rw [U.apply_one]
      change q.val (upperSquareTriangle (triangleQuotient (t 1, t 0))) = q.val t
      rw [upperSquareTriangle_quotient t (le_of_not_ge h)]
  prop' r t ht := (gluedTriangleHomotopyMap_boundary L.toContinuousMap U.toContinuousMap
    hdiag x hL hU r t ht).trans (GenLoop.boundary p t ht).symm

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
