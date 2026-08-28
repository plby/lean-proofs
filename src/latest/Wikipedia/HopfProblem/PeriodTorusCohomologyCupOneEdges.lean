import Wikipedia.HopfProblem.PeriodTorusCohomologyCupOneBasic
import Wikipedia.HopfProblem.PeriodTorusCohomologyCupOneAffine
import Wikipedia.HopfProblem.SingularCohomologyCupCochains

/-!
# Exact coordinate cocycle values on affine torus edges

Every integral vertex has the same image in the actual torus.  Consequently
the restriction to any ordered pair of vertices is the actual period loop
of their difference.  The Alexander–Whitney formulas below are evaluations
of the native cup cochains on the actual affine singular simplices.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusCohomologyCup

open FirstHurewicz PeriodTorusHigherHomology SingularCohomologyCup

/-- Coordinate cocycles on a literal affine singular edge read its endpoint difference. -/
@[simp] theorem coordinateOneCochain_affineSimplex (n : ℕ) (i : Fin n)
    (v : Fin 2 → Fin n → ℤ) :
    coordinateOneCochain n i (simplexChain (ProductTorus n) 1 (affineTorusSimplex v)) =
      v 1 i - v 0 i := by
  rw [affineTorusSimplex_one, coordinateOneCochain_periodLoop]
  rfl

/-- The native vertex-map convention used by the cup product agrees with
literal restriction of the integer-affine simplex. -/
theorem affineTorusSimplex_vertexMap {n k l : ℕ}
    (v : Fin (k + 1) → Fin n → ℤ) (f : Fin (l + 1) → Fin (k + 1)) :
    (affineTorusSimplex v).comp (vertexMap f) = affineTorusSimplex (v ∘ f) :=
  affineTorusSimplex_restrict v f

/-- This applies to every ordered pair, including repeated or reversed vertices. -/
theorem coordinateOneCochain_affineEdge {n k : ℕ} (i : Fin n)
    (v : Fin (k + 1) → Fin n → ℤ) (f : Fin 2 → Fin (k + 1)) :
    coordinateOneCochain n i
      (simplexChain (ProductTorus n) 1 ((affineTorusSimplex v).comp (vertexMap f))) =
        v (f 1) i - v (f 0) i := by
  rw [affineTorusSimplex_vertexMap, coordinateOneCochain_affineSimplex]
  rfl

/-- The exact window-face form, useful inside iterated Alexander–Whitney products. -/
theorem coordinateOneCochain_affineWindow {n k : ℕ} (i : Fin n)
    (v : Fin (k + 1) → Fin n → ℤ) (a : ℕ) (ha : a + 1 ≤ k) :
    coordinateOneCochain n i
      (simplexChain (ProductTorus n) 1
        ((affineTorusSimplex v).comp (windowFace a 1 k ha))) =
      v (windowIndex a 1 k ha 1) i - v (windowIndex a 1 k ha 0) i :=
  coordinateOneCochain_affineEdge i v _

/-- The genuine cup of two coordinate one-cochains on an affine triangle. -/
theorem coordinateOneCup_affineSimplex (n : ℕ) (i j : Fin n)
    (v : Fin 3 → Fin n → ℤ) :
    cup (coordinateOneCochain n i) (coordinateOneCochain n j)
      (simplexChain (ProductTorus n) 2 (affineTorusSimplex v)) =
      (v 1 i - v 0 i) * (v 2 j - v 1 j) := by
  rw [cup_simplex]
  simp only [frontFace, backFace, coordinateOneCochain_affineWindow]
  rfl

/-- Four successive coordinate differences are the literal front/back cup evaluation. -/
theorem coordinateOneCupCup_affineSimplex (n : ℕ) (i j k l : Fin n)
    (v : Fin 5 → Fin n → ℤ) :
    cup (cup (coordinateOneCochain n i) (coordinateOneCochain n j))
        (cup (coordinateOneCochain n k) (coordinateOneCochain n l))
      (simplexChain (ProductTorus n) 4 (affineTorusSimplex v)) =
      ((v 1 i - v 0 i) * (v 2 j - v 1 j)) *
        ((v 3 k - v 2 k) * (v 4 l - v 3 l)) := by
  rw [cup_simplex]
  simp only [frontFace, backFace, windowFace, affineTorusSimplex_vertexMap]
  exact congrArg₂ (fun a b : ℤ => a * b)
    (coordinateOneCup_affineSimplex n i j (v ∘ windowIndex 0 2 4 (by decide)))
    (coordinateOneCup_affineSimplex n k l (v ∘ windowIndex 2 2 4 (by decide)))

/-- The native cup-complex coboundary of each coordinate representative is zero. -/
@[simp] theorem coordinateOneCochain_coboundary (n : ℕ) (i : Fin n) :
    coboundary (coordinateOneCochain n i) = 0 :=
  coordinateOneCochain_closed n i

end Wikipedia.HopfProblem.PeriodTorusCohomologyCup
