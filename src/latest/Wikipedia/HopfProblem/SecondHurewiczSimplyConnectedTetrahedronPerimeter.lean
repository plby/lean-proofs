import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTetrahedronFill
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTetrahedronRotation

/-!
# The two actual tetrahedral fillings have the same perimeter

The second filling uses the other diagonal of the quadrilateral. Affine
interpolation in the tetrahedron is consequently fixed on the perimeter,
before even composing with the given singular tetrahedron.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

open FirstHurewicz

/-- The diagonal `13` filling, with the same ordered perimeter as `A`. -/
def tetrahedronQuadrilateralB : C(Fin 2 → I, Simplex 3) :=
  (tetrahedronQuarterShift.comp tetrahedronQuadrilateralA).comp quarterTurn

@[simp] theorem tetrahedronQuadrilateralB_apply (u : Fin 2 → I) :
    tetrahedronQuadrilateralB u =
      tetrahedronQuarterShift (tetrahedronQuadrilateralA ![u 1, σ (u 0)]) := rfl

/-- These are equal as actual points, not merely after collapsing the skeleton. -/
theorem tetrahedronQuadrilateral_perimeter (u : Fin 2 → I)
    (hu : u ∈ Cube.boundary (Fin 2)) :
    tetrahedronQuadrilateralA u = tetrahedronQuadrilateralB u := by
  apply Subtype.ext
  funext j
  change tetrahedronQuadrilateralA u j = tetrahedronQuadrilateralB u j
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      fin_cases j <;>
        simp [hi, min_eq_left (u 1).property.2, max_eq_right (u 1).property.2,
          min_eq_left (u 1).property.1, max_eq_right (u 1).property.1]
    · change u 1 = 0 at hi
      fin_cases j <;>
        simp [hi, min_eq_right (u 0).property.1, max_eq_left (u 0).property.1,
          (u 0).property.2]
  · fin_cases i
    · change u 0 = 1 at hi
      fin_cases j <;>
        simp [hi, min_eq_right (u 1).property.2, max_eq_left (u 1).property.2,
          min_eq_right (u 1).property.1, max_eq_left (u 1).property.1]
    · change u 1 = 1 at hi
      fin_cases j <;>
        simp [hi, min_eq_left (u 0).property.2, max_eq_right (u 0).property.2,
          (u 0).property.1]

variable {X : Type} [TopologicalSpace X] {x : X}

/-- The convex homotopy is literally fixed on the whole cube boundary. -/
def tetrahedronFillingsHomotopy (τ : BasedTetrahedron x) :
    (tetrahedronQuadrilateralLoop τ).val.HomotopyRel
      (rotatedSquareLoop (tetrahedronShiftedQuadrilateralLoop τ)).val
        (Cube.boundary (Fin 2)) where
  toFun p := τ.val
    (tetrahedronSimplexBlend p.1 (tetrahedronQuadrilateralA p.2)
      (tetrahedronQuadrilateralB p.2))
  continuous_toFun := τ.val.continuous.comp
    (tetrahedronSimplexBlendMap tetrahedronQuadrilateralA tetrahedronQuadrilateralB).continuous
  map_zero_left u := by
    change τ.val (tetrahedronSimplexBlend 0 _ _) = τ.val (tetrahedronQuadrilateralA u)
    rw [tetrahedronSimplexBlend_zero]
  map_one_left u := by
    change τ.val (tetrahedronSimplexBlend 1 _ _) = τ.val (tetrahedronQuadrilateralB u)
    rw [tetrahedronSimplexBlend_one]
  prop' t u hu := by
    change τ.val (tetrahedronSimplexBlend t _ _) = τ.val (tetrahedronQuadrilateralA u)
    rw [← tetrahedronQuadrilateral_perimeter u hu, tetrahedronSimplexBlend_self]

theorem tetrahedronFillings_homotopic (τ : BasedTetrahedron x) :
    GenLoop.Homotopic (tetrahedronQuadrilateralLoop τ)
      (rotatedSquareLoop (tetrahedronShiftedQuadrilateralLoop τ)) :=
  ⟨tetrahedronFillingsHomotopy τ⟩

/-- The two face pairs determine the same actual second homotopy class. -/
theorem tetrahedronFillings_class (τ : BasedTetrahedron x) :
    (⟦tetrahedronQuadrilateralLoop τ⟧ : π_ 2 X x) =
      ⟦tetrahedronShiftedQuadrilateralLoop τ⟧ :=
  (Quotient.sound (tetrahedronFillings_homotopic τ)).trans
    (rotatedSquareLoop_class (tetrahedronShiftedQuadrilateralLoop τ))

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
