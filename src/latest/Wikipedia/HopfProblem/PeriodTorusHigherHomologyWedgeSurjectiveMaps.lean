import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusGroupsCoordinateTransport
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusHomomorphisms

/-!
# Additivity of the actual coordinate-subtorus maps

The coordinate inclusions and their transports into period tori preserve
the actual addition of points. These identities supply the additive-map
hypotheses for naturality of the Pontryagin product; they do not replace
the continuous maps by abstract homology maps.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open Elliptic

/-- The actual continuous matrix map preserves addition of torus points. -/
@[simp] theorem torusMatrixMap_add {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (x y : ProductTorus n) :
    torusMatrixMap A (x + y) = torusMatrixMap A x + torusMatrixMap A y :=
  (torusMatrixLinearMap A).map_add x y

/-- Every actual coordinate-subtorus inclusion preserves addition. -/
@[simp] theorem coordinateTorusMap_add (r n : ℕ) (i : Fin (r.choose n))
    (x y : ProductTorus n) :
    coordinateTorusMap r n i (x + y) =
      coordinateTorusMap r n i x + coordinateTorusMap r n i y := by
  simpa only [coordinateTorusMap_eq_torusMatrixMap] using
    torusMatrixMap_add (coordinateTorusMatrix r n i) x y

/-- The inverse of an additive homeomorphism is additive, with no
compatibility between addition and the topology needed for this identity. -/
theorem homeomorph_symm_add_of_add {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [Add X] [Add Y]
    (e : X ≃ₜ Y) (he : ∀ x y, e (x + y) = e x + e y) (x y : Y) :
    e.symm (x + y) = e.symm x + e.symm y := by
  apply e.injective
  rw [Homeomorph.apply_symm_apply, he, Homeomorph.apply_symm_apply,
    Homeomorph.apply_symm_apply]

/-- Coordinate inclusions transported through an additive homeomorphism
still preserve the literal addition of points. -/
theorem coordinateTorusMapAlong_add {X : Type} [TopologicalSpace X] [Add X] {r : ℕ}
    (e : X ≃ₜ ProductTorus r) (he : ∀ x y, e (x + y) = e x + e y)
    (n : ℕ) (i : Fin (r.choose n)) (x y : ProductTorus n) :
    coordinateTorusMapAlong e n i (x + y) =
      coordinateTorusMapAlong e n i x + coordinateTorusMapAlong e n i y := by
  change e.symm (coordinateTorusMap r n i (x + y)) =
    e.symm (coordinateTorusMap r n i x) + e.symm (coordinateTorusMap r n i y)
  rw [coordinateTorusMap_add]
  exact homeomorph_symm_add_of_add e he _ _

/-- The actual inverse period-coordinate homeomorphism preserves addition. -/
@[simp] theorem periodTorusCircleHomeomorph_symm_add (p : PeriodDomain)
    (x y : ProductTorus 4) :
    (periodTorusCircleHomeomorph p).symm (x + y) =
      (periodTorusCircleHomeomorph p).symm x + (periodTorusCircleHomeomorph p).symm y :=
  (periodTorusCircleAddEquiv p).symm.map_add x y

/-- The actual coordinate-subtorus maps into a period torus are additive. -/
@[simp] theorem periodTorusCoordinateMap_add (p : PeriodDomain) (n : ℕ)
    (i : Fin (Nat.choose 4 n)) (x y : ProductTorus n) :
    periodTorusCoordinateMap p n i (x + y) =
      periodTorusCoordinateMap p n i x + periodTorusCoordinateMap p n i y :=
  coordinateTorusMapAlong_add (periodTorusCircleHomeomorph p)
    (periodTorusCircleHomeomorph_add p) n i x y

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
