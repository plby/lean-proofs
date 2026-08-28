import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupLastAlgebraBasic

/-!
# The literal last-row determinant in the existing total cohomology

Closed row pairs give actual total cocycles. Their already defined total
cup product is the actual total class of the determinant coefficient.
No separate row cup product or native cohomology marking is introduced.
-/

universe u

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.LastAlgebra.Data

variable {A R0 R1 R2 R3 : Type u}
  [CommRing A] [CommRing R0] [CommRing R1] [CommRing R2] [CommRing R3]
  {D : Algebra.Data R0 R1 R2 R3} (F : Data A D)

theorem mapOne_isCocycle {x : A × A} (hx : F.rowD1 x = 0) :
    D.d1 (F.mapOne x) = 0 := by
  rw [← F.d1_comm, hx, map_zero]

theorem mapTwo_isCocycle (x : A) : D.d2 (F.mapTwo x) = 0 := by
  rw [← F.d2_comm, F.mapThree_apply]

/-- A closed original row pair determines its literal total cocycle. -/
def oneCocycle (x : A × A) (hx : F.rowD1 x = 0) : D.CocycleOne :=
  ⟨F.mapOne x, F.mapOne_isCocycle hx⟩

/-- Every original row top coefficient determines its literal total cocycle. -/
def twoCocycle : A →+ D.CocycleTwo where
  toFun x := ⟨F.mapTwo x, F.mapTwo_isCocycle x⟩
  map_zero' := Subtype.ext (map_zero F.mapTwo)
  map_add' x y := Subtype.ext (map_add F.mapTwo x y)

@[simp] theorem oneCocycle_coe (x : A × A) (hx : F.rowD1 x = 0) :
    (F.oneCocycle x hx : D.One) = (0, (F.unit x.1, F.unit x.2)) := rfl

@[simp] theorem twoCocycle_coe (x : A) :
    (F.twoCocycle x : D.Two) = (0, 0, F.unit x) := rfl

/-- The original closed row pair, viewed in the existing total quotient. -/
def oneClass (x : A × A) (hx : F.rowD1 x = 0) : D.CohomologyOne :=
  D.classOne (F.oneCocycle x hx)

/-- The original top row coefficient, viewed in the existing total quotient. -/
def twoClass : A →+ D.CohomologyTwo := D.classTwo.comp F.twoCocycle

theorem oneCocycle_rowD0 (x : A) :
    F.oneCocycle (F.rowD0 x) (F.rowD1_rowD0 x) = D.boundaryOne (F.mapZero x) :=
  Subtype.ext (F.d0_comm x)

theorem twoCocycle_rowD1 (x : A × A) :
    F.twoCocycle (F.rowD1 x) = D.boundaryTwo (F.mapOne x) :=
  Subtype.ext (F.d1_comm x)

@[simp] theorem oneClass_rowD0 (x : A) :
    F.oneClass (F.rowD0 x) (F.rowD1_rowD0 x) = 0 := by
  change D.classOne (F.oneCocycle (F.rowD0 x) (F.rowD1_rowD0 x)) = 0
  rw [F.oneCocycle_rowD0, D.classOne_boundary]

@[simp] theorem twoClass_rowD1 (x : A × A) : F.twoClass (F.rowD1 x) = 0 := by
  change D.classTwo (F.twoCocycle (F.rowD1 x)) = 0
  rw [F.twoCocycle_rowD1, D.classTwo_boundary]

/-- Multiplication of literal last-row cochains has the original determinant coefficient. -/
theorem cupOne_comm (x y : A × A) :
    D.cupOne (F.mapOne x) (F.mapOne y) = F.mapTwo (x.1 * y.2 - x.2 * y.1) := by
  rw [F.mapOne_apply, F.mapOne_apply, D.cupOne_last, F.mapTwo_apply]
  simp only [map_sub, map_mul]

/-- The actual total cocycle cup retains the literal row determinant. -/
theorem cupCocycle_comm (x y : A × A) (hx : F.rowD1 x = 0) (hy : F.rowD1 y = 0) :
    D.cupCocycle (F.oneCocycle x hx) (F.oneCocycle y hy) =
      F.twoCocycle (x.1 * y.2 - x.2 * y.1) :=
  Subtype.ext (F.cupOne_comm x y)

/-- The existing total quotient cup is the actual class of the literal row determinant. -/
theorem cup_oneClass (x y : A × A) (hx : F.rowD1 x = 0) (hy : F.rowD1 y = 0) :
    D.cup (F.oneClass x hx) (F.oneClass y hy) = F.twoClass (x.1 * y.2 - x.2 * y.1) := by
  change D.cup (D.classOne (F.oneCocycle x hx)) (D.classOne (F.oneCocycle y hy)) =
    D.classTwo (F.twoCocycle (x.1 * y.2 - x.2 * y.1))
  rw [D.cup_classOne, F.cupCocycle_comm]

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.LastAlgebra.Data
