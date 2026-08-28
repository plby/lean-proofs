import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupFirstAlgebraBasic

/-!
# First-column maps on the actual total kernels and boundaries
-/

universe u

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.FirstAlgebra.Data

variable {A0 A1 A2 A3 R0 R1 R2 R3 : Type u}
  [CommRing A0] [CommRing A1] [CommRing A2] [CommRing A3]
  [CommRing R0] [CommRing R1] [CommRing R2] [CommRing R3]
  {E : SheafCupProduct.Coface.Data A0 A1 A2 A3}
  {D : Algebra.Data R0 R1 R2 R3} (F : Data E D)

theorem mapOne_isCocycle {x : A1} (hx : E.d1 x = 0) :
    D.d1 (F.mapOne x) = 0 := by
  rw [← F.d1_comm, hx, map_zero]

theorem mapTwo_isCocycle {x : A2} (hx : E.d2 x = 0) :
    D.d2 (F.mapTwo x) = 0 := by
  rw [← F.d2_comm, hx, map_zero]

/-- The literal first-column cochain map restricted to the first kernel. -/
def cocycleOneMap : E.CocycleOne →+ D.CocycleOne where
  toFun x := ⟨F.mapOne x, F.mapOne_isCocycle x.property⟩
  map_zero' := Subtype.ext (map_zero F.mapOne)
  map_add' x y := Subtype.ext (map_add F.mapOne (x : A1) (y : A1))

/-- The literal first-column cochain map restricted to the second kernel. -/
def cocycleTwoMap : E.CocycleTwo →+ D.CocycleTwo where
  toFun x := ⟨F.mapTwo x, F.mapTwo_isCocycle x.property⟩
  map_zero' := Subtype.ext (map_zero F.mapTwo)
  map_add' x y := Subtype.ext (map_add F.mapTwo (x : A2) (y : A2))

@[simp] theorem cocycleOneMap_coe (x : E.CocycleOne) :
    (F.cocycleOneMap x : D.One) = (F.morphism.f1 x, 0) := rfl

@[simp] theorem cocycleTwoMap_coe (x : E.CocycleTwo) :
    (F.cocycleTwoMap x : D.Two) = (F.morphism.f2 x, 0, 0) := rfl

/-- Each first boundary goes to the boundary of its original degree-zero image. -/
theorem cocycleOneMap_boundary (x : A0) :
    F.cocycleOneMap (E.boundaryOne x) = D.boundaryOne (F.mapZero x) :=
  Subtype.ext (F.d0_comm x)

/-- Each second boundary goes to the boundary of its original degree-one image. -/
theorem cocycleTwoMap_boundary (x : A1) :
    F.cocycleTwoMap (E.boundaryTwo x) = D.boundaryTwo (F.mapOne x) :=
  Subtype.ext (F.d1_comm x)

/-- The actual cochain cup is preserved by the original first-column ring maps. -/
theorem cupOne_comm (x y : A1) :
    F.mapTwo (E.cupOne x y) = D.cupOne (F.mapOne x) (F.mapOne y) := by
  rw [F.mapTwo_apply, F.mapOne_apply, F.mapOne_apply, D.cupOne_first,
    F.morphism.cupOne_comm]

/-- The actual first-column kernel map preserves the original cocycle product. -/
theorem cocycleTwoMap_cup (x y : E.CocycleOne) :
    F.cocycleTwoMap (E.cupCocycle x y) =
      D.cupCocycle (F.cocycleOneMap x) (F.cocycleOneMap y) :=
  Subtype.ext (F.cupOne_comm x y)

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.FirstAlgebra.Data
