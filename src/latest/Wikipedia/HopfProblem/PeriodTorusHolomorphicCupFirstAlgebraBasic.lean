import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupAlgebraHomology
import Wikipedia.HopfProblem.SheafCupProductCofaceMorphism

/-!
# The actual first-column map to the Godement–Dolbeault total algebra

The input consists of degreewise ring maps commuting with the cofaces,
whose images have zero horizontal derivative. The signed total
differential squares are consequences of these literal conditions.
-/

universe u

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.FirstAlgebra

variable {A0 A1 A2 A3 R0 R1 R2 R3 : Type u}
  [CommRing A0] [CommRing A1] [CommRing A2] [CommRing A3]
  [CommRing R0] [CommRing R1] [CommRing R2] [CommRing R3]

/-- Coface-compatible ring maps with horizontally constant images. -/
structure Data (E : SheafCupProduct.Coface.Data A0 A1 A2 A3)
    (D : Algebra.Data R0 R1 R2 R3) where
  morphism : E.Morphism D.cofaces
  gradient0 : ∀ x, D.gradient0 (morphism.f0 x) = 0
  gradient1 : ∀ x, D.gradient1 (morphism.f1 x) = 0
  gradient2 : ∀ x, D.gradient2 (morphism.f2 x) = 0

namespace Data

variable {E : SheafCupProduct.Coface.Data A0 A1 A2 A3}
  {D : Algebra.Data R0 R1 R2 R3} (F : Data E D)

abbrev mapZero : A0 →+ D.Zero := F.morphism.f0.toAddMonoidHom

/-- The literal degree-one first-column inclusion. -/
def mapOne : A1 →+ D.One := F.morphism.f1.toAddMonoidHom.prod 0

/-- The literal degree-two first-column inclusion. -/
def mapTwo : A2 →+ D.Two := F.morphism.f2.toAddMonoidHom.prod 0

/-- The literal degree-three first-column inclusion. -/
def mapThree : A3 →+ D.Three := F.morphism.f3.toAddMonoidHom.prod 0

@[simp] theorem mapZero_apply (x : A0) : F.mapZero x = F.morphism.f0 x := rfl

@[simp] theorem mapOne_apply (x : A1) : F.mapOne x = (F.morphism.f1 x, 0) := rfl

@[simp] theorem mapTwo_apply (x : A2) : F.mapTwo x = (F.morphism.f2 x, 0, 0) := rfl

@[simp] theorem mapThree_apply (x : A3) :
    F.mapThree x = (F.morphism.f3 x, 0, 0, 0) := rfl

/-- The first-column ring map commutes with the initial total differential. -/
theorem d0_comm (x : A0) : F.mapOne (E.d0 x) = D.d0 (F.mapZero x) := by
  change (F.morphism.f1 (E.d0 x), 0) =
    (D.cofaces.d0 (F.morphism.f0 x), D.gradient0 (F.morphism.f0 x))
  rw [F.morphism.d0_comm, F.gradient0]

/-- The signed mixed term vanishes on the degree-one first column. -/
theorem d1_comm (x : A1) : F.mapTwo (E.d1 x) = D.d1 (F.mapOne x) := by
  change (F.morphism.f2 (E.d1 x), 0, 0) =
    (D.cofaces.d1 (F.morphism.f1 x),
      -D.gradient1 (F.morphism.f1 x) + Algebra.pairMap D.cofaces.d0 0, D.curl0 0)
  rw [F.morphism.d1_comm, F.gradient1, map_zero, neg_zero, zero_add, map_zero]

/-- The degree-two first column commutes with the next total differential. -/
theorem d2_comm (x : A2) : F.mapThree (E.d2 x) = D.d2 (F.mapTwo x) := by
  change (F.morphism.f3 (E.d2 x), 0, 0, 0) =
    (D.cofaces.d2 (F.morphism.f2 x),
      D.gradient2 (F.morphism.f2 x) + Algebra.pairMap D.cofaces.d1 0,
      -D.curl1 0 + D.cofaces.d0 0, 0)
  rw [F.morphism.d2_comm, F.gradient2, map_zero, zero_add, map_zero, map_zero,
    neg_zero, zero_add]

end Data

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.FirstAlgebra
