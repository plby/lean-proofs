import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupAlgebraHomology

/-!
# The actual last-row map into the Godement–Dolbeault total algebra

A ring map with vertically constant image intertwines the two actual
derivatives. These literal conditions imply the row and total
differential identities; no cohomology comparison is assumed.
-/

universe u

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.LastAlgebra

variable {R0 R1 R2 R3 : Type u}
  [CommRing R0] [CommRing R1] [CommRing R2] [CommRing R3]

/-- Actual row derivatives and their compatible vertically constant ring map. -/
structure Data (A : Type u) [CommRing A] (D : Algebra.Data R0 R1 R2 R3) where
  unit : A →+* R0
  baseDeriv : Fin 2 → A →+ A
  commute : ∀ x, baseDeriv 0 (baseDeriv 1 x) = baseDeriv 1 (baseDeriv 0 x)
  unit_vertical : ∀ x, D.cofaces.d0 (unit x) = 0
  unit_derivative : ∀ i x, D.deriv0 i (unit x) = unit (baseDeriv i x)

namespace Data

variable {A : Type u} [CommRing A] {D : Algebra.Data R0 R1 R2 R3} (F : Data A D)

/-- The original two-component row derivative. -/
abbrev rowD0 : A →+ A × A := Algebra.gradient (F.baseDeriv 0) (F.baseDeriv 1)

/-- The original alternating top row derivative. -/
abbrev rowD1 : A × A →+ A := Algebra.curl (F.baseDeriv 0) (F.baseDeriv 1)

/-- The row ends in the actual zero additive group. -/
def rowD2 (_F : Data A D) : A →+ PUnit.{u + 1} := 0

@[simp] theorem rowD0_apply (x : A) : F.rowD0 x = (F.baseDeriv 0 x, F.baseDeriv 1 x) := rfl

@[simp] theorem rowD1_apply (x : A × A) :
    F.rowD1 x = F.baseDeriv 0 x.2 - F.baseDeriv 1 x.1 := rfl

@[simp] theorem rowD2_apply (x : A) : F.rowD2 x = 0 := rfl

@[simp] theorem rowD1_rowD0 (x : A) : F.rowD1 (F.rowD0 x) = 0 := by
  simp only [rowD1_apply, rowD0_apply, F.commute, sub_self]

theorem rowD1_comp_rowD0 : F.rowD1.comp F.rowD0 = 0 :=
  AddMonoidHom.ext F.rowD1_rowD0

@[simp] theorem rowD2_rowD1 (x : A × A) : F.rowD2 (F.rowD1 x) = 0 := rfl

theorem rowD2_comp_rowD1 : F.rowD2.comp F.rowD1 = 0 :=
  AddMonoidHom.ext F.rowD2_rowD1

abbrev mapZero : A →+ D.Zero := F.unit.toAddMonoidHom

/-- A row one-form has zero vertical component in the actual total complex. -/
def mapOne : A × A →+ D.One :=
  (0 : A × A →+ R1).prod (Algebra.pairMap F.unit.toAddMonoidHom)

/-- A row top-form occupies the literal last total component. -/
def mapTwo : A →+ D.Two :=
  (0 : A →+ R2).prod ((0 : A →+ R1 × R1).prod F.unit.toAddMonoidHom)

/-- The final zero row term maps to the zero total cochain. -/
def mapThree (_F : Data A D) : PUnit.{u + 1} →+ D.Three := 0

@[simp] theorem mapZero_apply (x : A) : F.mapZero x = F.unit x := rfl

@[simp] theorem mapOne_apply (x : A × A) :
    F.mapOne x = (0, (F.unit x.1, F.unit x.2)) := rfl

@[simp] theorem mapTwo_apply (x : A) : F.mapTwo x = (0, 0, F.unit x) := rfl

@[simp] theorem mapThree_apply (x : PUnit.{u + 1}) : F.mapThree x = 0 := rfl

/-- The initial literal row map commutes with the total differential. -/
theorem d0_comm (x : A) : F.mapOne (F.rowD0 x) = D.d0 (F.mapZero x) := by
  simp only [mapOne_apply, rowD0_apply, mapZero_apply, Algebra.Data.d0_apply,
    F.unit_vertical, F.unit_derivative]

/-- The alternating row derivative has the original signed total image. -/
theorem d1_comm (x : A × A) : F.mapTwo (F.rowD1 x) = D.d1 (F.mapOne x) := by
  change (0, 0, F.unit (F.baseDeriv 0 x.2 - F.baseDeriv 1 x.1)) =
    (D.cofaces.d1 0,
      (-D.deriv1 0 0 + D.cofaces.d0 (F.unit x.1),
        -D.deriv1 1 0 + D.cofaces.d0 (F.unit x.2)),
      D.deriv0 0 (F.unit x.2) - D.deriv0 1 (F.unit x.1))
  simp only [map_zero, F.unit_vertical, F.unit_derivative, neg_zero, zero_add, map_sub]
  rfl

/-- Vertically constant row top-forms are actual total cocycles. -/
theorem d2_comm (x : A) : F.mapThree (F.rowD2 x) = D.d2 (F.mapTwo x) := by
  change (0 : D.Three) =
    (D.cofaces.d2 0,
      (D.deriv2 0 0 + D.cofaces.d1 0, D.deriv2 1 0 + D.cofaces.d1 0),
      -(D.deriv1 0 0 - D.deriv1 1 0) + D.cofaces.d0 (F.unit x), 0)
  simp only [map_zero, F.unit_vertical, zero_add, sub_self, neg_zero]
  rfl

end Data

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.LastAlgebra
