import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# The original signed triangular total complex in an additive category

Every term is a genuine finite categorical biproduct of the supplied
objects. The twelve maps are the actual horizontal and vertical maps;
their square-zero and commuting identities are retained literally.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.TotalCategory

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The original triangular part of a commuting double complex. -/
structure Data (R00 R10 R01 R20 R11 R02 R30 R21 R12 R03 : C) where
  v00 : R00 ⟶ R10
  h00 : R00 ⟶ R01
  v10 : R10 ⟶ R20
  h10 : R10 ⟶ R11
  v01 : R01 ⟶ R11
  h01 : R01 ⟶ R02
  v20 : R20 ⟶ R30
  h20 : R20 ⟶ R21
  v11 : R11 ⟶ R21
  h11 : R11 ⟶ R12
  v02 : R02 ⟶ R12
  h02 : R02 ⟶ R03
  vertical00 : v00 ≫ v10 = 0
  vertical10 : v10 ≫ v20 = 0
  vertical01 : v01 ≫ v11 = 0
  horizontal00 : h00 ≫ h01 = 0
  horizontal01 : h01 ≫ h02 = 0
  horizontal10 : h10 ≫ h11 = 0
  mixed00 : h00 ≫ v01 = v00 ≫ h10
  mixed10 : h10 ≫ v11 = v10 ≫ h20
  mixed01 : h01 ≫ v02 = v01 ≫ h11

namespace Data

variable {R00 R10 R01 R20 R11 R02 R30 R21 R12 R03 : C}
  (D : Data R00 R10 R01 R20 R11 R02 R30 R21 R12 R03)
  [HasBinaryBiproducts C]

abbrev zeroTerm (_D : Data R00 R10 R01 R20 R11 R02 R30 R21 R12 R03) : C := R00
abbrev oneTerm (_D : Data R00 R10 R01 R20 R11 R02 R30 R21 R12 R03) : C := R10 ⊞ R01
abbrev twoTerm (_D : Data R00 R10 R01 R20 R11 R02 R30 R21 R12 R03) : C :=
  R20 ⊞ (R11 ⊞ R02)
abbrev threeTerm (_D : Data R00 R10 R01 R20 R11 R02 R30 R21 R12 R03) : C :=
  R30 ⊞ (R21 ⊞ (R12 ⊞ R03))

/-- The original degree-zero total differential. -/
def d0 : R00 ⟶ D.oneTerm := biprod.lift D.v00 D.h00

/-- The original degree-one total differential, with its middle sign. -/
def d1 : D.oneTerm ⟶ D.twoTerm :=
  biprod.lift (biprod.fst ≫ D.v10)
    (biprod.lift (-(biprod.fst ≫ D.h10) + biprod.snd ≫ D.v01)
      (biprod.snd ≫ D.h01))

/-- The original degree-two total differential, with its mixed signs. -/
def d2 : D.twoTerm ⟶ D.threeTerm :=
  biprod.lift (biprod.fst ≫ D.v20)
    (biprod.lift (biprod.fst ≫ D.h20 + biprod.snd ≫ biprod.fst ≫ D.v11)
      (biprod.lift (-(biprod.snd ≫ biprod.fst ≫ D.h11) +
        biprod.snd ≫ biprod.snd ≫ D.v02)
        (biprod.snd ≫ biprod.snd ≫ D.h02)))

@[reassoc (attr := simp)] theorem d0_fst : D.d0 ≫ biprod.fst = D.v00 := by
  simp [d0]

@[reassoc (attr := simp)] theorem d0_snd : D.d0 ≫ biprod.snd = D.h00 := by
  simp [d0]

@[reassoc (attr := simp)] theorem d1_fst :
    D.d1 ≫ biprod.fst = biprod.fst ≫ D.v10 := by
  simp [d1]

@[reassoc (attr := simp)] theorem d1_snd_fst :
    D.d1 ≫ biprod.snd ≫ biprod.fst =
      -(biprod.fst ≫ D.h10) + biprod.snd ≫ D.v01 := by
  simp [d1]

@[reassoc (attr := simp)] theorem d1_snd_snd :
    D.d1 ≫ biprod.snd ≫ biprod.snd = biprod.snd ≫ D.h01 := by
  simp [d1]

@[reassoc (attr := simp)] theorem d2_fst :
    D.d2 ≫ biprod.fst = biprod.fst ≫ D.v20 := by
  simp [d2]

@[reassoc (attr := simp)] theorem d2_snd_fst :
    D.d2 ≫ biprod.snd ≫ biprod.fst =
      biprod.fst ≫ D.h20 + biprod.snd ≫ biprod.fst ≫ D.v11 := by
  simp [d2]

@[reassoc (attr := simp)] theorem d2_snd_snd_fst :
    D.d2 ≫ biprod.snd ≫ biprod.snd ≫ biprod.fst =
      -(biprod.snd ≫ biprod.fst ≫ D.h11) +
        biprod.snd ≫ biprod.snd ≫ D.v02 := by
  simp [d2]

@[reassoc (attr := simp)] theorem d2_snd_snd_snd :
    D.d2 ≫ biprod.snd ≫ biprod.snd ≫ biprod.snd =
      biprod.snd ≫ biprod.snd ≫ D.h02 := by
  simp [d2]

end Data

end Wikipedia.HopfProblem.SheafSingularCupComparison.TotalCategory
