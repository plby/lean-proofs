import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalAlgebraBasic
import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalComplex

/-!
# The actual total complex of the triangular ring cofaces

All six square-zero identities and all three commuting squares follow
from the ring-coface identities. The resulting additive data are fed
into the shared literal total complex, so the algebra and the eventual
resolution comparison use exactly the same products and differentials.
-/

universe u

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.TotalAlgebra.Data

variable {R00 R10 R01 R20 R11 R02 R30 R21 R12 R03 : Type u}
  [CommRing R00] [CommRing R10] [CommRing R01] [CommRing R20] [CommRing R11]
  [CommRing R02] [CommRing R30] [CommRing R21] [CommRing R12] [CommRing R03]
  (D : Data R00 R10 R01 R20 R11 R02 R30 R21 R12 R03)

/-- The actual commuting additive complex derived from the given ring cofaces. -/
def complexData : TotalComplex.Data R00 R10 R01 R20 R11 R02 R30 R21 R12 R03 where
  v00 := D.dv00
  h00 := D.dh00
  v10 := D.dv10
  h10 := D.dh10
  v01 := D.dv01
  h01 := D.dh01
  v20 := D.dv20
  h20 := D.dh20
  v11 := D.dv11
  h11 := D.dh11
  v02 := D.dv02
  h02 := D.dh02
  vertical00 := by
    ext x
    exact D.vertical.d1_d0 x
  vertical10 := by
    ext x
    exact D.vertical.d2_d1 x
  vertical01 := by
    ext x
    exact alternating1_alternating0 D.cofaceV01 x
  horizontal00 := by
    ext x
    exact D.horizontal.d1_d0 x
  horizontal01 := by
    ext x
    exact D.horizontal.d2_d1 x
  horizontal10 := by
    ext x
    exact alternating1_alternating0 D.cofaceH10 x
  mixed00 := by
    ext x
    change D.dv01 (D.dh00 x) = D.dh10 (D.dv00 x)
    simp only [dv01, dh00, dh10, dv00, alternating0_apply, map_sub, D.mixed00_apply]
    abel
  mixed10 := by
    ext x
    change D.dv11 (D.dh10 x) = D.dh20 (D.dv10 x)
    simp only [dv11, dh10, dh20, dv10, alternating0_apply, alternating1_apply,
      map_add, map_sub, D.mixed10_apply]
    abel
  mixed01 := by
    ext x
    change D.dv02 (D.dh01 x) = D.dh11 (D.dv01 x)
    simp only [dv02, dh01, dh11, dv01, alternating0_apply, alternating1_apply,
      map_add, map_sub, D.mixed01_apply]
    abel

abbrev Zero := D.complexData.Zero
abbrev One := D.complexData.One
abbrev Two := D.complexData.Two
abbrev Three := D.complexData.Three

abbrev d0 : D.Zero →+ D.One := D.complexData.d0
abbrev d1 : D.One →+ D.Two := D.complexData.d1
abbrev d2 : D.Two →+ D.Three := D.complexData.d2

@[simp] theorem d0_apply (x : R00) : D.d0 x = (D.dv00 x, D.dh00 x) := rfl

@[simp] theorem d1_apply (a : D.One) :
    D.d1 a = (D.dv10 a.1, -D.dh10 a.1 + D.dv01 a.2, D.dh01 a.2) := rfl

@[simp] theorem d2_apply (c : D.Two) :
    D.d2 c = (D.dv20 c.1, D.dh20 c.1 + D.dv11 c.2.1,
      -D.dh11 c.2.1 + D.dv02 c.2.2, D.dh02 c.2.2) := rfl

@[simp] theorem d1_d0 (x : R00) : D.d1 (D.d0 x) = 0 := D.complexData.d1_d0 x
@[simp] theorem d2_d1 (a : D.One) : D.d2 (D.d1 a) = 0 := D.complexData.d2_d1 a

theorem d1_comp_d0 : D.d1.comp D.d0 = 0 := D.complexData.d1_comp_d0
theorem d2_comp_d1 : D.d2.comp D.d1 = 0 := D.complexData.d2_comp_d1

end Wikipedia.HopfProblem.SheafSingularCupComparison.TotalAlgebra.Data
