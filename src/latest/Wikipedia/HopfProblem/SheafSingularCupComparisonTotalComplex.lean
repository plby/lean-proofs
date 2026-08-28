import Mathlib.Algebra.Group.Hom.Instances
import Mathlib.Algebra.Exact.Basic

/-!
# The actual low-degree total complex of a commuting double complex

The ten original groups and twelve original differentials determine the
four literal product groups. The total differential uses the sign
`(-1)^p` on the horizontal differential in bidegree `(p,q)`.
Only the original square-zero and commuting-square identities are used.
-/

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.TotalComplex

universe u

variable (R00 R10 R01 R20 R11 R02 R30 R21 R12 R03 : Type u)
  [AddCommGroup R00] [AddCommGroup R10] [AddCommGroup R01]
  [AddCommGroup R20] [AddCommGroup R11] [AddCommGroup R02]
  [AddCommGroup R30] [AddCommGroup R21] [AddCommGroup R12] [AddCommGroup R03]

/-- A triangular truncation of an actual commuting cochain double complex. -/
structure Data where
  v00 : R00 →+ R10
  h00 : R00 →+ R01
  v10 : R10 →+ R20
  h10 : R10 →+ R11
  v01 : R01 →+ R11
  h01 : R01 →+ R02
  v20 : R20 →+ R30
  h20 : R20 →+ R21
  v11 : R11 →+ R21
  h11 : R11 →+ R12
  v02 : R02 →+ R12
  h02 : R02 →+ R03
  vertical00 : v10.comp v00 = 0
  vertical10 : v20.comp v10 = 0
  vertical01 : v11.comp v01 = 0
  horizontal00 : h01.comp h00 = 0
  horizontal01 : h02.comp h01 = 0
  horizontal10 : h11.comp h10 = 0
  mixed00 : v01.comp h00 = h10.comp v00
  mixed10 : v11.comp h10 = h20.comp v10
  mixed01 : v02.comp h01 = h11.comp v01

namespace Data

variable {R00 R10 R01 R20 R11 R02 R30 R21 R12 R03}
  (D : Data R00 R10 R01 R20 R11 R02 R30 R21 R12 R03)

abbrev Zero (_D : Data R00 R10 R01 R20 R11 R02 R30 R21 R12 R03) := R00
abbrev One (_D : Data R00 R10 R01 R20 R11 R02 R30 R21 R12 R03) := R10 × R01
abbrev Two (_D : Data R00 R10 R01 R20 R11 R02 R30 R21 R12 R03) := R20 × R11 × R02
abbrev Three (_D : Data R00 R10 R01 R20 R11 R02 R30 R21 R12 R03) :=
  R30 × R21 × R12 × R03

/-- The actual total differential out of degree zero. -/
def d0 : D.Zero →+ D.One := D.v00.prod D.h00

/-- The actual signed total differential out of degree one. -/
def d1 : D.One →+ D.Two :=
  (D.v10.comp (AddMonoidHom.fst R10 R01)).prod
    (((-(D.h10.comp (AddMonoidHom.fst R10 R01))) +
      D.v01.comp (AddMonoidHom.snd R10 R01)).prod
        (D.h01.comp (AddMonoidHom.snd R10 R01)))

/-- The actual signed total differential out of degree two. -/
def d2 : D.Two →+ D.Three :=
  let p0 := AddMonoidHom.fst R20 (R11 × R02)
  let p1 := (AddMonoidHom.fst R11 R02).comp (AddMonoidHom.snd R20 (R11 × R02))
  let p2 := (AddMonoidHom.snd R11 R02).comp (AddMonoidHom.snd R20 (R11 × R02))
  (D.v20.comp p0).prod
    ((D.h20.comp p0 + D.v11.comp p1).prod
      ((-(D.h11.comp p1) + D.v02.comp p2).prod (D.h02.comp p2)))

@[simp] theorem d0_apply (x : R00) : D.d0 x = (D.v00 x, D.h00 x) := rfl
@[simp] theorem d1_apply (x : R10 × R01) :
    D.d1 x = (D.v10 x.1, -D.h10 x.1 + D.v01 x.2, D.h01 x.2) := rfl
@[simp] theorem d2_apply (x : R20 × R11 × R02) :
    D.d2 x = (D.v20 x.1, D.h20 x.1 + D.v11 x.2.1,
      -D.h11 x.2.1 + D.v02 x.2.2, D.h02 x.2.2) := rfl

@[simp] theorem v10_v00 (x : R00) : D.v10 (D.v00 x) = 0 :=
  DFunLike.congr_fun D.vertical00 x
@[simp] theorem v20_v10 (x : R10) : D.v20 (D.v10 x) = 0 :=
  DFunLike.congr_fun D.vertical10 x
@[simp] theorem v11_v01 (x : R01) : D.v11 (D.v01 x) = 0 :=
  DFunLike.congr_fun D.vertical01 x
@[simp] theorem h01_h00 (x : R00) : D.h01 (D.h00 x) = 0 :=
  DFunLike.congr_fun D.horizontal00 x
@[simp] theorem h02_h01 (x : R01) : D.h02 (D.h01 x) = 0 :=
  DFunLike.congr_fun D.horizontal01 x
@[simp] theorem h11_h10 (x : R10) : D.h11 (D.h10 x) = 0 :=
  DFunLike.congr_fun D.horizontal10 x
@[simp] theorem v01_h00 (x : R00) : D.v01 (D.h00 x) = D.h10 (D.v00 x) :=
  DFunLike.congr_fun D.mixed00 x
@[simp] theorem v11_h10 (x : R10) : D.v11 (D.h10 x) = D.h20 (D.v10 x) :=
  DFunLike.congr_fun D.mixed10 x
@[simp] theorem v02_h01 (x : R01) : D.v02 (D.h01 x) = D.h11 (D.v01 x) :=
  DFunLike.congr_fun D.mixed01 x

/-- The first two signed total differentials compose to zero. -/
@[simp] theorem d1_d0 (x : R00) : D.d1 (D.d0 x) = 0 := by
  simp

/-- The next two signed total differentials likewise compose to zero. -/
@[simp] theorem d2_d1 (x : D.One) : D.d2 (D.d1 x) = 0 := by
  ext <;> simp

theorem d1_comp_d0 : D.d1.comp D.d0 = 0 := by
  apply AddMonoidHom.ext
  intro x
  exact D.d1_d0 x

theorem d2_comp_d1 : D.d2.comp D.d1 = 0 := by
  apply AddMonoidHom.ext
  intro x
  exact D.d2_d1 x

end Data

end Wikipedia.HopfProblem.SheafSingularCupComparison.TotalComplex
