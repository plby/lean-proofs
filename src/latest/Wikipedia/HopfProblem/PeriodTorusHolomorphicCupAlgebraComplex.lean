import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupAlgebraBasic

/-!
# The actual signed Godement--Dolbeault total differential

The vertical maps are the literal alternating coface maps and their
pairwise versions. The horizontal maps are the two actual derivatives
and their alternating top derivative. The shared total-complex
construction supplies the signs and both square-zero identities.
-/

universe u

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Algebra.Data

open SheafSingularCupComparison

variable {R0 R1 R2 R3 : Type u}
  [CommRing R0] [CommRing R1] [CommRing R2] [CommRing R3]
  (D : Data R0 R1 R2 R3)

/-- The actual triangular additive diagram, with no assumed total-complex identities. -/
def complexData : TotalComplex.Data
    R0 R1 (R0 × R0) R2 (R1 × R1) R0 R3 (R2 × R2) R1 PUnit where
  v00 := D.cofaces.d0
  h00 := D.gradient0
  v10 := D.cofaces.d1
  h10 := D.gradient1
  v01 := pairMap D.cofaces.d0
  h01 := D.curl0
  v20 := D.cofaces.d2
  h20 := D.gradient2
  v11 := pairMap D.cofaces.d1
  h11 := D.curl1
  v02 := D.cofaces.d0
  h02 := 0
  vertical00 := D.cofaces.d1_comp_d0
  vertical10 := D.cofaces.d2_comp_d1
  vertical01 := by
    apply AddMonoidHom.ext
    intro x
    exact Prod.ext (D.cofaces.d1_d0 x.1) (D.cofaces.d1_d0 x.2)
  horizontal00 := by
    apply AddMonoidHom.ext
    intro x
    exact D.curl0_gradient0 x
  horizontal01 := by
    apply AddMonoidHom.ext
    intro x
    exact Subsingleton.elim _ _
  horizontal10 := by
    apply AddMonoidHom.ext
    intro x
    exact D.curl1_gradient1 x
  mixed00 := by
    apply AddMonoidHom.ext
    intro x
    simp only [AddMonoidHom.comp_apply, pairMap_apply, gradient_apply, D.deriv1_d0]
  mixed10 := by
    apply AddMonoidHom.ext
    intro x
    simp only [AddMonoidHom.comp_apply, pairMap_apply, gradient_apply, D.deriv2_d1]
  mixed01 := by
    apply AddMonoidHom.ext
    intro x
    simp only [AddMonoidHom.comp_apply, pairMap_apply, curl_apply, map_sub, D.deriv1_d0]

abbrev Zero := D.complexData.Zero
abbrev One := D.complexData.One
abbrev Two := D.complexData.Two
abbrev Three := D.complexData.Three

abbrev d0 : D.Zero →+ D.One := D.complexData.d0
abbrev d1 : D.One →+ D.Two := D.complexData.d1
abbrev d2 : D.Two →+ D.Three := D.complexData.d2

@[simp] theorem d0_apply (x : R0) :
    D.d0 x = (D.cofaces.d0 x, (D.deriv0 0 x, D.deriv0 1 x)) := rfl

@[simp] theorem d1_apply (x : D.One) :
    D.d1 x = (D.cofaces.d1 x.1,
      (-D.deriv1 0 x.1 + D.cofaces.d0 x.2.1,
        -D.deriv1 1 x.1 + D.cofaces.d0 x.2.2),
      D.deriv0 0 x.2.2 - D.deriv0 1 x.2.1) := rfl

@[simp] theorem d2_apply (x : D.Two) :
    D.d2 x = (D.cofaces.d2 x.1,
      (D.deriv2 0 x.1 + D.cofaces.d1 x.2.1.1,
        D.deriv2 1 x.1 + D.cofaces.d1 x.2.1.2),
      -(D.deriv1 0 x.2.1.2 - D.deriv1 1 x.2.1.1) + D.cofaces.d0 x.2.2, 0) := rfl

@[simp] theorem d1_d0 (x : R0) : D.d1 (D.d0 x) = 0 := D.complexData.d1_d0 x
@[simp] theorem d2_d1 (x : D.One) : D.d2 (D.d1 x) = 0 := D.complexData.d2_d1 x

theorem d1_comp_d0 : D.d1.comp D.d0 = 0 := D.complexData.d1_comp_d0
theorem d2_comp_d1 : D.d2.comp D.d1 = 0 := D.complexData.d2_comp_d1

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Algebra.Data
