import Wikipedia.HopfProblem.RiemannMapping
import Wikipedia.HopfProblem.SpecialPeriodsTriangleInterior

/-!
# Riemann uniformization of the actual half-Ford triangle interior

This is an application of the proved domain theorem to the explicitly
constructed nonempty simply connected proper open half-Ford triangle.
It does not assert a boundary extension, Schwarz reflection, or an
identification of the full triangle-group quotient with a projective line.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.RiemannMapping

open SpecialPeriods.Triangle

/-- The actual open half-Ford triangle, with inherited complex charts. -/
def triangleDomain : TopologicalSpace.Opens ℂ :=
  ⟨triangleInterior, triangleInterior_isOpen⟩

/-- The explicitly checked interior normalizing point `-1 + 2i`. -/
def trianglePoint : triangleDomain := ⟨triangleBasepoint, triangleBasepoint_mem⟩

/-- An actual biholomorphism from the source's open half-Ford triangle
to the actual unit disc, with every domain hypothesis discharged. -/
def triangleBiholomorph :
    Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      triangleDomain unitDisc ω :=
  biholomorphUnitDisc triangleDomain triangleInterior_isSimplyConnected
    triangleInterior_ne_univ trianglePoint

@[simp] theorem triangleBiholomorph_basepoint : triangleBiholomorph trianglePoint = discZero :=
  biholomorphUnitDisc_basepoint triangleDomain triangleInterior_isSimplyConnected
    triangleInterior_ne_univ trianglePoint

theorem triangleBiholomorph_holomorphic :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω triangleBiholomorph :=
  triangleBiholomorph.contMDiff_toFun

theorem triangleBiholomorph_symm_holomorphic :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω triangleBiholomorph.symm :=
  triangleBiholomorph.contMDiff_invFun

end Wikipedia.HopfProblem.RiemannMapping
