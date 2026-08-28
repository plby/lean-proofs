import Wikipedia.HopfProblem.CuspBoundaryGammaZeroMappingTorus
import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusCuspCoordinates

/-!
# Actual fibre negation on the native cusp boundary

The original integral cusp monodromy is linear and therefore commutes
with negation on the actual real period torus. The existing mapping-torus
construction descends this map through the original deck quotient. Its
base coordinate is unchanged and the resulting map is an involution.
No action on homology or extension to a filling is assumed here.
-/

noncomputable section

namespace Wikipedia.HopfProblem.CuspNegation

open SpecialPeriods.CuspFamily ThreefoldOverlapMappingTorus.Cusp

/-- Literal negation on the original real period torus. -/
def fibreNeg : C(RealTorus₄, RealTorus₄) := ⟨Neg.neg, continuous_neg⟩

@[simp] theorem fibreNeg_apply (x : RealTorus₄) : fibreNeg x = -x := rfl

/-- This is a consequence of the actual integral linear map inducing
the original cusp monodromy, not an assumed equivariance. -/
theorem monodromy_map_neg (x : RealTorus₄) : monodromy (-x) = -monodromy x := by
  obtain ⟨v, rfl⟩ := standardLattice.mkQ_surjective x
  change cuspTorusHomeomorph 1 (-standardLattice.mkQ v) =
    -cuspTorusHomeomorph 1 (standardLattice.mkQ v)
  rw [← map_neg, cuspTorusHomeomorph_mkQ, map_neg, map_neg, cuspTorusHomeomorph_mkQ]

theorem fibreNeg_monodromy (x : RealTorus₄) :
    fibreNeg (monodromy x) = monodromy (fibreNeg x) :=
  (monodromy_map_neg x).symm

/-- The actual boundary map `[t,x] ↦ [t,-x]` in the original native
mapping torus of the original cusp monodromy. -/
def boundaryNeg : C(Boundary, Boundary) :=
  CuspBoundaryGammaZero.mappingTorusMap monodromy monodromy fibreNeg fibreNeg_monodromy

@[simp] theorem boundaryNeg_mk (t : ℝ) (x : RealTorus₄) :
    boundaryNeg (MappingTorus.mk monodromy (t, x)) =
      MappingTorus.mk monodromy (t, -x) := rfl

/-- The map preserves the actual original base-circle projection. -/
@[simp] theorem boundaryNeg_base (x : Boundary) :
    MappingTorus.base monodromy (boundaryNeg x) = MappingTorus.base monodromy x :=
  CuspBoundaryGammaZero.mappingTorusMap_base monodromy monodromy fibreNeg fibreNeg_monodromy x

theorem boundaryNeg_involutive : Function.Involutive boundaryNeg := by
  intro x
  obtain ⟨⟨t, y⟩, rfl⟩ := MappingTorus.mk_surjective monodromy x
  rw [boundaryNeg_mk, boundaryNeg_mk, neg_neg]

/-- The same actual map, with its actual inverse and original topology. -/
def boundaryNegHomeomorph : Boundary ≃ₜ Boundary where
  toFun := boundaryNeg
  invFun := boundaryNeg
  left_inv := boundaryNeg_involutive
  right_inv := boundaryNeg_involutive
  continuous_toFun := boundaryNeg.continuous
  continuous_invFun := boundaryNeg.continuous

@[simp] theorem boundaryNegHomeomorph_apply (x : Boundary) :
    boundaryNegHomeomorph x = boundaryNeg x := rfl

/-- The literal zero section on the original boundary cylinder is fixed. -/
@[simp] theorem boundaryNeg_zero_section (t : ℝ) :
    boundaryNeg (MappingTorus.mk monodromy (t, 0)) = MappingTorus.mk monodromy (t, 0) := by
  rw [boundaryNeg_mk, neg_zero]

end Wikipedia.HopfProblem.CuspNegation
