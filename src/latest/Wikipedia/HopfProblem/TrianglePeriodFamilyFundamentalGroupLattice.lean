import Wikipedia.HopfProblem.TrianglePeriodFamilyFundamentalGroupMaps
import Wikipedia.HopfProblem.TrianglePeriodFamilyTransportTorus

/-!
# The actual triangle action on the flat-torus fundamental group

The integral dual representation acts by automorphisms of the marked
lattice. The covering-theoretic marking of the genuine flat-torus
fundamental group intertwines this action with the maps of based loops
induced by the actual triangle torus homeomorphisms.

The comparison uses the already proved straight period-loop
representatives of all fundamental-group elements, not an assumed
identification with homology.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods

/-- The actual dual integral representation, as automorphisms of the
source-column lattice written multiplicatively. -/
def triangleLatticeMulAutHom : TriangleGroup →* MulAut (Multiplicative Lattice) where
  toFun g := (Matrix.SpecialLinearGroup.toLin'
    (triangleDualRepresentation g)).toAddEquiv.toMultiplicative
  map_one' := by
    apply MulEquiv.ext
    intro n
    apply Multiplicative.toAdd.injective
    change Matrix.SpecialLinearGroup.toLin' (triangleDualRepresentation 1) n.toAdd =
      n.toAdd
    rw [map_one, map_one]
    rfl
  map_mul' g h := by
    apply MulEquiv.ext
    intro n
    apply Multiplicative.toAdd.injective
    change Matrix.SpecialLinearGroup.toLin' (triangleDualRepresentation (g * h)) n.toAdd =
      Matrix.SpecialLinearGroup.toLin' (triangleDualRepresentation g)
        (Matrix.SpecialLinearGroup.toLin' (triangleDualRepresentation h) n.toAdd)
    rw [map_mul, map_mul]
    rfl

/-- The automorphism acts by the constructed integral matrix, with the
same column convention as the actual torus action. -/
@[simp] theorem triangleLatticeMulAutHom_toAdd
    (g : TriangleGroup) (n : Multiplicative Lattice) :
    (triangleLatticeMulAutHom g n).toAdd =
      (triangleDualRepresentation g : LatticeMatrix) *ᵥ n.toAdd := rfl

@[simp] theorem triangleLatticeMulAutHom_ofAdd (g : TriangleGroup) (c : Lattice) :
    triangleLatticeMulAutHom g (Multiplicative.ofAdd c) =
      Multiplicative.ofAdd ((triangleDualRepresentation g : LatticeMatrix) *ᵥ c) := rfl

end Wikipedia.HopfProblem.SpecialPeriods

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.FlatTorus

open FirstHurewicz SpecialPeriods DiagonalQuotient

local instance : MulAction TriangleGroup RealTorus₄ := triangleTorusAction
local instance : ContinuousConstSMul TriangleGroup RealTorus₄ :=
  triangleTorusAction_continuous

/-- The actual based-loop map sends each straight period loop to the
straight period loop for the dual integral matrix. -/
theorem fibreActionFundamentalGroupHom_periodLoop (g : TriangleGroup) (c : Lattice) :
    fibreActionFundamentalGroupHom (0 : RealTorus₄) triangleTorusAction_zero g
        (loopQuotient (periodLoop c)) =
      loopQuotient (periodLoop ((triangleDualRepresentation g : LatticeMatrix) *ᵥ c)) := by
  rw [fibreActionFundamentalGroupHom, FundamentalGroup.mapOfEq_apply]
  change Path.Homotopic.Quotient.mk
    (((periodLoop c).map (triangleTorusHomeomorph g).continuous).cast
      (triangleTorusHomeomorph_zero g).symm (triangleTorusHomeomorph_zero g).symm) = _
  rw [periodLoop_map_triangle]
  rfl

/-- The genuine covering-theoretic fundamental-group marking intertwines
the actual triangle fibre action with the dual integral representation. -/
theorem fundamentalGroupEquiv_fibreAction (g : TriangleGroup)
    (γ : FundamentalGroup RealTorus₄ 0) :
    fundamentalGroupEquiv
        (fibreActionFundamentalGroupHom (0 : RealTorus₄) triangleTorusAction_zero g γ) =
      triangleLatticeMulAutHom g (fundamentalGroupEquiv γ) := by
  obtain ⟨c, rfl⟩ := fundamentalGroupEquiv.symm.surjective γ
  change fundamentalGroupEquiv
      (fibreActionFundamentalGroupHom (0 : RealTorus₄) triangleTorusAction_zero g
        (fundamentalGroupEquiv.symm (Multiplicative.ofAdd c.toAdd))) = _
  rw [fundamentalGroupEquiv_symm_apply, fibreActionFundamentalGroupHom_periodLoop,
    fundamentalGroupEquiv_periodLoop, MulEquiv.apply_symm_apply]
  rfl

end Wikipedia.HopfProblem.TrianglePeriodFamily.FlatTorus
