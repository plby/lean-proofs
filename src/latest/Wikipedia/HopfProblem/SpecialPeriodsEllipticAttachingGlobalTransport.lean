import Wikipedia.HopfProblem.ThreefoldFundamentalGroupMarkedInclusion
import Wikipedia.HopfProblem.TrianglePeriodFamilyFundamentalGroupBaseChange
import Wikipedia.HopfProblem.FundamentalGroupBasepointNaturality

/-!
# Transport of the original period column to the global marked basepoint

The loops below are the literal positive flat-torus period loops, mapped
into the actual regular family and then the glued threefold.  Moving the
basepoint along the zero section of any genuine upstairs path preserves
the same integral column exactly.
-/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.EllipticGeometry

open Elliptic TrianglePeriodFamily FundamentalGroup

local notation "Dsp" =>
  regularData specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂
local notation "bsp" => Meridians.normalizedRegularMeridianBasepoint

/-- The original positive period loop in the actual regular fibre. -/
def regularColumnLoop (b : TriangleRegularPoint) (w : Lattice) :
    Path ((Dsp).fundamentalGroupBasepoint b) ((Dsp).fundamentalGroupBasepoint b) :=
  (FlatTorus.periodLoop w).map
    ((Dsp).quotient_continuous.comp (continuous_const.prodMk continuous_id))

theorem regularColumnLoop_apply (b : TriangleRegularPoint) (w : Lattice) (t : I) :
    regularColumnLoop b w t =
      (Dsp).quotient (b, standardLattice.mkQ ((t : ℝ) • realCast w)) := by
  change (Dsp).quotient (b, FlatTorus.periodLoop w t) = _
  rw [FlatTorus.periodLoop_apply]

/-- Its class is the previously fixed source-column lattice homomorphism. -/
theorem regularColumnLoop_class (b : TriangleRegularPoint) (w : Lattice) :
    FundamentalGroup.fromPath ⟦regularColumnLoop b w⟧ =
      (Dsp).latticeFundamentalGroupHom b (Multiplicative.ofAdd w) :=
  ((Dsp).latticeFundamentalGroupHom_periodLoop b w).symm

/-- Include that same actual period loop into the glued threefold. -/
def globalColumnLoop (b : TriangleRegularPoint) (w : Lattice) :
    Path (regularFamilyInclusionMap ((Dsp).fundamentalGroupBasepoint b))
      (regularFamilyInclusionMap ((Dsp).fundamentalGroupBasepoint b)) :=
  (regularColumnLoop b w).map regularFamilyInclusionMap.continuous

theorem globalColumnLoop_apply (b : TriangleRegularPoint) (w : Lattice) (t : I) :
    globalColumnLoop b w t =
      regularFamilyInclusionMap
        ((Dsp).quotient (b, standardLattice.mkQ ((t : ℝ) • realCast w))) :=
  congrArg regularFamilyInclusionMap (regularColumnLoop_apply b w t)

theorem globalColumnLoop_class (b : TriangleRegularPoint) (w : Lattice) :
    FundamentalGroup.fromPath ⟦globalColumnLoop b w⟧ =
      FundamentalGroup.map regularFamilyInclusionMap ((Dsp).fundamentalGroupBasepoint b)
        ((Dsp).latticeFundamentalGroupHom b (Multiplicative.ofAdd w)) :=
  congrArg (FundamentalGroup.map regularFamilyInclusionMap ((Dsp).fundamentalGroupBasepoint b))
    (regularColumnLoop_class b w)

/-- The global tail comes from a genuine path in the original parameter space. -/
def upstairsPathGlobalTail {b : TriangleRegularPoint} (p : Path bsp b) :
    Path PiOne.basepoint (regularFamilyInclusionMap ((Dsp).fundamentalGroupBasepoint b)) :=
  ((Dsp).zeroSectionPath p).map regularFamilyInclusionMap.continuous

theorem upstairsPathGlobalTail_symm {b : TriangleRegularPoint} (p : Path bsp b) :
    (upstairsPathGlobalTail p).symm =
      ((Dsp).zeroSectionPath p.symm).map regularFamilyInclusionMap.continuous := by
  ext t
  rfl

/-- Transport to the fixed global basepoint changes neither the sign nor the column. -/
theorem transport_globalColumnLoop {b : TriangleRegularPoint} (p : Path bsp b)
    (w : Lattice) :
    fundamentalGroupMulEquivOfPath (upstairsPathGlobalTail p).symm
      (FundamentalGroup.fromPath ⟦globalColumnLoop b w⟧) =
        PiOne.latticeHom (Multiplicative.ofAdd w) := by
  rw [upstairsPathGlobalTail_symm, globalColumnLoop_class]
  exact (fundamentalGroup_basepoint_naturality_apply regularFamilyInclusionMap
    ((Dsp).zeroSectionPath p.symm)
    ((Dsp).latticeFundamentalGroupHom b (Multiplicative.ofAdd w))).trans
      (congrArg (FundamentalGroup.map regularFamilyInclusionMap
        ((Dsp).fundamentalGroupBasepoint bsp))
        ((Dsp).latticeFundamentalGroupHom_baseChange p.symm (Multiplicative.ofAdd w)))

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.EllipticGeometry
